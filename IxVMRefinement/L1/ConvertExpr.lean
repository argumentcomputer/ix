import IxVMRefinement.L1.Decode
import IxVMRefinement.Obs.Convert
import IxVMRefinement.Nat.Utf8
import IxVMRefinement.Subst.Basic
import IxC.Kernel.Ixon.Reader
import IxC.Kernel.Verify.PropWhen
import Ix.IxVM.Consistency.Statement

/-! # Expression, Universe, Literal, and Binder-Table Conversion (`Convert` part 1)

Observed-derivation (`ObsFn`) specifications for the expression-level conversion pipeline in
`IxVM/IxVM/Source/Convert.lean`:
* standalone UTF-8 validation (`utf8_cont_spec`, `utf8_decode_one_spec`, `utf8_validate_spec`);
* canonical natural literal checking and little-endian limb conversion
  (`assert_nat_blob_canonical_spec`, `bytes_to_limbs_spec`);
* universe level conversion (`RawKLevel`, `convert_univ_spec`, `convert_univ_idxs_spec`, and the
  `posOf` / `RepKLevel` bridge under `allParamsDefined`);
* binder search-tree construction and lookup (`RepBinderTree`, `binder_table_spec`,
  `binder_nodes_spec`, `params_level_spec`, `binder_level_spec`);
* manual observed-derivation inversion for `Convert::convert_annotated`;
* unconditional `RawConvExpr` + `HashedPairs` specifications for `convert_expr`,
  `convert_annotated`, `convert_block`, and `convert_root`, together with the `Reader.convExpr` /
  `Annotates` / `Tm` / `TmC` bridge (`RawConvExpr.toTm`, `RawConvExpr.toTmC`).
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

local notation "W" => IxVM.Refinement.Obs.W

/-! ## Standalone UTF-8 validation (`KernelNatPrim::utf8_*`) -/

/-- `KernelNatPrim::utf8_cont` checks `128 ≤ b < 192` and returns `b - 128` without allocation. -/
theorem utf8_cont_spec {bp r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    {b : UInt8} (hb : RepU8 h b bp)
    (ev : ObsFn W "KernelNatPrim::utf8_cont" [bp] h r h' cs) :
    128 ≤ b.toNat ∧ b.toNat < 192 ∧ r = .field ((b.toNat - 128 : Nat) : F) ∧ h' = h := by
  have hbv : bp = .field (b.toNat : F) := hb
  obtain ⟨m2, cs13, m36, cs47, x69, m71, cs80, ev15, ev49, ev82, he91, op76, _⟩ :=
    Obs.«KernelNatPrim::utf8_cont».obs ev
  obtain ⟨hv15, hm2⟩ := Core.Utf8Aux.u8_lt_lit 128 (by omega) (by rfl) hbv ev15
  subst m2
  obtain ⟨hv49, hm36⟩ := Core.Utf8Aux.u8_lt_lit 192 (by omega) (by rfl) hbv ev49
  subst m36
  obtain ⟨hx69, hm71⟩ := Lib.u8_to_field_spec ev82
  subst x69 m71 h'
  have l128 : ¬ b.toNat < 128 := Core.Utf8Aux.not_of_field_zero hv15
  have l192 : b.toNat < 192 := Core.Utf8Aux.of_field_one hv49
  refine ⟨by omega, l192, ?_, rfl⟩
  exact (Core.Utf8Aux.binop_sub_lit hbv op76).trans
    (Core.Utf8Aux.field_congr (Core.Utf8Aux.cast1 (by omega)))

/-- `KernelNatPrim::utf8_decode_one` decodes one UTF-8 scalar value from `b :: bs` without
allocating. -/
theorem utf8_decode_one_spec {bp rest r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    {b : UInt8} {bs : List UInt8}
    (hb : RepU8 h b bp) (hbs : Bytes.RepByteStream Core.byteListEnum h bs rest)
    (ev : ObsFn W "KernelNatPrim::utf8_decode_one" [bp, rest] h r h' cs) :
    h' = h ∧ ∃ (ch : Char) (bs' : List UInt8) (rem : SourceValue F),
      b :: bs = String.utf8EncodeChar ch ++ bs' ∧
      r = .tuple [.field (ch.toNat : F), rem] ∧
      Bytes.RepByteStream Core.byteListEnum h bs' rem := by
  have hbv : bp = .field (b.toNat : F) := hb
  have hb256 : b.toNat < 256 := b.toNat_lt_size
  rcases Obs.«KernelNatPrim::utf8_decode_one».obs ev with
    ⟨m2, cs13, v37, m41, cs49, ev15, he39, ev51, he67, _⟩ |
    ⟨v1, m2, cs13, m74, cs85, m108, cs119, x_b1, x_r1, v170, m171, x178, y179, x186, x194, m196,
      cs205, cs219, ev15, hne69, ev87, ev121, ld152, ev207, op201, op193, ev221, op185, he234,
      he249, _⟩ |
    ⟨v1, m2, cs13, m74, cs85, v107, m108, cs119, m257, cs268, x_b1, x_r1, x_b2, x_r2, v348, m349,
      x356, y357, x364, y365, x372, x380, m382, cs391, x402, m404, cs413, cs427, m439, cs450, m473,
      cs484, ev15, hne69, ev87, ev121, hne252, ev270, ld301, ld330, ev393, op387, op379, ev415,
      op409, op371, ev429, op363, ev452, ev486, he510, he525, _⟩ |
    ⟨v1, m2, cs13, m74, cs85, v107, m108, cs119, m257, cs268, x_b1, x_r1, x_b2, x_r2, v348, m349,
      x356, y357, x364, y365, x372, x380, m382, cs391, x402, m404, cs413, cs427, m439, cs450, m473,
      cs484, m533, cs544, ev15, hne69, ev87, ev121, hne252, ev270, ld301, ld330, ev393, op387,
      op379, ev415, op409, op371, ev429, op363, ev452, ev486, ev546, he570, he585, _⟩ |
    ⟨v1, m2, cs13, m74, cs85, v107, m108, cs119, v256, m257, cs268, x_b1, x_r1, x_b2, x_r2, x_b3,
      x_r3, v683, m684, x691, y692, x699, y700, x707, y708, x715, x723, m725, cs734, x745, m747,
      cs756, x767, m769, cs778, cs792, m804, cs815, m838, cs849, ev15, hne69, ev87, ev121, hne252,
      ev270, hne592, ld607, ld636, ld665, ev736, op730, op722, ev758, op752, op714, ev780, op774,
      op706, ev794, op698, ev817, ev851, he875, he890, _⟩
  · subst he39 he67
    obtain ⟨hv15, hm2⟩ := Core.Utf8Aux.u8_lt_lit 128 (by omega) (by rfl) hbv ev15
    subst m2
    obtain ⟨hv37, hm41⟩ := Lib.u8_to_field_spec ev51
    subst v37 m41
    obtain ⟨ch, hch, henc⟩ := Core.Utf8Aux.encode_one (Core.Utf8Aux.of_field_one hv15)
    refine ⟨rfl, ch, bs, rest, by simp [henc], ?_, hbs⟩
    rw [hbv]
    exact Core.Utf8Aux.tuple_field_congr (congrArg (Nat.cast : Nat → F) hch.symm)
  · subst he234 he249
    obtain ⟨hv1, hm2⟩ := Core.Utf8Aux.u8_lt_lit 128 (by omega) (by rfl) hbv ev15
    subst v1 m2
    obtain ⟨hv87, hm74⟩ := Core.Utf8Aux.u8_lt_lit 194 (by omega) (by rfl) hbv ev87
    subst m74
    obtain ⟨hv121, hm108⟩ := Core.Utf8Aux.u8_lt_lit 224 (by omega) (by rfl) hbv ev121
    subst m108
    have l194 : ¬ b.toNat < 194 := Core.Utf8Aux.not_of_field_zero hv87
    have l224 : b.toNat < 224 := Core.Utf8Aux.of_field_one hv121
    obtain ⟨b1, bs1, rfl, hb1, hbs1⟩ := Core.RepList.cons_of_load hbs ld152
    obtain ⟨hx194, hm196⟩ := Lib.u8_to_field_spec ev207
    subst x194 m196
    obtain ⟨c1lo, c1hi, hy179, hm171⟩ := utf8_cont_spec hb1 ev221
    subst m171
    have e170 : v170 = .field ((((b.toNat - 192) * 64 + (b1.toNat - 128) : Nat)) : F) :=
      (Core.Utf8Aux.binop_add
        (Core.Utf8Aux.binop_mul_lit (Core.Utf8Aux.binop_sub_lit hbv op201) op193) hy179 op185).trans
        (Core.Utf8Aux.field_congr (Core.Utf8Aux.cast2 (by omega)))
    subst v170
    obtain ⟨ch, hch, henc⟩ := Core.Utf8Aux.encode_two (by omega) l224 c1lo c1hi
    refine ⟨rfl, ch, bs1, x_r1, by simp [henc], ?_, hbs1⟩
    exact Core.Utf8Aux.tuple_field_congr (congrArg (Nat.cast : Nat → F) hch.symm)
  · subst he510 he525
    obtain ⟨hv1, hm2⟩ := Core.Utf8Aux.u8_lt_lit 128 (by omega) (by rfl) hbv ev15
    subst v1 m2
    obtain ⟨hv87, hm74⟩ := Core.Utf8Aux.u8_lt_lit 194 (by omega) (by rfl) hbv ev87
    subst m74
    obtain ⟨hv107, hm108⟩ := Core.Utf8Aux.u8_lt_lit 224 (by omega) (by rfl) hbv ev121
    subst v107 m108
    obtain ⟨hv270, hm257⟩ := Core.Utf8Aux.u8_lt_lit 240 (by omega) (by rfl) hbv ev270
    subst m257
    have l224 : ¬ b.toNat < 224 := Core.Utf8Aux.not_of_ne_one hne252
    have l240 : b.toNat < 240 := Core.Utf8Aux.of_field_one hv270
    obtain ⟨b1, bs1, rfl, hb1, hbs1⟩ := Core.RepList.cons_of_load hbs ld301
    obtain ⟨b2, bs2, rfl, hb2, hbs2⟩ := Core.RepList.cons_of_load hbs1 ld330
    obtain ⟨hx380, hm382⟩ := Lib.u8_to_field_spec ev393
    subst x380 m382
    obtain ⟨c1lo, c1hi, hx402, hm404⟩ := utf8_cont_spec hb1 ev415
    subst m404
    obtain ⟨c2lo, c2hi, hy357, hm349⟩ := utf8_cont_spec hb2 ev429
    subst m349
    have e348 : v348 = .field ((((b.toNat - 224) * 4096 + (b1.toNat - 128) * 64 +
        (b2.toNat - 128) : Nat)) : F) :=
      (Core.Utf8Aux.binop_add (Core.Utf8Aux.binop_add
        (Core.Utf8Aux.binop_mul_lit (Core.Utf8Aux.binop_sub_lit hbv op387) op379)
        (Core.Utf8Aux.binop_mul_lit hx402 op409) op371) hy357 op363).trans
        (Core.Utf8Aux.field_congr (Core.Utf8Aux.cast3 (by omega)))
    subst v348
    obtain ⟨hlo, hm439⟩ := Core.Utf8Aux.ltf_zero 2048 (by omega) (by omega) (by rfl) ev452
    subst m439
    obtain ⟨hhi, hm473⟩ := Core.Utf8Aux.ltf_one 55296 (by omega) (by omega) (by rfl) ev486
    subst m473
    obtain ⟨ch, hch, henc⟩ :=
      Core.Utf8Aux.encode_three (b0 := b) (by omega) l240 c1lo c1hi c2lo c2hi (by omega)
        (.inl (by omega))
    refine ⟨rfl, ch, bs2, x_r2, by simp [henc], ?_, hbs2⟩
    exact Core.Utf8Aux.tuple_field_congr (congrArg (Nat.cast : Nat → F) hch.symm)
  · subst he570 he585
    obtain ⟨hv1, hm2⟩ := Core.Utf8Aux.u8_lt_lit 128 (by omega) (by rfl) hbv ev15
    subst v1 m2
    obtain ⟨hv87, hm74⟩ := Core.Utf8Aux.u8_lt_lit 194 (by omega) (by rfl) hbv ev87
    subst m74
    obtain ⟨hv107, hm108⟩ := Core.Utf8Aux.u8_lt_lit 224 (by omega) (by rfl) hbv ev121
    subst v107 m108
    obtain ⟨hv270, hm257⟩ := Core.Utf8Aux.u8_lt_lit 240 (by omega) (by rfl) hbv ev270
    subst m257
    have l224 : ¬ b.toNat < 224 := Core.Utf8Aux.not_of_ne_one hne252
    have l240 : b.toNat < 240 := Core.Utf8Aux.of_field_one hv270
    obtain ⟨b1, bs1, rfl, hb1, hbs1⟩ := Core.RepList.cons_of_load hbs ld301
    obtain ⟨b2, bs2, rfl, hb2, hbs2⟩ := Core.RepList.cons_of_load hbs1 ld330
    obtain ⟨hx380, hm382⟩ := Lib.u8_to_field_spec ev393
    subst x380 m382
    obtain ⟨c1lo, c1hi, hx402, hm404⟩ := utf8_cont_spec hb1 ev415
    subst m404
    obtain ⟨c2lo, c2hi, hy357, hm349⟩ := utf8_cont_spec hb2 ev429
    subst m349
    have e348 : v348 = .field ((((b.toNat - 224) * 4096 + (b1.toNat - 128) * 64 +
        (b2.toNat - 128) : Nat)) : F) :=
      (Core.Utf8Aux.binop_add (Core.Utf8Aux.binop_add
        (Core.Utf8Aux.binop_mul_lit (Core.Utf8Aux.binop_sub_lit hbv op387) op379)
        (Core.Utf8Aux.binop_mul_lit hx402 op409) op371) hy357 op363).trans
        (Core.Utf8Aux.field_congr (Core.Utf8Aux.cast3 (by omega)))
    subst v348
    obtain ⟨hlo, hm439⟩ := Core.Utf8Aux.ltf_zero 2048 (by omega) (by omega) (by rfl) ev452
    subst m439
    obtain ⟨-, hm473⟩ := Core.Utf8Aux.ltf_zero 55296 (by omega) (by omega) (by rfl) ev486
    subst m473
    obtain ⟨hhi, hm533⟩ := Core.Utf8Aux.ltf_zero 57344 (by omega) (by omega) (by rfl) ev546
    subst m533
    obtain ⟨ch, hch, henc⟩ :=
      Core.Utf8Aux.encode_three (b0 := b) (by omega) l240 c1lo c1hi c2lo c2hi (by omega)
        (.inr (by omega))
    refine ⟨rfl, ch, bs2, x_r2, by simp [henc], ?_, hbs2⟩
    exact Core.Utf8Aux.tuple_field_congr (congrArg (Nat.cast : Nat → F) hch.symm)
  · subst he875 he890
    obtain ⟨hv1, hm2⟩ := Core.Utf8Aux.u8_lt_lit 128 (by omega) (by rfl) hbv ev15
    subst v1 m2
    obtain ⟨hv87, hm74⟩ := Core.Utf8Aux.u8_lt_lit 194 (by omega) (by rfl) hbv ev87
    subst m74
    obtain ⟨hv107, hm108⟩ := Core.Utf8Aux.u8_lt_lit 224 (by omega) (by rfl) hbv ev121
    subst v107 m108
    obtain ⟨hv256, hm257⟩ := Core.Utf8Aux.u8_lt_lit 240 (by omega) (by rfl) hbv ev270
    subst v256 m257
    have l240 : ¬ b.toNat < 240 := Core.Utf8Aux.not_of_ne_one hne592
    obtain ⟨b1, bs1, rfl, hb1, hbs1⟩ := Core.RepList.cons_of_load hbs ld607
    obtain ⟨b2, bs2, rfl, hb2, hbs2⟩ := Core.RepList.cons_of_load hbs1 ld636
    obtain ⟨b3, bs3, rfl, hb3, hbs3⟩ := Core.RepList.cons_of_load hbs2 ld665
    obtain ⟨hx723, hm725⟩ := Lib.u8_to_field_spec ev736
    subst x723 m725
    obtain ⟨c1lo, c1hi, hx745, hm747⟩ := utf8_cont_spec hb1 ev758
    subst m747
    obtain ⟨c2lo, c2hi, hx767, hm769⟩ := utf8_cont_spec hb2 ev780
    subst m769
    obtain ⟨c3lo, c3hi, hy692, hm684⟩ := utf8_cont_spec hb3 ev794
    subst m684
    have e683 : v683 = .field ((((b.toNat - 240) * 262144 + (b1.toNat - 128) * 4096 +
        (b2.toNat - 128) * 64 + (b3.toNat - 128) : Nat)) : F) :=
      (Core.Utf8Aux.binop_add (Core.Utf8Aux.binop_add (Core.Utf8Aux.binop_add
        (Core.Utf8Aux.binop_mul_lit (Core.Utf8Aux.binop_sub_lit hbv op730) op722)
        (Core.Utf8Aux.binop_mul_lit hx745 op752) op714)
        (Core.Utf8Aux.binop_mul_lit hx767 op774) op706) hy692 op698).trans
        (Core.Utf8Aux.field_congr (Core.Utf8Aux.cast4 (by omega)))
    subst v683
    obtain ⟨hlo, hm804⟩ := Core.Utf8Aux.ltf_zero 65536 (by omega) (by omega) (by rfl) ev817
    subst m804
    obtain ⟨hhi, hm838⟩ := Core.Utf8Aux.ltf_one 1114112 (by omega) (by omega) (by rfl) ev851
    subst m838
    obtain ⟨ch, hch, henc⟩ :=
      Core.Utf8Aux.encode_four (b0 := b) (by omega) c1lo c1hi c2lo c2hi c3lo c3hi
        (by omega) (by omega)
    refine ⟨rfl, ch, bs3, x_r3, by simp [henc], ?_, hbs3⟩
    exact Core.Utf8Aux.tuple_field_congr (congrArg (Nat.cast : Nat → F) hch.symm)

private theorem utf8_validate_go (n : Nat) :
    ∀ {bs : List UInt8} {bp r : SourceValue F} {h h' : Heap F} {cs : List (Call F)},
      bs.length ≤ n →
      Bytes.RepByteStream Core.byteListEnum h bs bp →
      ObsFn W "KernelNatPrim::utf8_validate" [bp] h r h' cs →
      h' = h ∧ ∃ s : String, Core.StrBytes s bs := by
  induction n with
  | zero =>
    intro bs bp r h h' cs hlen hbs ev
    have hbs_nil : bs = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst hbs_nil
    rcases Obs.«KernelNatPrim::utf8_validate».obs ev with
      ⟨_, _, he23, _⟩ | ⟨x_b0, x_rest, _, _, _, _, _, ld12, _, _, _⟩
    · exact ⟨he23, Core.Utf8Aux.exists_strBytes_iff.mpr ⟨[], by simp⟩⟩
    · exact absurd rfl (repList_ne_nil_of_load_cons hbs ld12)
  | succ n ih =>
    intro bs bp r h h' cs hlen hbs ev
    rcases Obs.«KernelNatPrim::utf8_validate».obs ev with
      ⟨ld12, _, he23, _⟩ |
      ⟨x_b0, x_rest, m43, cs54, w79, x_remaining, cs93, ld12, ev56, ev95, _⟩
    · obtain rfl := repList_nil_of_load hbs ld12
      exact ⟨he23, Core.Utf8Aux.exists_strBytes_iff.mpr ⟨[], by simp⟩⟩
    · obtain ⟨b0, bs0, rfl, hb0, hbs0⟩ := Core.RepList.cons_of_load hbs ld12
      obtain ⟨hm43, ch, bs', rem, hsplit, hr, hrem⟩ := utf8_decode_one_spec hb0 hbs0 ev56
      subst m43
      obtain ⟨-, hrm⟩ := Core.Utf8Aux.tuple2_inj hr
      subst x_remaining
      have henc_pos : 0 < (String.utf8EncodeChar ch).length := by
        rw [Core.Utf8Aux.utf8EncodeChar_eq]
        split_ifs <;> simp
      have hsplit_len := congrArg List.length hsplit
      simp only [List.length_cons, List.length_append] at hsplit_len
      simp only [List.length_cons] at hlen
      obtain ⟨hh', s, hs⟩ := ih (by omega) hrem ev95
      obtain ⟨chars, hchars⟩ := Core.Utf8Aux.exists_strBytes_iff.mp ⟨s, hs⟩
      exact ⟨hh', Core.Utf8Aux.exists_strBytes_iff.mpr
        ⟨ch :: chars, by rw [List.flatMap_cons, hchars, hsplit]⟩⟩

/-- `KernelNatPrim::utf8_validate` witnesses that `bs` is valid UTF-8 (`Core.StrBytes s bs`)
without modifying the heap. -/
theorem utf8_validate_spec {bs : List UInt8} {bp r : SourceValue F} {h h' : Heap F}
    {cs : List (Call F)}
    (hbs : Bytes.RepByteStream Core.byteListEnum h bs bp)
    (ev : ObsFn W "KernelNatPrim::utf8_validate" [bp] h r h' cs) :
    h' = h ∧ ∃ s : String, Core.StrBytes s bs :=
  utf8_validate_go bs.length (Nat.le_refl _) hbs ev

/-! ## Canonical natural literal blobs and little-endian limb conversion -/

/-- Little-endian natural number value of a byte list. -/
def bytesVal : List UInt8 → Nat
  | [] => 0
  | b :: bs => b.toNat + 256 * bytesVal bs

theorem bytesVal_eq_natural (bs : List UInt8) :
    bytesVal bs = Ix.Kernel.Reader.natural ⟨bs.toArray⟩ := by
  unfold Ix.Kernel.Reader.natural
  show bytesVal bs = bs.toArray.foldr (fun byte rest => byte.toNat + 256 * rest) 0
  rw [List.foldr_toArray]
  induction bs with
  | nil => rfl
  | cons b bs ih => simp [bytesVal, List.foldr, ih]

/-- `Convert::assert_nat_blob_last_nonzero` checks that `bs` is non-empty and its last byte is
non-zero, without modifying the heap. -/
theorem assert_nat_blob_last_nonzero_spec {bs : List UInt8} :
    ∀ {bp r : SourceValue F} {h h' : Heap F} {cs : List (Call F)},
      Bytes.RepByteStream Core.byteListEnum h bs bp →
      ObsFn W "Convert::assert_nat_blob_last_nonzero" [bp] h r h' cs →
      h' = h ∧ ∃ last : UInt8, bs.getLast? = some last ∧ last ≠ 0 := by
  induction bs with
  | nil =>
    intro bp r h h' cs hbs ev
    rcases «Convert::assert_nat_blob_last_nonzero».obs ev with
      ⟨_, _, _, _, ld11, _, _, _, _, _, _⟩ |
      ⟨_, _, _, _, _, ld11, _, _, _, _, _, _⟩ |
      ⟨_, _, _, _, ld11, _, _, _, _⟩
    all_goals exact absurd rfl (repList_ne_nil_of_load_cons hbs ld11)
  | cons b rest ih =>
    intro bp r h h' cs hbs ev
    rcases «Convert::assert_nat_blob_last_nonzero».obs ev with
      ⟨_, _, _, _, _, _, _, heq97, _, _, _⟩ |
      ⟨x_byte, x_rest, v45, m46, _, ld11, ld37, ev59, hne103, _, he110, _⟩ |
      ⟨x_byte, x_rest, v26, _, ld11, ld37, hne112, ev121, _⟩
    · simp at heq97
    · obtain ⟨b', rest', heq, hb', hrest⟩ := Core.RepList.cons_of_load hbs ld11
      cases heq
      obtain rfl := repList_nil_of_load hrest ld37
      obtain ⟨hv45, hm46⟩ := Lib.u8_to_field_spec ev59
      have hbv : x_byte = .field (b.toNat : F) := hb'
      have hb_ne : b ≠ 0 := by
        intro hz
        subst hz
        exact hne103 (hv45.symm.trans hbv)
      exact ⟨he110.trans hm46, b, rfl, hb_ne⟩
    · obtain ⟨b', rest', heq, _, hrest⟩ := Core.RepList.cons_of_load hbs ld11
      cases heq
      have hrest_ne : rest ≠ [] := by
        intro hnil
        subst hnil
        cases hrest with
        | nil cell =>
          rw [Core.loadValue_enum_cell cell] at ld37
          injection ld37 with hv
          subst hv
          exact hne112 [] rfl rfl
      obtain ⟨hh', last, hlast, hne⟩ := ih hrest ev121
      refine ⟨hh', last, ?_, hne⟩
      rw [List.getLast?_cons_of_ne_nil hrest_ne]
      exact hlast

/-- `Convert::assert_nat_blob_canonical` checks `Reader.canonicalNatural ⟨bs.toArray⟩ = true`
without modifying the heap. -/
theorem assert_nat_blob_canonical_spec {bs : List UInt8} {bp r : SourceValue F}
    {h h' : Heap F} {cs : List (Call F)}
    (hbs : Bytes.RepByteStream Core.byteListEnum h bs bp)
    (ev : ObsFn W "Convert::assert_nat_blob_canonical" [bp] h r h' cs) :
    Ix.Kernel.Reader.canonicalNatural ⟨bs.toArray⟩ = true ∧ h' = h := by
  rcases «Convert::assert_nat_blob_canonical».obs ev with
    ⟨_, heq45, _, _, _⟩ |
    ⟨w58, x_rest, ld12, ld80, _, he91, _⟩ |
    ⟨w58, x_rest, v69, _, ld12, ld80, hne93, ev102, _⟩
  · simp at heq45
  · obtain ⟨b, rest, rfl, _, hrest⟩ := Core.RepList.cons_of_load hbs ld12
    obtain rfl := repList_nil_of_load hrest ld80
    refine ⟨?_, he91⟩
    simp [Ix.Kernel.Reader.canonicalNatural, ByteArray.size]
  · obtain ⟨b, rest, rfl, _, hrest⟩ := Core.RepList.cons_of_load hbs ld12
    obtain ⟨hh', last, hlast, hne⟩ := assert_nat_blob_last_nonzero_spec hrest ev102
    have hrest_ne : rest ≠ [] := by
      intro hnil
      subst hnil
      simp at hlast
    have hbs_last : (b :: rest).getLast? = some last := by
      rw [List.getLast?_cons_of_ne_nil hrest_ne]
      exact hlast
    refine ⟨?_, hh'⟩
    unfold Ix.Kernel.Reader.canonicalNatural
    show (match (b :: rest).getLast? with | none => false | some l => l != 0 || _) = true
    rw [hbs_last]
    have hne_b : (last != 0) = true := bne_iff_ne.mpr hne
    simp [hne_b]

/-- Pure byte-packing model of `Convert::bytes_to_u64_limb`. -/
def limbBytesGo : List UInt8 → Nat →
    UInt8 → UInt8 → UInt8 → UInt8 → UInt8 → UInt8 → UInt8 → UInt8 →
    List UInt8
  | _, 8, b0, b1, b2, b3, b4, b5, b6, b7 => [b0, b1, b2, b3, b4, b5, b6, b7]
  | [], _, b0, b1, b2, b3, b4, b5, b6, b7 => [b0, b1, b2, b3, b4, b5, b6, b7]
  | x :: xs, 0, _, b1, b2, b3, b4, b5, b6, b7 => limbBytesGo xs 1 x b1 b2 b3 b4 b5 b6 b7
  | x :: xs, 1, b0, _, b2, b3, b4, b5, b6, b7 => limbBytesGo xs 2 b0 x b2 b3 b4 b5 b6 b7
  | x :: xs, 2, b0, b1, _, b3, b4, b5, b6, b7 => limbBytesGo xs 3 b0 b1 x b3 b4 b5 b6 b7
  | x :: xs, 3, b0, b1, b2, _, b4, b5, b6, b7 => limbBytesGo xs 4 b0 b1 b2 x b4 b5 b6 b7
  | x :: xs, 4, b0, b1, b2, b3, _, b5, b6, b7 => limbBytesGo xs 5 b0 b1 b2 b3 x b5 b6 b7
  | x :: xs, 5, b0, b1, b2, b3, b4, _, b6, b7 => limbBytesGo xs 6 b0 b1 b2 b3 b4 x b6 b7
  | x :: xs, 6, b0, b1, b2, b3, b4, b5, _, b7 => limbBytesGo xs 7 b0 b1 b2 b3 b4 b5 x b7
  | x :: xs, _, b0, b1, b2, b3, b4, b5, b6, _ => limbBytesGo xs 8 b0 b1 b2 b3 b4 b5 b6 x

def pack8 (b0 b1 b2 b3 b4 b5 b6 b7 : UInt8) : Nat :=
  b0.toNat + 256 * b1.toNat + 65536 * b2.toNat + 16777216 * b3.toNat +
    4294967296 * b4.toNat + 1099511627776 * b5.toNat +
    281474976710656 * b6.toNat + 72057594037927936 * b7.toNat

private theorem pack8_lt (b0 b1 b2 b3 b4 b5 b6 b7 : UInt8) :
    pack8 b0 b1 b2 b3 b4 b5 b6 b7 < 18446744073709551616 := by
  have : b0.toNat < 256 := b0.toNat_lt; have : b1.toNat < 256 := b1.toNat_lt
  have : b2.toNat < 256 := b2.toNat_lt; have : b3.toNat < 256 := b3.toNat_lt
  have : b4.toNat < 256 := b4.toNat_lt; have : b5.toNat < 256 := b5.toNat_lt
  have : b6.toNat < 256 := b6.toNat_lt; have : b7.toNat < 256 := b7.toNat_lt
  unfold pack8; omega

private theorem u64Value_pack8 (b0 b1 b2 b3 b4 b5 b6 b7 : UInt8) :
    u64Value (pack8 b0 b1 b2 b3 b4 b5 b6 b7) =
      .tuple [.field (b0.toNat : F), .field (b1.toNat : F), .field (b2.toNat : F),
        .field (b3.toNat : F), .field (b4.toNat : F), .field (b5.toNat : F),
        .field (b6.toNat : F), .field (b7.toNat : F)] := by
  have : b0.toNat < 256 := b0.toNat_lt; have : b1.toNat < 256 := b1.toNat_lt
  have : b2.toNat < 256 := b2.toNat_lt; have : b3.toNat < 256 := b3.toNat_lt
  have : b4.toNat < 256 := b4.toNat_lt; have : b5.toNat < 256 := b5.toNat_lt
  have : b6.toNat < 256 := b6.toNat_lt; have : b7.toNat < 256 := b7.toNat_lt
  unfold u64Value pack8
  simp only [Value.tuple.injEq, List.cons.injEq, Value.field.injEq, and_true]
  refine ⟨congrArg Nat.cast (by omega), congrArg Nat.cast (by omega),
    congrArg Nat.cast (by omega), congrArg Nat.cast (by omega),
    congrArg Nat.cast (by omega), congrArg Nat.cast (by omega),
    congrArg Nat.cast (by omega), congrArg Nat.cast (by omega)⟩

private theorem bytes_to_u64_limb_go (bs : List UInt8) :
    ∀ (pos : Nat) (hpos : pos ≤ 8) (b0 b1 b2 b3 b4 b5 b6 b7 : UInt8)
      {bp r : SourceValue F} {h h' : Heap F} {cs : List (Call F)},
      Bytes.RepByteStream Core.byteListEnum h bs bp →
      ObsFn W "Convert::bytes_to_u64_limb"
        [bp, .tuple [.field (b0.toNat : F), .field (b1.toNat : F), .field (b2.toNat : F),
          .field (b3.toNat : F), .field (b4.toNat : F), .field (b5.toNat : F),
          .field (b6.toNat : F), .field (b7.toNat : F)], .field (pos : F)] h r h' cs →
      h' = h ∧
        r = .tuple ((limbBytesGo bs pos b0 b1 b2 b3 b4 b5 b6 b7).map fun b => .field (b.toNat : F)) := by
  induction bs with
  | nil =>
    intro pos hpos b0 b1 b2 b3 b4 b5 b6 b7 bp r h h' cs hbs ev
    rcases «Convert::bytes_to_u64_limb».obs ev with
      ⟨hv14, he16, he17, _⟩ |
      ⟨hne19, ld34, he43, he44, _⟩ |
      ⟨_, _, _, _, _, _, _, _, _, _, _, _, ld34, _, _, _, _⟩ |
      ⟨_, _, _, _, _, _, _, _, _, _, _, _, ld34, _, _, _, _, _⟩ |
      ⟨_, _, _, _, _, _, _, _, _, _, _, _, ld34, _, _, _, _, _, _⟩ |
      ⟨_, _, _, _, _, _, _, _, _, _, _, _, ld34, _, _, _, _, _, _, _⟩ |
      ⟨_, _, _, _, _, _, _, _, _, _, _, _, ld34, _, _, _, _, _, _, _, _⟩ |
      ⟨_, _, _, _, _, _, _, _, _, _, _, _, ld34, _, _, _, _, _, _, _, _, _⟩ |
      ⟨_, _, _, _, _, _, _, _, _, _, _, _, ld34, _, _, _, _, _, _, _, _, _, _⟩ |
      ⟨_, _, _, _, _, _, _, _, _, _, _, _, ld34, _, _, _, _, _, _, _, _, _, _⟩
    · have hp8 : pos = 8 :=
        (natCast_eq_ofNat_iff (n := 8) (by omega) (by omega)).mp (Value.field.inj hv14)
      subst hp8 he16 he17
      exact ⟨rfl, rfl⟩
    · subst he43 he44
      have hp_ne : pos ≠ 8 := fun hp => hne19 (by subst hp; rfl)
      have hlt : pos < 8 := by omega
      interval_cases pos <;> exact ⟨rfl, rfl⟩
    all_goals exact absurd rfl (repList_ne_nil_of_load_cons hbs ld34)
  | cons x xs ih =>
    intro pos hpos b0 b1 b2 b3 b4 b5 b6 b7 bp r h h' cs hbs ev
    rcases «Convert::bytes_to_u64_limb».obs ev with
      ⟨hv14, he16, he17, _⟩ |
      ⟨_, ld34, _, _, _⟩ |
      ⟨x_byte, x_rest, v0, v1, v2, v3, v4, v5, v6, v7, _, _, ld34, hv73, hv128, ev_rec, _⟩ |
      ⟨x_byte, x_rest, v0, v1, v2, v3, v4, v5, v6, v7, _, _, ld34, hv73, _, hv228, ev_rec, _⟩ |
      ⟨x_byte, x_rest, v0, v1, v2, v3, v4, v5, v6, v7, _, _, ld34, hv73, _, _, hv328, ev_rec, _⟩ |
      ⟨x_byte, x_rest, v0, v1, v2, v3, v4, v5, v6, v7, _, _, ld34, hv73, _, _, _, hv428, ev_rec, _⟩ |
      ⟨x_byte, x_rest, v0, v1, v2, v3, v4, v5, v6, v7, _, _, ld34, hv73, _, _, _, _, hv528, ev_rec, _⟩ |
      ⟨x_byte, x_rest, v0, v1, v2, v3, v4, v5, v6, v7, _, _, ld34, hv73, _, _, _, _, _, hv628, ev_rec, _⟩ |
      ⟨x_byte, x_rest, v0, v1, v2, v3, v4, v5, v6, v7, _, _, ld34, hv73, _, _, _, _, _, _, hv728, ev_rec, _⟩ |
      ⟨x_byte, x_rest, v0, v1, v2, v3, v4, v5, v6, v7, _, hne8, ld34, hv73, hne0, hne1, hne2,
        hne3, hne4, hne5, hne6, ev_rec, _⟩
    · have hp8 : pos = 8 :=
        (natCast_eq_ofNat_iff (n := 8) (by omega) (by omega)).mp (Value.field.inj hv14)
      subst hp8 he16 he17
      exact ⟨rfl, rfl⟩
    · have hnil := repList_nil_of_load hbs ld34
      simp at hnil
    · have hp : pos = 0 := (natCast_eq_zero_iff (by omega)).mp (Value.field.inj hv128)
      subst hp
      obtain ⟨x', xs', heq, hx, hxs⟩ := Core.RepList.cons_of_load hbs ld34
      cases heq
      have hxb : x_byte = .field (x.toNat : F) := hx
      simp only [Value.tuple.injEq, List.cons.injEq, and_true] at hv73
      rcases hv73 with ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      rw [hxb] at ev_rec
      exact ih 1 (by omega) x b1 b2 b3 b4 b5 b6 b7 hxs ev_rec
    · have hp : pos = 1 := (natCast_eq_one_iff (by omega)).mp (Value.field.inj hv228)
      subst hp
      obtain ⟨x', xs', heq, hx, hxs⟩ := Core.RepList.cons_of_load hbs ld34
      cases heq
      have hxb : x_byte = .field (x.toNat : F) := hx
      simp only [Value.tuple.injEq, List.cons.injEq, and_true] at hv73
      rcases hv73 with ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      rw [hxb] at ev_rec
      exact ih 2 (by omega) b0 x b2 b3 b4 b5 b6 b7 hxs ev_rec
    · have hp : pos = 2 := (natCast_eq_ofNat_iff (n := 2) (by omega) (by omega)).mp (Value.field.inj hv328)
      subst hp
      obtain ⟨x', xs', heq, hx, hxs⟩ := Core.RepList.cons_of_load hbs ld34
      cases heq
      have hxb : x_byte = .field (x.toNat : F) := hx
      simp only [Value.tuple.injEq, List.cons.injEq, and_true] at hv73
      rcases hv73 with ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      rw [hxb] at ev_rec
      exact ih 3 (by omega) b0 b1 x b3 b4 b5 b6 b7 hxs ev_rec
    · have hp : pos = 3 := (natCast_eq_ofNat_iff (n := 3) (by omega) (by omega)).mp (Value.field.inj hv428)
      subst hp
      obtain ⟨x', xs', heq, hx, hxs⟩ := Core.RepList.cons_of_load hbs ld34
      cases heq
      have hxb : x_byte = .field (x.toNat : F) := hx
      simp only [Value.tuple.injEq, List.cons.injEq, and_true] at hv73
      rcases hv73 with ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      rw [hxb] at ev_rec
      exact ih 4 (by omega) b0 b1 b2 x b4 b5 b6 b7 hxs ev_rec
    · have hp : pos = 4 := (natCast_eq_ofNat_iff (n := 4) (by omega) (by omega)).mp (Value.field.inj hv528)
      subst hp
      obtain ⟨x', xs', heq, hx, hxs⟩ := Core.RepList.cons_of_load hbs ld34
      cases heq
      have hxb : x_byte = .field (x.toNat : F) := hx
      simp only [Value.tuple.injEq, List.cons.injEq, and_true] at hv73
      rcases hv73 with ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      rw [hxb] at ev_rec
      exact ih 5 (by omega) b0 b1 b2 b3 x b5 b6 b7 hxs ev_rec
    · have hp : pos = 5 := (natCast_eq_ofNat_iff (n := 5) (by omega) (by omega)).mp (Value.field.inj hv628)
      subst hp
      obtain ⟨x', xs', heq, hx, hxs⟩ := Core.RepList.cons_of_load hbs ld34
      cases heq
      have hxb : x_byte = .field (x.toNat : F) := hx
      simp only [Value.tuple.injEq, List.cons.injEq, and_true] at hv73
      rcases hv73 with ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      rw [hxb] at ev_rec
      exact ih 6 (by omega) b0 b1 b2 b3 b4 x b6 b7 hxs ev_rec
    · have hp : pos = 6 := (natCast_eq_ofNat_iff (n := 6) (by omega) (by omega)).mp (Value.field.inj hv728)
      subst hp
      obtain ⟨x', xs', heq, hx, hxs⟩ := Core.RepList.cons_of_load hbs ld34
      cases heq
      have hxb : x_byte = .field (x.toNat : F) := hx
      simp only [Value.tuple.injEq, List.cons.injEq, and_true] at hv73
      rcases hv73 with ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      rw [hxb] at ev_rec
      exact ih 7 (by omega) b0 b1 b2 b3 b4 b5 x b7 hxs ev_rec
    · have hp : pos = 7 := by
        interval_cases pos
        · exact absurd rfl hne0
        · exact absurd rfl hne1
        · exact absurd rfl hne2
        · exact absurd rfl hne3
        · exact absurd rfl hne4
        · exact absurd rfl hne5
        · exact absurd rfl hne6
        · rfl
        · exact absurd rfl hne8
      subst hp
      obtain ⟨x', xs', heq, hx, hxs⟩ := Core.RepList.cons_of_load hbs ld34
      cases heq
      have hxb : x_byte = .field (x.toNat : F) := hx
      simp only [Value.tuple.injEq, List.cons.injEq, and_true] at hv73
      rcases hv73 with ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      rw [hxb] at ev_rec
      exact ih 8 (by omega) b0 b1 b2 b3 b4 b5 b6 x hxs ev_rec

/-- `Convert::bytes_to_u64_limb` from `pos = 0` and `[0; 8]` packs the first (up to 8) bytes of
`bs` into a `RepU64` word whose value plus `2^64 * bytesVal (bs.drop 8)` equals `bytesVal bs`. -/
theorem bytes_to_u64_limb_spec {bs : List UInt8} {bp r : SourceValue F}
    {h h' : Heap F} {cs : List (Call F)}
    (hbs : Bytes.RepByteStream Core.byteListEnum h bs bp)
    (ev : ObsFn W "Convert::bytes_to_u64_limb"
      [bp, .tuple (List.replicate 8 (.field 0)), .field 0] h r h' cs) :
    h' = h ∧ ∃ w : UInt64, RepU64 h w r ∧
      w.toNat + 18446744073709551616 * bytesVal (bs.drop 8) = bytesVal bs := by
  have ev' : ObsFn W "Convert::bytes_to_u64_limb"
      [bp, .tuple [.field ((0 : UInt8).toNat : F), .field ((0 : UInt8).toNat : F),
        .field ((0 : UInt8).toNat : F), .field ((0 : UInt8).toNat : F),
        .field ((0 : UInt8).toNat : F), .field ((0 : UInt8).toNat : F),
        .field ((0 : UInt8).toNat : F), .field ((0 : UInt8).toNat : F)], .field (0 : F)]
      h r h' cs := ev
  obtain ⟨hh', hr⟩ := bytes_to_u64_limb_go bs 0 (by omega) 0 0 0 0 0 0 0 0 hbs ev'
  refine ⟨hh', ?_⟩
  have hsplit : ∃ b0 b1 b2 b3 b4 b5 b6 b7 : UInt8,
      limbBytesGo bs 0 0 0 0 0 0 0 0 0 = [b0, b1, b2, b3, b4, b5, b6, b7] ∧
      pack8 b0 b1 b2 b3 b4 b5 b6 b7 + 18446744073709551616 * bytesVal (bs.drop 8) = bytesVal bs := by
    match bs with
    | [] => exact ⟨0, 0, 0, 0, 0, 0, 0, 0, rfl, by simp [pack8, bytesVal]⟩
    | [x0] => exact ⟨x0, 0, 0, 0, 0, 0, 0, 0, rfl, by simp [pack8, bytesVal]; omega⟩
    | [x0, x1] => exact ⟨x0, x1, 0, 0, 0, 0, 0, 0, rfl, by simp [pack8, bytesVal]; omega⟩
    | [x0, x1, x2] => exact ⟨x0, x1, x2, 0, 0, 0, 0, 0, rfl, by simp [pack8, bytesVal]; omega⟩
    | [x0, x1, x2, x3] => exact ⟨x0, x1, x2, x3, 0, 0, 0, 0, rfl, by simp [pack8, bytesVal]; omega⟩
    | [x0, x1, x2, x3, x4] =>
      exact ⟨x0, x1, x2, x3, x4, 0, 0, 0, rfl, by simp [pack8, bytesVal]; omega⟩
    | [x0, x1, x2, x3, x4, x5] =>
      exact ⟨x0, x1, x2, x3, x4, x5, 0, 0, rfl, by simp [pack8, bytesVal]; omega⟩
    | [x0, x1, x2, x3, x4, x5, x6] =>
      exact ⟨x0, x1, x2, x3, x4, x5, x6, 0, rfl, by simp [pack8, bytesVal]; omega⟩
    | x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: rest =>
      exact ⟨x0, x1, x2, x3, x4, x5, x6, x7, by cases rest <;> rfl,
        by simp [pack8, bytesVal]; omega⟩
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7, hgo, hval⟩ := hsplit
  rw [hgo] at hr
  simp only [List.map] at hr
  rw [← u64Value_pack8] at hr
  have hlt := pack8_lt b0 b1 b2 b3 b4 b5 b6 b7
  refine ⟨UInt64.ofNatLT (pack8 b0 b1 b2 b3 b4 b5 b6 b7) hlt, ?_, ?_⟩
  · rw [hr]
    exact Lib.repU64_ofNatLT h hlt
  · rw [UInt64.toNat_ofNatLT]
    exact hval

/-- `Convert::skip_bytes` drops `n` bytes (`n ≤ 8`) from a byte stream. -/
theorem skip_bytes_spec (n : Nat) (hn : n ≤ 8) :
    ∀ {bs : List UInt8} {bp r : SourceValue F} {h h' : Heap F} {cs : List (Call F)},
      Bytes.RepByteStream Core.byteListEnum h bs bp →
      ObsFn W "Convert::skip_bytes" [bp, .field (n : F)] h r h' cs →
      Heap.Extends h h' ∧ Bytes.RepByteStream Core.byteListEnum h' (bs.drop n) r := by
  induction n with
  | zero =>
    intro bs bp r h h' cs hbs ev
    rcases «Convert::skip_bytes».obs ev with
      ⟨_, he16, he17, _⟩ | ⟨hne19, _, _, _, _⟩ | ⟨_, _, _, _, hne19, _, _, _, _⟩
    · subst he16 he17
      exact ⟨Heap.Extends.refl _, hbs⟩
    · exact absurd rfl hne19
    · exact absurd rfl hne19
  | succ n ih =>
    intro bs bp r h h' cs hbs ev
    rcases «Convert::skip_bytes».obs ev with
      ⟨hv14, _, _, _⟩ |
      ⟨_, ld34, he46, hm45, _⟩ |
      ⟨w58, x_rest, _, v76, _, ld34, op97, ev74, _⟩
    · have h0 := (natCast_eq_zero_iff (by omega)).mp (Value.field.inj hv14)
      omega
    · obtain rfl := repList_nil_of_load hbs ld34
      subst he46 hm45
      exact ⟨Heap.Extends.snoc _ _, Lib.rep_store_nil _⟩
    · obtain ⟨b, rest, rfl, _, hrest⟩ := Core.RepList.cons_of_load hbs ld34
      simp only [evalBinOp, Except.ok.injEq] at op97
      have hsub : (((n + 1 : Nat) : F) - 1) = (n : F) := by push_cast; ring
      rw [← op97, hsub] at ev74
      exact ih (by omega) hrest ev74

private theorem bytes_to_limbs_go (fuel : Nat) :
    ∀ {bs : List UInt8} {bp r : SourceValue F} {h h' : Heap F} {cs : List (Call F)},
      bs.length ≤ fuel →
      Bytes.RepByteStream Core.byteListEnum h bs bp →
      ObsFn W "Convert::bytes_to_limbs" [bp] h r h' cs →
      Heap.Extends h h' ∧ ∃ limbs : List UInt64,
        RepList Core.limbListEnum RepU64 h' limbs r ∧
        limbs.getLast? ≠ some 0 ∧
        Core.limbsVal limbs = bytesVal bs := by
  induction fuel with
  | zero =>
    intro bs bp r h h' cs hlen hbs ev
    have hbs_nil : bs = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst hbs_nil
    rcases «Convert::bytes_to_limbs».obs ev with
      ⟨v1, m2, _, v39, m40, _, v115, m116, _, m144, _, ev14, ev52, sg123, ld135, ev157,
        he174, hm173, _⟩ |
      ⟨v1, m2, _, v39, m40, _, v115, m116, _, m144, _, m202, ev14, ev52, sg123, ld135, ev157,
        he188, hm187, hm210, _⟩ |
      ⟨v1, m2, _, v39, m40, _, v115, m116, _, v124, ev14, ev52, sg123, ld135, hne216,
        _, _, _⟩
    · obtain ⟨hm2, w, hw, hval⟩ := bytes_to_u64_limb_spec hbs ev14
      subst m2
      obtain ⟨ext40, hskip⟩ := skip_bytes_spec 8 (by omega) hbs ev52
      rcases sg123 with ⟨_, _, hm90, _⟩ | ⟨v68, _, ld79, hne96, _, _⟩
      · subst hm90
        obtain ⟨_, hm144⟩ := Lib.u64_is_zero_spec (repU64_heapMono₂ (ext40.trans (Heap.Extends.snoc _ _)) hw) ev157
        subst hm144 he174 hm173
        refine ⟨(ext40.trans (Heap.Extends.snoc _ _)).trans (Heap.Extends.snoc _ _), [],
          Lib.rep_store_nil _, by simp, ?_⟩
        simp only [List.drop_nil, bytesVal, Nat.mul_zero, Nat.add_zero] at hval
        simp [Core.limbsVal]
      · cases hskip with
        | nil cell =>
          rw [Core.loadValue_enum_cell cell] at ld79
          injection ld79 with hv; subst hv
          exact hne96 [] rfl rfl
    · obtain ⟨hm2, w, hw, hval⟩ := bytes_to_u64_limb_spec hbs ev14
      subst m2
      obtain ⟨ext40, hskip⟩ := skip_bytes_spec 8 (by omega) hbs ev52
      simp only [List.drop_nil, bytesVal, Nat.mul_zero, Nat.add_zero] at hval
      rcases sg123 with ⟨_, _, hm90, _⟩ | ⟨v68, _, ld79, hne96, _, _⟩
      · subst hm90
        obtain ⟨hiz, _⟩ := Lib.u64_is_zero_spec (repU64_heapMono₂ (ext40.trans (Heap.Extends.snoc _ _)) hw) ev157
        simp [hval] at hiz
      · cases hskip with
        | nil cell =>
          rw [Core.loadValue_enum_cell cell] at ld79
          injection ld79 with hv; subst hv
          exact hne96 [] rfl rfl
    · obtain ⟨hm2, _, _, _⟩ := bytes_to_u64_limb_spec hbs ev14
      subst m2
      obtain ⟨_, hskip⟩ := skip_bytes_spec 8 (by omega) hbs ev52
      rcases sg123 with ⟨_, he91, hm90, _⟩ | ⟨v68, _, ld79, hne96, _, _⟩
      · subst he91 hm90
        have hcell : (m40 ++ [.construct Core.limbListEnum "Nil" []])[m40.length]? =
            some (.construct Core.limbListEnum "Nil" []) := by simp
        rw [Core.loadValue_enum_cell hcell] at ld135
        injection ld135 with hv; subst hv
        exact hne216 [] rfl rfl
      · cases hskip with
        | nil cell =>
          rw [Core.loadValue_enum_cell cell] at ld79
          injection ld79 with hv; subst hv
          exact hne96 [] rfl rfl
  | succ fuel ih =>
    intro bs bp r h h' cs hlen hbs ev
    have seg1_spec : ∀ {v39 v1 v115 : SourceValue F} {m40 m116 : Heap F} {cs118 : List (Call F)},
        Bytes.RepByteStream Core.byteListEnum m40 (bs.drop 8) v39 →
        «Convert::bytes_to_limbs».Seg1 v39 v1 bp m40 v115 m116 cs118 →
        Heap.Extends m40 m116 ∧ ∃ rlimbs : List UInt64,
          RepList Core.limbListEnum RepU64 m116 rlimbs v115 ∧
          rlimbs.getLast? ≠ some 0 ∧
          Core.limbsVal rlimbs = bytesVal (bs.drop 8) := by
      intro v39 v1 v115 m40 m116 cs118 hskip sg
      rcases sg with ⟨ld79, he91, hm90, _⟩ | ⟨v68, _, ld79, hne96, ev105, _⟩
      · have hdrop_nil := repList_nil_of_load hskip ld79
        subst he91 hm90
        exact ⟨Heap.Extends.snoc _ _, [], Lib.rep_store_nil _, by simp,
          by simp [hdrop_nil, Core.limbsVal, bytesVal]⟩
      · have hdrop_ne : bs.drop 8 ≠ [] := by
          intro hnil
          rw [hnil] at hskip
          cases hskip with
          | nil cell =>
            rw [Core.loadValue_enum_cell cell] at ld79
            injection ld79 with hv; subst hv
            exact hne96 [] rfl rfl
        have hbs_pos : 8 < bs.length := by
          by_contra hle
          exact hdrop_ne (List.drop_eq_nil_iff.mpr (by omega))
        have hdrop_len : (bs.drop 8).length ≤ fuel := by
          rw [List.length_drop]; omega
        exact ih hdrop_len hskip ev105
    rcases «Convert::bytes_to_limbs».obs ev with
      ⟨v1, m2, _, v39, m40, _, v115, m116, _, m144, _, ev14, ev52, sg123, ld135, ev157,
        he174, hm173, _⟩ |
      ⟨v1, m2, _, v39, m40, _, v115, m116, _, m144, _, m202, ev14, ev52, sg123, ld135, ev157,
        he188, hm187, hm210, _⟩ |
      ⟨v1, m2, _, v39, m40, _, v115, m116, _, v124, ev14, ev52, sg123, ld135, hne216,
        he224, hm223, _⟩
    · obtain ⟨hm2, w, hw, hval⟩ := bytes_to_u64_limb_spec hbs ev14
      subst m2
      obtain ⟨ext40, hskip⟩ := skip_bytes_spec 8 (by omega) hbs ev52
      obtain ⟨ext116, rlimbs, hrlimbs, _, hrval⟩ := seg1_spec hskip sg123
      obtain rfl := repList_nil_of_load hrlimbs ld135
      obtain ⟨hiz, hm144⟩ := Lib.u64_is_zero_spec (repU64_heapMono₂ (ext40.trans ext116) hw) ev157
      subst hm144 he174 hm173
      have hw0 : w.toNat = 0 := by
        by_cases hz : w.toNat = 0
        · exact hz
        · simp [hz] at hiz
      refine ⟨(ext40.trans ext116).trans (Heap.Extends.snoc _ _), [],
        Lib.rep_store_nil _, by simp, ?_⟩
      simp only [Core.limbsVal] at hrval ⊢
      omega
    · obtain ⟨hm2, w, hw, hval⟩ := bytes_to_u64_limb_spec hbs ev14
      subst m2
      obtain ⟨ext40, hskip⟩ := skip_bytes_spec 8 (by omega) hbs ev52
      obtain ⟨ext116, rlimbs, hrlimbs, _, hrval⟩ := seg1_spec hskip sg123
      obtain rfl := repList_nil_of_load hrlimbs ld135
      obtain ⟨hiz, hm144⟩ := Lib.u64_is_zero_spec (repU64_heapMono₂ (ext40.trans ext116) hw) ev157
      subst hm144 he188 hm187 hm210
      have hw_ne : w.toNat ≠ 0 := by
        intro hz
        simp [hz] at hiz
      have hw_ne0 : w ≠ 0 := fun hz => hw_ne (by subst hz; rfl)
      have ext_nil : Heap.Extends m116 (m116 ++ [.construct Core.limbListEnum "Nil" []]) :=
        Heap.Extends.snoc _ _
      have ext_cons : Heap.Extends (m116 ++ [.construct Core.limbListEnum "Nil" []])
          ((m116 ++ [.construct Core.limbListEnum "Nil" []]) ++
            [.construct Core.limbListEnum "Cons"
              [v1, .ptr (.enum Core.limbListEnum) m116.length]]) :=
        Heap.Extends.snoc _ _
      refine ⟨((ext40.trans ext116).trans ext_nil).trans ext_cons, [w],
        Lib.rep_store_cons repU64_heapMono₂
          (repU64_heapMono₂ ((ext40.trans ext116).trans ext_nil) hw)
          (Lib.rep_store_nil _),
        by simp [hw_ne0], ?_⟩
      simp only [Core.limbsVal] at hrval ⊢
      omega
    · obtain ⟨hm2, w, hw, hval⟩ := bytes_to_u64_limb_spec hbs ev14
      subst m2
      obtain ⟨ext40, hskip⟩ := skip_bytes_spec 8 (by omega) hbs ev52
      obtain ⟨ext116, rlimbs, hrlimbs, hrlast, hrval⟩ := seg1_spec hskip sg123
      have hr_ne : rlimbs ≠ [] := by
        intro hnil
        subst hnil
        cases hrlimbs with
        | nil cell =>
          rw [Core.loadValue_enum_cell cell] at ld135
          injection ld135 with hv; subst hv
          exact hne216 [] rfl rfl
      subst he224 hm223
      refine ⟨(ext40.trans ext116).trans (Heap.Extends.snoc _ _), w :: rlimbs,
        Lib.rep_store_cons repU64_heapMono₂
          (repU64_heapMono₂ (ext40.trans ext116) hw) hrlimbs,
        by rw [List.getLast?_cons_of_ne_nil hr_ne]; exact hrlast, ?_⟩
      simp only [Core.limbsVal]
      omega

/-- `Convert::bytes_to_limbs` converts a byte stream `bs` to canonical little-endian 64-bit limbs
whose `Core.limbsVal` equals `Reader.natural ⟨bs.toArray⟩`. -/
theorem bytes_to_limbs_spec {bs : List UInt8} {bp r : SourceValue F}
    {h h' : Heap F} {cs : List (Call F)}
    (hbs : Bytes.RepByteStream Core.byteListEnum h bs bp)
    (ev : ObsFn W "Convert::bytes_to_limbs" [bp] h r h' cs) :
    Heap.Extends h h' ∧ ∃ limbs : List UInt64,
      RepList Core.limbListEnum RepU64 h' limbs r ∧
      limbs.getLast? ≠ some 0 ∧
      Core.limbsVal limbs = Ix.Kernel.Reader.natural ⟨bs.toArray⟩ := by
  obtain ⟨ext, limbs, hrep, hlast, hval⟩ := bytes_to_limbs_go bs.length (Nat.le_refl _) hbs ev
  exact ⟨ext, limbs, hrep, hlast, hval.trans (bytesVal_eq_natural bs)⟩

/-! ## Universe level conversion (`RawKLevel`, `convert_univ`, `convert_univ_idxs`, `posOf`) -/

/-- Heap representation of a kernel universe level produced unconditionally by
`Convert::convert_univ` (whose `.param` index is bounded by `2^56` via `UInt64::to_field`;
upgraded to `KernelLevels.RepKLevel` once parameters are bounded below `2^32`). -/
inductive RawKLevel (h : Heap F) : Core.KLevel → SourceValue F → Prop where
  | zero {addr : Nat}
      (cell : h[addr]? = some (.construct Core.klevelEnum "Zero" [])) :
      RawKLevel h .zero (.ptr (.enum Core.klevelEnum) addr)
  | succ {l : Core.KLevel} {p : SourceValue F} {addr : Nat}
      (cell : h[addr]? = some (.construct Core.klevelEnum "Succ" [p]))
      (inner : RawKLevel h l p) :
      RawKLevel h (.succ l) (.ptr (.enum Core.klevelEnum) addr)
  | max {l₁ l₂ : Core.KLevel} {p₁ p₂ : SourceValue F} {addr : Nat}
      (cell : h[addr]? = some (.construct Core.klevelEnum "Max" [p₁, p₂]))
      (left : RawKLevel h l₁ p₁)
      (right : RawKLevel h l₂ p₂) :
      RawKLevel h (.max l₁ l₂) (.ptr (.enum Core.klevelEnum) addr)
  | imax {l₁ l₂ : Core.KLevel} {p₁ p₂ : SourceValue F} {addr : Nat}
      (cell : h[addr]? = some (.construct Core.klevelEnum "IMax" [p₁, p₂]))
      (left : RawKLevel h l₁ p₁)
      (right : RawKLevel h l₂ p₂) :
      RawKLevel h (.imax l₁ l₂) (.ptr (.enum Core.klevelEnum) addr)
  | param {n : Nat} {addr : Nat}
      (hn : n < 72057594037927936)
      (cell : h[addr]? = some (.construct Core.klevelEnum "Param" [.field (n : F)])) :
      RawKLevel h (.param n) (.ptr (.enum Core.klevelEnum) addr)

abbrev RawKLevelList (h : Heap F) (ls : List Core.KLevel) (p : SourceValue F) : Prop :=
  RepList Core.klevelListEnum RawKLevel h ls p

theorem RawKLevel.mono {h₁ h₂ : Heap F} {l : Core.KLevel} {p : SourceValue F}
    (ext : Heap.Extends h₁ h₂) (rep : RawKLevel h₁ l p) : RawKLevel h₂ l p := by
  induction rep with
  | zero cell => exact .zero (ext.getElem?_eq cell)
  | succ cell _ ih => exact .succ (ext.getElem?_eq cell) ih
  | max cell _ _ ihl ihr => exact .max (ext.getElem?_eq cell) ihl ihr
  | imax cell _ _ ihl ihr => exact .imax (ext.getElem?_eq cell) ihl ihr
  | param hn cell => exact .param hn (ext.getElem?_eq cell)

theorem rawKLevel_heapMono₂ : HeapMono₂ RawKLevel :=
  fun _ _ _ _ ext rep => rep.mono ext

theorem RawKLevelList.mono {h₁ h₂ : Heap F} {ls : List Core.KLevel} {p : SourceValue F}
    (ext : Heap.Extends h₁ h₂) (rep : RawKLevelList h₁ ls p) : RawKLevelList h₂ ls p :=
  repList_heapMono₂ Core.klevelListEnum rawKLevel_heapMono₂ ext rep

/-- Upgrade `RawKLevel` to `KernelLevels.RepKLevel` once all parameters are below `2^32`. -/
theorem RawKLevel.toRepKLevel {h : Heap F} {l : Core.KLevel} {p : SourceValue F}
    (rep : RawKLevel h l p) (hplt : KernelLevels.ParamsLt 4294967296 l) :
    KernelLevels.RepKLevel h l p := by
  induction rep with
  | zero cell => exact .zero cell
  | succ cell _ ih => exact .succ cell (ih hplt)
  | max cell _ _ ihl ihr => exact .max cell (ihl hplt.1) (ihr hplt.2)
  | imax cell _ _ ihl ihr => exact .imax cell (ihl hplt.1) (ihr hplt.2)
  | param _ cell => exact .param hplt cell

/-- Upgrade `RawKLevelList` to `Core.RepKLevelList` once all parameters are below `2^32`. -/
theorem RawKLevelList.toRepKLevelList {h : Heap F} {ls : List Core.KLevel} {p : SourceValue F}
    (rep : RawKLevelList h ls p) (hplt : ∀ l ∈ ls, KernelLevels.ParamsLt 4294967296 l) :
    KernelLevels.RepKLevelList h ls p := by
  induction rep with
  | nil cell =>
    rw [Core.klevelListEnum_eq] at cell
    exact .nil cell
  | cons cell hhd _ ih =>
    rw [Core.klevelListEnum_eq] at cell
    exact .cons cell (hhd.toRepKLevel (hplt _ (by simp)))
      (ih (fun l hl => hplt l (List.mem_cons_of_mem _ hl)))

/-- `Convert::convert_univ` converts an `Ixon.Univ` heap node to `Reader.convUniv id u`. -/
theorem convert_univ_spec {u : Ixon.Univ} :
    ∀ {up r : SourceValue F} {h h' : Heap F} {cs : List (Call F)},
      RepUnivPtr h u up →
      ObsFn W "Convert::convert_univ" [up] h r h' cs →
      Heap.Extends h h' ∧ RawKLevel h' (Ix.Kernel.Reader.convUniv id u) r := by
  induction u with
  | zero =>
    intro up r h h' cs hup ev
    obtain ⟨addr, v, rfl, cell, hv⟩ := hup
    cases hv
    rcases «Convert::convert_univ».obs ev with
      ⟨_, he24, hm23, _⟩ | ⟨_, _, _, _, ld12, _, _, _, _⟩ |
      ⟨_, _, _, _, _, _, _, _, ld12, _, _, _, _, _⟩ |
      ⟨_, _, _, _, _, _, _, _, ld12, _, _, _, _, _⟩ |
      ⟨_, _, _, _, ld12, _, _, _, _⟩
    · subst he24 hm23
      exact ⟨Heap.Extends.snoc _ _, .zero (by simp)⟩
    all_goals exact (Core.load_cell_ne cell ld12 (by decide)).elim
  | succ inner ih =>
    intro up r h h' cs hup ev
    obtain ⟨addr, v, rfl, cell, hv⟩ := hup
    cases hv with
    | succ cellIn repIn =>
      rcases «Convert::convert_univ».obs ev with
        ⟨ld12, _, _, _⟩ | ⟨x_inner, v49, m51, _, ld12, he45, hm44, ev61, _⟩ |
        ⟨_, _, _, _, _, _, _, _, ld12, _, _, _, _, _⟩ |
        ⟨_, _, _, _, _, _, _, _, ld12, _, _, _, _, _⟩ |
        ⟨_, _, _, _, ld12, _, _, _, _⟩
      · exact (Core.load_cell_ne cell ld12 (by decide)).elim
      · have hxs := (Core.load_cell cell ld12).2
        simp only [List.cons.injEq, and_true] at hxs
        subst hxs he45 hm44
        obtain ⟨ext1, hrec⟩ := ih ⟨_, _, rfl, cellIn, repIn⟩ ev61
        exact ⟨ext1.trans (Heap.Extends.snoc _ _),
          .succ (by simp) (hrec.mono (Heap.Extends.snoc _ _))⟩
      all_goals exact (Core.load_cell_ne cell ld12 (by decide)).elim
  | max a b iha ihb =>
    intro up r h h' cs hup ev
    obtain ⟨addr, v, rfl, cell, hv⟩ := hup
    cases hv with
    | max cellA cellB repA repB =>
      rcases «Convert::convert_univ».obs ev with
        ⟨ld12, _, _, _⟩ | ⟨_, _, _, _, ld12, _, _, _, _⟩ |
        ⟨x_a, x_b, v96, v97, m99, _, m119, _, ld12, he92, hm91, ev109, ev129, _⟩ |
        ⟨_, _, _, _, _, _, _, _, ld12, _, _, _, _, _⟩ |
        ⟨_, _, _, _, ld12, _, _, _, _⟩
      · exact (Core.load_cell_ne cell ld12 (by decide)).elim
      · exact (Core.load_cell_ne cell ld12 (by decide)).elim
      · have hxs := (Core.load_cell cell ld12).2
        simp only [List.cons.injEq, and_true] at hxs
        obtain ⟨rfl, rfl⟩ := hxs
        subst he92 hm91
        obtain ⟨ext1, hrecA⟩ := iha ⟨_, _, rfl, cellA, repA⟩ ev109
        obtain ⟨ext2, hrecB⟩ := ihb (RepUnivPtr.mono ext1 ⟨_, _, rfl, cellB, repB⟩) ev129
        have ext_fin := Heap.Extends.snoc m119
          (.construct Core.klevelEnum "Max" [v96, v97])
        exact ⟨(ext1.trans ext2).trans ext_fin,
          .max (by simp) (hrecA.mono (ext2.trans ext_fin)) (hrecB.mono ext_fin)⟩
      all_goals exact (Core.load_cell_ne cell ld12 (by decide)).elim
  | imax a b iha ihb =>
    intro up r h h' cs hup ev
    obtain ⟨addr, v, rfl, cell, hv⟩ := hup
    cases hv with
    | imax cellA cellB repA repB =>
      rcases «Convert::convert_univ».obs ev with
        ⟨ld12, _, _, _⟩ | ⟨_, _, _, _, ld12, _, _, _, _⟩ |
        ⟨_, _, _, _, _, _, _, _, ld12, _, _, _, _, _⟩ |
        ⟨x_a, x_b, v164, v165, m167, _, m187, _, ld12, he160, hm159, ev177, ev197, _⟩ |
        ⟨_, _, _, _, ld12, _, _, _, _⟩
      · exact (Core.load_cell_ne cell ld12 (by decide)).elim
      · exact (Core.load_cell_ne cell ld12 (by decide)).elim
      · exact (Core.load_cell_ne cell ld12 (by decide)).elim
      · have hxs := (Core.load_cell cell ld12).2
        simp only [List.cons.injEq, and_true] at hxs
        obtain ⟨rfl, rfl⟩ := hxs
        subst he160 hm159
        obtain ⟨ext1, hrecA⟩ := iha ⟨_, _, rfl, cellA, repA⟩ ev177
        obtain ⟨ext2, hrecB⟩ := ihb (RepUnivPtr.mono ext1 ⟨_, _, rfl, cellB, repB⟩) ev197
        have ext_fin := Heap.Extends.snoc m187
          (.construct Core.klevelEnum "IMax" [v164, v165])
        exact ⟨(ext1.trans ext2).trans ext_fin,
          .imax (by simp) (hrecA.mono (ext2.trans ext_fin)) (hrecB.mono ext_fin)⟩
      · exact (Core.load_cell_ne cell ld12 (by decide)).elim
  | var idx =>
    intro up r h h' cs hup ev
    obtain ⟨addr, v, rfl, cell, hv⟩ := hup
    cases hv with
    | var idx =>
      rcases «Convert::convert_univ».obs ev with
        ⟨ld12, _, _, _⟩ | ⟨_, _, _, _, ld12, _, _, _, _⟩ |
        ⟨_, _, _, _, _, _, _, _, ld12, _, _, _, _, _⟩ |
        ⟨_, _, _, _, _, _, _, _, ld12, _, _, _, _, _⟩ |
        ⟨x_idx, v227, m229, _, ld12, he223, hm222, ev239, _⟩
      · exact (Core.load_cell_ne cell ld12 (by decide)).elim
      · exact (Core.load_cell_ne cell ld12 (by decide)).elim
      · exact (Core.load_cell_ne cell ld12 (by decide)).elim
      · exact (Core.load_cell_ne cell ld12 (by decide)).elim
      · have hxs := (Core.load_cell cell ld12).2
        simp only [List.cons.injEq, and_true] at hxs
        subst hxs he223 hm222
        have hx_u64 : RepU64 h idx (u64Value idx.toNat) := Deserialize.repU64_u64Value h idx
        obtain ⟨hlt, hv227, hm229⟩ := Lib.u64_to_field_spec hx_u64 ev239
        subst hv227 hm229
        exact ⟨Heap.Extends.snoc _ _, .param hlt (by simp)⟩

private theorem univList_inst_eq :
    (Instance.mk "Lists::Node" [.ptr (.named "Ixon::Univ" [])]).symbol = univListEnum := by
  decide +kernel

private theorem univLookup_inst_eq :
    (Instance.mk "Lists::lookup" [.ptr (.named "Ixon::Univ" [])]).symbol =
      Names.«Lists::lookup<&Ixon::Univ>» := by
  decide +kernel

/-- `Convert::convert_univ_idxs` looks up each index in `univs` and converts it with
`Reader.convUniv id`. -/
theorem convert_univ_idxs_spec {idxs : List UInt64} {univs : List Ixon.Univ} :
    ∀ {idxsPtr univsPtr r : SourceValue F} {h h' : Heap F} {cs : List (Call F)},
      RepList u64ListEnum RepU64 h idxs idxsPtr →
      RepList univListEnum RepUnivPtr h univs univsPtr →
      ObsFn W "Convert::convert_univ_idxs" [idxsPtr, univsPtr] h r h' cs →
      Heap.Extends h h' ∧ ∃ ls : List Core.KLevel,
        RawKLevelList h' ls r ∧
        idxs.mapM (fun i => univs[i.toNat]?.map (Ix.Kernel.Reader.convUniv id)) = some ls := by
  induction idxs with
  | nil =>
    intro idxsPtr univsPtr r h h' cs hidxs hunivs ev
    rw [u64ListEnum_eq] at hidxs
    rcases «Convert::convert_univ_idxs».obs ev with
      ⟨_, he24, hm23, _⟩ | ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, ld12, _, _, _, _, _, _, _⟩
    · subst he24 hm23
      exact ⟨Heap.Extends.snoc _ _, [], Lib.rep_store_nil _, rfl⟩
    · exact absurd rfl (repList_ne_nil_of_load_cons hidxs ld12)
  | cons idx rest ih =>
    intro idxsPtr univsPtr r h h' cs hidxs hunivs ev
    rw [u64ListEnum_eq] at hidxs
    rcases «Convert::convert_univ_idxs».obs ev with
      ⟨ld12, _, _, _⟩ |
      ⟨x_idx, x_rest, v46, m47, _, v61, m70, _, v97, v98, m100, _, m120, _,
        ld12, ev80, ev59, he93, hm92, ev110, ev130, _⟩
    · have hnil := repList_nil_of_load hidxs ld12
      simp at hnil
    · obtain ⟨idx', rest', heq, hidx, hrest⟩ := Core.RepList.cons_of_load hidxs ld12
      cases heq
      obtain ⟨hlt, hv61, hm70⟩ := Lib.u64_to_field_spec hidx ev80
      subst hv61 hm70
      rw [← univLookup_inst_eq] at ev59
      have hunivs' : RepList (Instance.mk "Lists::Node" [.ptr (.named "Ixon::Univ" [])]).symbol
          RepUnivPtr h univs univsPtr := by
        rwa [univList_inst_eq]
      obtain ⟨⟨u, hu_get, hu_rep⟩, hm47⟩ := Lib.Lists.lookup_spec ev59 hunivs'
      subst hm47
      have hval_idx : ((idx.toNat : F).val) = idx.toNat :=
        ZMod.val_cast_of_lt (by have := idx.toNat_lt; omega)
      rw [hval_idx] at hu_get
      obtain ⟨ext1, hconv1⟩ := convert_univ_spec hu_rep ev110
      rw [← u64ListEnum_eq] at hrest
      obtain ⟨ext2, ls_rest, hls_rep, hmap_rest⟩ :=
        ih (repList_heapMono₂ _ repU64_heapMono₂ ext1 hrest)
          (repList_heapMono₂ _ repUnivPtr_heapMono₂ ext1 hunivs) ev130
      subst he93 hm92
      have ext_fin := Heap.Extends.snoc m120
        (.construct Core.klevelListEnum "Cons" [v97, v98])
      refine ⟨(ext1.trans ext2).trans ext_fin,
        Ix.Kernel.Reader.convUniv id u :: ls_rest,
        Lib.rep_store_cons rawKLevel_heapMono₂ (hconv1.mono ext2) hls_rep, ?_⟩
      simp only [List.mapM_cons, hu_get, Option.map_some, Option.bind_some, hmap_rest]
      rfl

/-- Inverse positional level renaming: maps positional parameter `i < ps.length` to `ps[i]`,
leaving out-of-range parameters untouched. -/
def invPosLevel (ps : List Ix.Kernel.LevelParam) : Core.KLevel → Core.KLevel
  | .zero => .zero
  | .succ l => .succ (invPosLevel ps l)
  | .max a b => .max (invPosLevel ps a) (invPosLevel ps b)
  | .imax a b => .imax (invPosLevel ps a) (invPosLevel ps b)
  | .param i => if h : i < ps.length then .param ps[i] else .param i

private theorem subst_go_nodup_getElem :
    ∀ {ks : List Ix.Kernel.LevelParam} {vs : List Core.KLevel} {i : Nat},
      ks.Nodup → (hi : i < ks.length) → (hiv : i < vs.length) →
      Ix.Kernel.Level.subst.go ks vs ks[i] = vs[i]'hiv
  | [], _, _, _, hi, _ => absurd hi (Nat.not_lt_zero _)
  | k :: ks, [], _, _, _, hiv => absurd hiv (Nat.not_lt_zero _)
  | k :: ks, v :: vs, 0, _, _, _ => by
    simp [Ix.Kernel.Level.subst.go]
  | k :: ks, v :: vs, i + 1, hnd, hi, hiv => by
    obtain ⟨hk_not_mem, hnd_ks⟩ := List.nodup_cons.mp hnd
    have hmem : ks[i]'(Nat.lt_of_succ_lt_succ hi) ∈ ks := List.getElem_mem _
    have hne : k ≠ ks[i]'(Nat.lt_of_succ_lt_succ hi) :=
      fun heq => hk_not_mem (by rw [heq]; exact hmem)
    simp only [List.getElem_cons_succ, Ix.Kernel.Level.subst.go, if_neg hne]
    exact subst_go_nodup_getElem hnd_ks (Nat.lt_of_succ_lt_succ hi) (Nat.lt_of_succ_lt_succ hiv)

private theorem subst_go_not_mem :
    ∀ (ks : List Ix.Kernel.LevelParam) (vs : List Core.KLevel) {q : Ix.Kernel.LevelParam},
      q ∉ ks → Ix.Kernel.Level.subst.go ks vs q = .param q
  | [], _, _, _ => rfl
  | _ :: _, [], _, _ => rfl
  | k :: ks, _ :: vs, q, hq => by
    have hne : k ≠ q := fun heq => hq (by simp [heq])
    simp only [Ix.Kernel.Level.subst.go, if_neg hne]
    exact subst_go_not_mem ks vs (fun hm => hq (List.mem_cons_of_mem _ hm))

/-- `posOf`'s level substitution cancels `invPosLevel` for every permutation of `0 .. n-1`. -/
theorem subst_posLevels_invPosLevel {ps : List Ix.Kernel.LevelParam}
    (hperm : ps.Perm (List.range ps.length)) :
    ∀ ℓ : Core.KLevel, Ix.Kernel.Level.subst ps (Core.posLevels ps) (invPosLevel ps ℓ) = ℓ
  | .zero => rfl
  | .succ l => congrArg Ix.Kernel.Level.succ (subst_posLevels_invPosLevel hperm l)
  | .max a b =>
    congrArg₂ Ix.Kernel.Level.max
      (subst_posLevels_invPosLevel hperm a) (subst_posLevels_invPosLevel hperm b)
  | .imax a b =>
    congrArg₂ Ix.Kernel.Level.imax
      (subst_posLevels_invPosLevel hperm a) (subst_posLevels_invPosLevel hperm b)
  | .param i => by
    have hnd : ps.Nodup := hperm.nodup_iff.mpr List.nodup_range
    unfold invPosLevel
    split
    · next hi =>
      show Ix.Kernel.Level.subst.go ps (Core.posLevels ps) ps[i] = .param i
      have hlen : i < (Core.posLevels ps).length := by simp [Core.posLevels, hi]
      rw [subst_go_nodup_getElem hnd hi hlen]
      simp [Core.posLevels]
    · next hni =>
      show Ix.Kernel.Level.subst.go ps (Core.posLevels ps) i = .param i
      apply subst_go_not_mem
      intro hmem
      have hr : i ∈ List.range ps.length := hperm.mem_iff.mp hmem
      simp only [List.mem_range] at hr
      exact hni hr

/-- `posOf` on `Core.bmeta (invPosLevel ps ℓ)` recovers `Core.bmeta ℓ`. -/
theorem substPW_posLevels_bmeta {ps : List Ix.Kernel.LevelParam}
    (hperm : ps.Perm (List.range ps.length)) (ℓ : Core.KLevel) :
    { (Core.bmeta (invPosLevel ps ℓ)) with
        pw := Ix.Kernel.Level.substPW ps (Core.posLevels ps) (Core.bmeta (invPosLevel ps ℓ)).pw } =
      Core.bmeta ℓ := by
  dsimp only [Core.bmeta]
  congr 1
  apply Ix.Kernel.PropWhen.eq_of_holds
  intro φ
  rw [Ix.Kernel.Level.holds_substPW, Ix.Kernel.PropWhen.zeronessOf_sound,
    ← Ix.Kernel.Level.eval_subst, subst_posLevels_invPosLevel hperm,
    Ix.Kernel.PropWhen.zeronessOf_sound]

/-- For any `ps` permuting `List.range ps.length` (`ps.length < 2^32`), if
`Reader.convUniv (Reader.recParam ps) u` has all parameters in `ps`, then `posOf` maps it to
`Reader.convUniv id u` and all parameters of `Reader.convUniv id u` are below `2^32`. -/
theorem convUniv_posOf_eq {ps : List Ix.Kernel.LevelParam}
    (hperm : ps.Perm (List.range ps.length)) (hps_lt : ps.length < 4294967296) :
    ∀ {u : Ixon.Univ},
      (Ix.Kernel.Reader.convUniv (Ix.Kernel.Reader.recParam ps) u).allParamsDefined ps = true →
      Ix.Kernel.Level.subst ps (Core.posLevels ps)
          (Ix.Kernel.Reader.convUniv (Ix.Kernel.Reader.recParam ps) u) =
        Ix.Kernel.Reader.convUniv id u ∧
      KernelLevels.ParamsLt 4294967296 (Ix.Kernel.Reader.convUniv id u)
  | .zero, _ => ⟨rfl, trivial⟩
  | .succ u, hd => by
    obtain ⟨heq, hlt⟩ := convUniv_posOf_eq hperm hps_lt (u := u) hd
    exact ⟨congrArg Ix.Kernel.Level.succ heq, hlt⟩
  | .max a b, hd => by
    simp only [Ix.Kernel.Reader.convUniv, Ix.Kernel.Level.allParamsDefined, Bool.and_eq_true] at hd
    obtain ⟨heqA, hltA⟩ := convUniv_posOf_eq hperm hps_lt hd.1
    obtain ⟨heqB, hltB⟩ := convUniv_posOf_eq hperm hps_lt hd.2
    exact ⟨congrArg₂ Ix.Kernel.Level.max heqA heqB, hltA, hltB⟩
  | .imax a b, hd => by
    simp only [Ix.Kernel.Reader.convUniv, Ix.Kernel.Level.allParamsDefined, Bool.and_eq_true] at hd
    obtain ⟨heqA, hltA⟩ := convUniv_posOf_eq hperm hps_lt hd.1
    obtain ⟨heqB, hltB⟩ := convUniv_posOf_eq hperm hps_lt hd.2
    exact ⟨congrArg₂ Ix.Kernel.Level.imax heqA heqB, hltA, hltB⟩
  | .var idx, hd => by
    simp only [Ix.Kernel.Reader.convUniv, Ix.Kernel.Level.allParamsDefined,
      List.contains_iff_mem] at hd
    have hi_lt : idx.toNat < ps.length := by
      by_contra hge
      have hgetD : Ix.Kernel.Reader.recParam ps idx.toNat = idx.toNat := by
        unfold Ix.Kernel.Reader.recParam List.getD
        rw [List.getElem?_eq_none (by omega)]
        rfl
      rw [hgetD] at hd
      have hr : idx.toNat ∈ List.range ps.length := hperm.mem_iff.mp hd
      simp only [List.mem_range] at hr
      omega
    have hrec_eq : Ix.Kernel.Reader.recParam ps idx.toNat = ps[idx.toNat] := by
      unfold Ix.Kernel.Reader.recParam List.getD
      rw [List.getElem?_eq_getElem hi_lt]
      rfl
    have hnd : ps.Nodup := hperm.nodup_iff.mpr List.nodup_range
    have hplen : idx.toNat < (Core.posLevels ps).length := by simp [Core.posLevels, hi_lt]
    refine ⟨?_, by show idx.toNat < 4294967296; omega⟩
    show Ix.Kernel.Level.subst.go ps (Core.posLevels ps) (Ix.Kernel.Reader.recParam ps idx.toNat) =
      .param idx.toNat
    rw [hrec_eq, subst_go_nodup_getElem hnd hi_lt hplen]
    simp [Core.posLevels]

/-! ## Binder search tree (`binder_table`, `binder_nodes`) and `binder_level` -/

abbrev binderTreeEnum : String := "Convert::BinderTreeNode"
abbrev binderPairListEnum : String :=
  Names.«Lists::Node<(Field, Field, Field, &Convert::BinderTreeNode)>»

/-- Heap invariant for a `Convert::BinderTree`: every leaf stores a `RepList` of `RepBinderNode`
whose parameter indices are below `bound`. -/
inductive RepBinderTree (bound : Nat) (h : Heap F) : SourceValue F → Prop where
  | empty {addr : Nat}
      (cell : h[addr]? = some (.construct binderTreeEnum "Empty" [])) :
      RepBinderTree bound h (.ptr (.enum binderTreeEnum) addr)
  | leaf {addr : Nat} {e i v nodesPtr : SourceValue F} {ns : List Ixon.BinderNode}
      (cell : h[addr]? = some (.construct binderTreeEnum "Leaf" [e, i, v, nodesPtr]))
      (hrep : RepList binderNodeListEnum RepBinderNode h ns nodesPtr)
      (hplt : ∀ nd ∈ ns, BinderNodeParamsLt bound nd) :
      RepBinderTree bound h (.ptr (.enum binderTreeEnum) addr)
  | node {addr : Nat} {e i v left right : SourceValue F}
      (cell : h[addr]? = some (.construct binderTreeEnum "Node" [e, i, v, left, right]))
      (hleft : RepBinderTree bound h left)
      (hright : RepBinderTree bound h right) :
      RepBinderTree bound h (.ptr (.enum binderTreeEnum) addr)

theorem RepBinderTree.mono {bound : Nat} {h₁ h₂ : Heap F} {p : SourceValue F}
    (ext : Heap.Extends h₁ h₂) (rep : RepBinderTree bound h₁ p) :
    RepBinderTree bound h₂ p := by
  induction rep with
  | empty cell => exact .empty (ext.getElem?_eq cell)
  | leaf cell hrep hplt =>
    exact .leaf (ext.getElem?_eq cell)
      (repList_heapMono₂ _ repBinderNode_heapMono₂ ext hrep) hplt
  | node cell _ _ ihl ihr => exact .node (ext.getElem?_eq cell) ihl ihr

/-- Element representation for `(Field, Field, Field, Convert::BinderTree)` list entries. -/
def RepBinderTreeEntry (bound : Nat) (h : Heap F) (_u : Unit) (v : SourceValue F) : Prop :=
  ∃ e i var t, v = .tuple [e, i, var, t] ∧ RepBinderTree bound h t

theorem repBinderTreeEntry_heapMono₂ (bound : Nat) : HeapMono₂ (RepBinderTreeEntry bound) :=
  fun _ _ _ _ ext ⟨e, i, var, t, hv, ht⟩ => ⟨e, i, var, t, hv, ht.mono ext⟩

/-- `Convert::binder_key_lt` allocates nothing (`h' = h`). -/
theorem binder_key_lt_spec {e1 i1 v1 e2 i2 v2 r : SourceValue F} {h h' : Heap F}
    {cs : List (Call F)}
    (ev : ObsFn W "Convert::binder_key_lt" [e1, i1, v1, e2, i2, v2] h r h' cs) :
    h' = h := by
  rcases «Convert::binder_key_lt».obs ev with
    ⟨_, _, _, ev52, _⟩ | ⟨_, _, _, _, _, ev79, _⟩ | ⟨_, _, _, _, he103, _⟩
  · obtain ⟨_, _, _, _, _, _, _, hh⟩ := Lib.less_than_fields_spec ev52
    exact hh
  · obtain ⟨_, _, _, _, _, _, _, hh⟩ := Lib.less_than_fields_spec ev79
    exact hh
  · exact he103

/-- `Convert::binder_leaves` builds a list of leaf `BinderTree` entries preserving parameter bounds. -/
theorem binder_leaves_spec {bound : Nat} {blocks : List Ixon.BinderBlock} :
    ∀ {blocksPtr r : SourceValue F} {h h' : Heap F} {cs : List (Call F)},
      RepList binderBlockListEnum RepBinderBlock h blocks blocksPtr →
      (∀ b ∈ blocks, ∀ nd ∈ b.nodes.toList, BinderNodeParamsLt bound nd) →
      ObsFn W "Convert::binder_leaves" [blocksPtr] h r h' cs →
      Heap.Extends h h' ∧ ∃ us : List Unit,
        RepList binderPairListEnum (RepBinderTreeEntry bound) h' us r := by
  induction blocks with
  | nil =>
    intro blocksPtr r h h' cs hblks _ ev
    rw [binderBlockListEnum_eq] at hblks
    rcases «Convert::binder_leaves».obs ev with
      ⟨_, he24, hm23, _⟩ |
      ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, ld12, _, _, _, _, _, _, _⟩
    · subst he24 hm23
      exact ⟨Heap.Extends.snoc _ _, [], Lib.rep_store_nil _⟩
    · exact absurd rfl (repList_ne_nil_of_load_cons hblks ld12)
  | cons blk rest ih =>
    intro blocksPtr r h h' cs hblks hplt ev
    rw [binderBlockListEnum_eq] at hblks
    rcases «Convert::binder_leaves».obs ev with
      ⟨ld12, _, _, _⟩ |
      ⟨x_rest, x_ekind, x_eidx, x_variant, x_nodes, v78, m79, _, v100, m101, _, v131, m166,
        m211, _, ld12, ev91, ev113, he126, hm125, hm174, ev221, _⟩
    · have hnil := repList_nil_of_load hblks ld12
      simp at hnil
    · obtain ⟨blk', rest', heq, hblk, hrest⟩ := Core.RepList.cons_of_load hblks ld12
      cases heq
      obtain ⟨nodesPtr, hmk, hnodes⟩ := hblk
      simp only [Value.construct.injEq, List.cons.injEq, true_and, and_true] at hmk
      rcases hmk with ⟨rfl, rfl, rfl, rfl⟩
      obtain ⟨_, hv78, hm79⟩ :=
        Lib.u64_to_field_spec (Deserialize.repU64_u64Value h blk.index) ev91
      subst hv78 hm79
      obtain ⟨_, hv100, hm101⟩ :=
        Lib.u64_to_field_spec (Deserialize.repU64_u64Value h blk.variant) ev113
      subst hv100 hm101
      have ext_leaf : Heap.Extends h m166 := by
        rw [hm174]; exact Heap.Extends.snoc _ _
      have hleaf : RepBinderTree bound m166 (.ptr (.enum binderTreeEnum) h.length) := by
        rw [hm174]
        exact .leaf (by simp)
          (repList_heapMono₂ _ repBinderNode_heapMono₂ (Heap.Extends.snoc _ _) hnodes)
          (fun nd hnd => hplt blk (by simp) nd hnd)
      rw [← binderBlockListEnum_eq] at hrest
      obtain ⟨ext_rest, us, hus⟩ :=
        ih (repList_heapMono₂ _ repBinderBlock_heapMono₂ ext_leaf hrest)
          (fun b hb nd hnd => hplt b (List.mem_cons_of_mem _ hb) nd hnd) ev221
      subst he126 hm125
      have ext_cons := Heap.Extends.snoc m211
        (.construct binderPairListEnum "Cons"
          [.tuple [.field ((if blk.shared then 1 else 0 : Nat) : F),
              .field (blk.index.toNat : F), .field (blk.variant.toNat : F),
              .ptr (.enum binderTreeEnum) h.length], v131])
      exact ⟨(ext_leaf.trans ext_rest).trans ext_cons, () :: us,
        Lib.rep_store_cons (repBinderTreeEntry_heapMono₂ bound)
          ⟨_, _, _, _, rfl, hleaf.mono ext_rest⟩ hus⟩

private theorem binder_pairs_go (n : Nat) :
    ∀ {us : List Unit} {lvlPtr r : SourceValue F} {h h' : Heap F} {cs : List (Call F)},
      us.length ≤ n →
      RepList binderPairListEnum (RepBinderTreeEntry bound) h us lvlPtr →
      ObsFn W "Convert::binder_pairs" [lvlPtr] h r h' cs →
      Heap.Extends h h' ∧ ∃ us' : List Unit,
        RepList binderPairListEnum (RepBinderTreeEntry bound) h' us' r := by
  induction n with
  | zero =>
    intro us lvlPtr r h h' cs hlen hlvl ev
    have hus_nil : us = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst hus_nil
    rcases «Convert::binder_pairs».obs ev with
      ⟨_, he24, hm23, _⟩ | ⟨_, _, ld12, _, _, _, _⟩ |
      ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, ld12, _, _, _, _, _, _⟩
    · subst he24 hm23
      exact ⟨Heap.Extends.snoc _ _, [], Lib.rep_store_nil _⟩
    all_goals exact absurd rfl (repList_ne_nil_of_load_cons hlvl ld12)
  | succ n ih =>
    intro us lvlPtr r h h' cs hlen hlvl ev
    rcases «Convert::binder_pairs».obs ev with
      ⟨_, he24, hm23, _⟩ |
      ⟨x_x, x_rest, _, _, he66, he67, _⟩ |
      ⟨x_rest, x_rest2, x_e1, x_i1, x_v1, x_t1, x_e2, x_i2, x_v2, x_t2, v159, m194, m247, _,
        ld12, ld57, he154, hm153, hm202, ev257, _⟩
    · subst he24 hm23
      exact ⟨Heap.Extends.snoc _ _, [], Lib.rep_store_nil _⟩
    · subst he66 he67
      exact ⟨Heap.Extends.refl _, us, hlvl⟩
    · obtain ⟨u1, rest1, rfl, hu1, hrest1⟩ := Core.RepList.cons_of_load hlvl ld12
      obtain ⟨u2, rest2, rfl, hu2, hrest2⟩ := Core.RepList.cons_of_load hrest1 ld57
      obtain ⟨_, _, _, _, heq1, ht1⟩ := hu1
      simp only [Value.tuple.injEq, List.cons.injEq, and_true] at heq1
      rcases heq1 with ⟨rfl, rfl, rfl, rfl⟩
      obtain ⟨_, _, _, _, heq2, ht2⟩ := hu2
      simp only [Value.tuple.injEq, List.cons.injEq, and_true] at heq2
      rcases heq2 with ⟨rfl, rfl, rfl, rfl⟩
      have ext_node : Heap.Extends h m194 := by rw [hm202]; exact Heap.Extends.snoc _ _
      have hnode : RepBinderTree bound m194 (.ptr (.enum binderTreeEnum) h.length) := by
        rw [hm202]
        exact .node (by simp) (ht1.mono (Heap.Extends.snoc _ _)) (ht2.mono (Heap.Extends.snoc _ _))
      simp only [List.length_cons] at hlen
      obtain ⟨ext_rec, us2, hus2⟩ :=
        ih (by omega) (repList_heapMono₂ _ (repBinderTreeEntry_heapMono₂ bound) ext_node hrest2)
          ev257
      subst he154 hm153
      have ext_cons := Heap.Extends.snoc m247
        (.construct binderPairListEnum "Cons"
          [.tuple [x_e1, x_i1, x_v1, .ptr (.enum binderTreeEnum) h.length], v159])
      exact ⟨(ext_node.trans ext_rec).trans ext_cons, () :: us2,
        Lib.rep_store_cons (repBinderTreeEntry_heapMono₂ bound)
          ⟨_, _, _, _, rfl, hnode.mono ext_rec⟩ hus2⟩

private theorem binder_tree_of_go (fuel : Nat) :
    ∀ {us : List Unit} {lvlPtr r : SourceValue F} {h h' : Heap F} {calls : List (Call F)},
      calls.length ≤ fuel →
      RepList binderPairListEnum (RepBinderTreeEntry bound) h us lvlPtr →
      ObsFn W "Convert::binder_tree_of" [lvlPtr] h r h' calls →
      Heap.Extends h h' ∧ RepBinderTree bound h' r := by
  induction fuel with
  | zero =>
    intro us lvlPtr r h h' calls hfuel hlvl ev
    rcases «Convert::binder_tree_of».obs ev with
      ⟨_, he24, hm23, _⟩ |
      ⟨_, _, _, _, x_t, ld12, _, he101, he102, _⟩ |
      ⟨_, _, _, _, _, _, _, _, _, _, _, _, hc135⟩
    · subst he24 hm23
      exact ⟨Heap.Extends.snoc _ _, .empty (by simp)⟩
    · obtain ⟨_, _, _, hu, _⟩ := Core.RepList.cons_of_load hlvl ld12
      obtain ⟨_, _, _, _, heq, ht⟩ := hu
      simp only [Value.tuple.injEq, List.cons.injEq, and_true] at heq
      rcases heq with ⟨_, _, _, rfl⟩
      subst he101 he102
      exact ⟨Heap.Extends.refl _, ht⟩
    · rw [hc135] at hfuel
      simp at hfuel
  | succ fuel ih =>
    intro us lvlPtr r h h' calls hfuel hlvl ev
    rcases «Convert::binder_tree_of».obs ev with
      ⟨_, he24, hm23, _⟩ |
      ⟨_, _, _, _, x_t, ld12, _, he101, he102, _⟩ |
      ⟨_, _, _, cs111, v114, m116, cs124, _, _, _, ev126, ev113, hc135⟩
    · subst he24 hm23
      exact ⟨Heap.Extends.snoc _ _, .empty (by simp)⟩
    · obtain ⟨_, _, _, hu, _⟩ := Core.RepList.cons_of_load hlvl ld12
      obtain ⟨_, _, _, _, heq, ht⟩ := hu
      simp only [Value.tuple.injEq, List.cons.injEq, and_true] at heq
      rcases heq with ⟨_, _, _, rfl⟩
      subst he101 he102
      exact ⟨Heap.Extends.refl _, ht⟩
    · obtain ⟨ext1, us', hus'⟩ := binder_pairs_go us.length (Nat.le_refl _) hlvl ev126
      have hlen111 : cs111.length ≤ fuel := by
        rw [hc135] at hfuel
        simp only [List.length_cons, List.length_append] at hfuel
        omega
      obtain ⟨ext2, htree⟩ := ih hlen111 hus' ev113
      exact ⟨ext1.trans ext2, htree⟩

/-- `Convert::binder_table` builds a `RepBinderTree` from a constant's `binders` list. -/
theorem binder_table_spec {bound : Nat} {blocks : List Ixon.BinderBlock}
    {blocksPtr r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (hblks : RepList binderBlockListEnum RepBinderBlock h blocks blocksPtr)
    (hplt : ∀ b ∈ blocks, ∀ nd ∈ b.nodes.toList, BinderNodeParamsLt bound nd)
    (ev : ObsFn W "Convert::binder_table" [blocksPtr] h r h' cs) :
    Heap.Extends h h' ∧ RepBinderTree bound h' r := by
  obtain ⟨cs4, v7, m9, _, ev19, ev6, _⟩ := «Convert::binder_table».obs ev
  obtain ⟨ext1, us, hus⟩ := binder_leaves_spec hblks hplt ev19
  obtain ⟨ext2, htree⟩ := binder_tree_of_go cs4.length (Nat.le_refl _) hus ev6
  exact ⟨ext1.trans ext2, htree⟩

/-- `Convert::binder_nodes` looks up a block's `BinderNode` list in `tree` without allocation. -/
theorem binder_nodes_spec {bound : Nat} {tree : SourceValue F} {h : Heap F}
    (htree : RepBinderTree bound h tree) :
    ∀ {ek ei evar r : SourceValue F} {h' : Heap F} {cs : List (Call F)},
      ObsFn W "Convert::binder_nodes" [tree, ek, ei, evar] h r h' cs →
      h' = h ∧ ∃ ns : List Ixon.BinderNode,
        RepList binderNodeListEnum RepBinderNode h ns r ∧
        ∀ nd ∈ ns, BinderNodeParamsLt bound nd := by
  induction htree with
  | empty cell =>
    intro ek ei evar r h' cs ev
    rcases «Convert::binder_nodes».obs ev with
      ⟨_, _, _, _, ld12, _, _, _, _, _, _⟩ |
      ⟨_, _, _, _, _, _, _, _, ld12, _, _, _⟩ |
      ⟨_, _, _, _, _, _, _, _, ld12, _, _, _⟩
    all_goals exact (Core.load_cell_ne cell ld12 (by decide)).elim
  | leaf cell hrep hplt =>
    intro ek ei evar r h' cs ev
    rcases «Convert::binder_nodes».obs ev with
      ⟨_, _, _, _, ld12, _, _, _, he125, he126, _⟩ |
      ⟨_, _, _, _, _, _, _, _, ld12, _, _, _⟩ |
      ⟨_, _, _, _, _, _, _, _, ld12, _, _, _⟩
    · have hxs := (Core.load_cell cell ld12).2
      simp only [List.cons.injEq, and_true] at hxs
      rcases hxs with ⟨_, _, _, rfl⟩
      subst he125 he126
      exact ⟨rfl, _, hrep, hplt⟩
    all_goals exact (Core.load_cell_ne cell ld12 (by decide)).elim
  | node cell _ _ ihl ihr =>
    intro ek ei evar r h' cs ev
    rcases «Convert::binder_nodes».obs ev with
      ⟨_, _, _, _, ld12, _, _, _, _, _, _⟩ |
      ⟨_, _, _, _, _, m161, _, _, ld12, ev174, ev232, _⟩ |
      ⟨_, _, _, _, _, m161, _, _, ld12, ev174, ev276, _⟩
    · exact (Core.load_cell_ne cell ld12 (by decide)).elim
    · have hxs := (Core.load_cell cell ld12).2
      simp only [List.cons.injEq, and_true] at hxs
      rcases hxs with ⟨_, _, _, rfl, rfl⟩
      have hm := binder_key_lt_spec ev174
      subst hm
      exact ihl ev232
    · have hxs := (Core.load_cell cell ld12).2
      simp only [List.cons.injEq, and_true] at hxs
      rcases hxs with ⟨_, _, _, rfl, rfl⟩
      have hm := binder_key_lt_spec ev174
      subst hm
      exact ihr ev276

/-- `Convert::params_level` builds a `Max`-chain of `.param` nodes represented by `RepKLevel`. -/
theorem params_level_spec {params : List UInt64} :
    ∀ {paramsPtr r : SourceValue F} {h h' : Heap F} {cs : List (Call F)},
      RepList u64ListEnum RepU64 h params paramsPtr →
      (∀ p ∈ params, p.toNat < 4294967296) →
      ObsFn W "Convert::params_level" [paramsPtr] h r h' cs →
      Heap.Extends h h' ∧ ∃ ℓ : Core.KLevel, KernelLevels.RepKLevel h' ℓ r := by
  induction params with
  | nil =>
    intro paramsPtr r h h' cs hps _ ev
    rw [u64ListEnum_eq] at hps
    rcases «Convert::params_level».obs ev with
      ⟨_, _, _, _, _, _, ld11, _, _, _, _, _, _⟩ |
      ⟨_, _, _, _, _, _, _, _, _, _, ld11, _, _, _, _, _, _, _, _⟩
    all_goals exact absurd rfl (repList_ne_nil_of_load_cons hps ld11)
  | cons p rest ih =>
    intro paramsPtr r h h' cs hps hplt ev
    rw [u64ListEnum_eq] at hps
    rcases «Convert::params_level».obs ev with
      ⟨x_p, x_rest, m27, v41, m43, _, ld11, hm37, ev53, _, he82, he83, _⟩ |
      ⟨x_p, x_rest, m27, v41, m43, _, _, v98, m107, _, ld11, hm37, ev53, _, _,
        he93, hm92, ev117, _⟩
    · obtain ⟨p', rest', heq, hp, _⟩ := Core.RepList.cons_of_load hps ld11
      cases heq
      obtain ⟨_, hv41, hm43⟩ := Lib.u64_to_field_spec hp ev53
      subst hv41 hm43 he82 he83 hm37
      exact ⟨Heap.Extends.snoc _ _, .param p.toNat,
        .param (hplt p (by simp)) (by simp)⟩
    · obtain ⟨p', rest', heq, hp, hrest⟩ := Core.RepList.cons_of_load hps ld11
      cases heq
      obtain ⟨_, hv41, hm43⟩ := Lib.u64_to_field_spec hp ev53
      subst hv41 hm43
      have ext_lp : Heap.Extends h m27 := by rw [hm37]; exact Heap.Extends.snoc _ _
      have hlp : KernelLevels.RepKLevel m27 (.param p.toNat)
          (.ptr (.enum Core.klevelEnum) h.length) := by
        rw [hm37]; exact .param (hplt p (by simp)) (by simp)
      rw [← u64ListEnum_eq] at hrest
      obtain ⟨ext_rec, ℓ_rest, hℓ_rest⟩ :=
        ih (repList_heapMono₂ _ repU64_heapMono₂ ext_lp hrest)
          (fun q hq => hplt q (List.mem_cons_of_mem _ hq)) ev117
      subst he93 hm92
      have ext_max := Heap.Extends.snoc m107
        (.construct Core.klevelEnum "Max" [.ptr (.enum Core.klevelEnum) h.length, v98])
      exact ⟨(ext_lp.trans ext_rec).trans ext_max, .max (.param p.toNat) ℓ_rest,
        .max (by simp) (hlp.mono (ext_rec.trans ext_max)) (hℓ_rest.mono ext_max)⟩

/-- `Convert::binder_level` converts a `RepBinderNode` (with parameters `< 2^32`) into a
`KernelLevels.RepKLevel` value. -/
theorem binder_level_spec {nd : Ixon.BinderNode} {nodeVal r : SourceValue F}
    {h h' : Heap F} {cs : List (Call F)}
    (hnd : RepBinderNode h nd nodeVal)
    (hplt : BinderNodeParamsLt 4294967296 nd)
    (ev : ObsFn W "Convert::binder_level" [nodeVal] h r h' cs) :
    Heap.Extends h h' ∧ ∃ ℓ : Core.KLevel, KernelLevels.RepKLevel h' ℓ r := by
  rcases «Convert::binder_level».obs ev with
    ⟨w17, m33, hv15, he27, hm26, hm41, _⟩ |
    ⟨w53, _, hv51, he63, hm62, _⟩ |
    ⟨x_params, w75, _, _, _, hv73, ev91, _⟩ |
    ⟨_, _, _, _, _, heq139, _, _, _⟩ |
    ⟨_, _, _, _, _, _, heq187, _, _, _⟩
  · subst he27 hm26 hm41
    have ext1 := Heap.Extends.snoc h (.construct Core.klevelEnum "Zero" [])
    have ext2 := Heap.Extends.snoc (h ++ [.construct Core.klevelEnum "Zero" []])
      (.construct Core.klevelEnum "Succ" [.ptr (.enum Core.klevelEnum) h.length])
    have hz : KernelLevels.RepKLevel (h ++ [.construct Core.klevelEnum "Zero" []]) .zero
        (.ptr (.enum Core.klevelEnum) h.length) := .zero (by simp)
    exact ⟨ext1.trans ext2, .succ .zero, .succ (by simp) (hz.mono ext2)⟩
  · subst he63 hm62
    exact ⟨Heap.Extends.snoc _ _, .zero, .zero (by simp)⟩
  · cases hnd with
    | never _ => simp at hv73
    | zero _ => simp at hv73
    | share _ => simp at hv73
    | undecided _ => simp at hv73
    | ifAllZero m hrep =>
      simp only [Value.construct.injEq, List.cons.injEq, true_and, and_true] at hv73
      rcases hv73 with ⟨rfl, _⟩
      exact params_level_spec hrep hplt ev91
  · simp at heq139
  · simp at heq187

/-! ## Manual `ObsExpr` path inversion for `Convert::convert_annotated` -/

/-- Branch relation for `match b { 0 => (k, nodes), _ => convert_annotated(...) }` inside
`Convert::convert_annotated`. -/
inductive AnnotBranch (x_sub x_sharing x_bound x_refs x_recur_addrs x_univs x_tbl : SourceValue F)
    (x_k x_b x_nodes : SourceValue F) (h : Heap F)
    (x_k2 x_nodes' : SourceValue F) (h' : Heap F) (cs : List (Call F)) : Prop where
  | n0 :
      x_b = .field 0 → x_k2 = x_k → x_nodes' = x_nodes → h' = h → cs = [] →
      AnnotBranch x_sub x_sharing x_bound x_refs x_recur_addrs x_univs x_tbl
        x_k x_b x_nodes h x_k2 x_nodes' h' cs
  | other (cs_rec : List (Call F)) :
      x_b ≠ .field 0 →
      ObsFn W "Convert::convert_annotated"
        [x_sub, x_sharing, x_bound, x_refs, x_recur_addrs, x_univs, x_tbl, x_nodes]
        h (.tuple [x_k2, x_nodes']) h' cs_rec →
      cs = (⟨"Convert::convert_annotated",
          [x_sub, x_sharing, x_bound, x_refs, x_recur_addrs, x_univs, x_tbl, x_nodes], h⟩ :
          Call F) :: cs_rec →
      AnnotBranch x_sub x_sharing x_bound x_refs x_recur_addrs x_univs x_tbl
        x_k x_b x_nodes h x_k2 x_nodes' h' cs

/-- Evaluation paths of `Convert::convert_annotated` (6 constructors, one per `Ixon::Expr` arm). -/
inductive ConvertAnnotatedPath
    (x_e x_sharing x_bound x_refs x_recur_addrs x_univs x_tbl x_nodes : SourceValue F)
    (h : Heap F) (r : SourceValue F) (h' : Heap F) (calls : List (Call F)) : Prop where
  | App
      (x_f x_a x_kf x_bf x_ka x_ba x_kf2 x_n1 x_ka2 x_n2 : SourceValue F)
      (m1 m2 m3 m4 : Heap F) (cs1 cs2 cs3 cs4 : List (Call F))
      (ld_e : loadValue h x_e = .ok (.construct "Ixon::Expr" "App" [x_f, x_a]))
      (ev_f : ObsFn W "Convert::convert_expr"
        [x_f, x_sharing, x_bound, x_refs, x_recur_addrs, x_univs] h (.tuple [x_kf, x_bf]) m1 cs1)
      (ev_a : ObsFn W "Convert::convert_expr"
        [x_a, x_sharing, x_bound, x_refs, x_recur_addrs, x_univs] m1 (.tuple [x_ka, x_ba]) m2 cs2)
      (br_f : AnnotBranch x_f x_sharing x_bound x_refs x_recur_addrs x_univs x_tbl
        x_kf x_bf x_nodes m2 x_kf2 x_n1 m3 cs3)
      (br_a : AnnotBranch x_a x_sharing x_bound x_refs x_recur_addrs x_univs x_tbl
        x_ka x_ba x_n1 m3 x_ka2 x_n2 m4 cs4)
      (hr : r = .tuple [.ptr (.enum Core.kexprEnum) m4.length, x_n2])
      (hh' : h' = m4 ++ [.construct Core.kexprEnum "App" [x_kf2, x_ka2]])
      (hcs : calls =
        (⟨"Convert::convert_expr",
            [x_f, x_sharing, x_bound, x_refs, x_recur_addrs, x_univs], h⟩ : Call F) :: cs1 ++
        ((⟨"Convert::convert_expr",
            [x_a, x_sharing, x_bound, x_refs, x_recur_addrs, x_univs], m1⟩ : Call F) :: cs2) ++
        cs3 ++ cs4)
  | Lam
      (x_ty x_body x_node x_n0 x_l x_kt x_bt x_kb x_bb x_kt2 x_n1 x_kb2 x_n2 : SourceValue F)
      (m1 m2 m3 m4 m5 : Heap F) (cs1 cs2 cs3 cs4 cs5 : List (Call F))
      (ld_e : loadValue h x_e = .ok (.construct "Ixon::Expr" "Lam" [x_ty, x_body]))
      (ld_nodes : loadValue h x_nodes =
        .ok (.construct Names.«Lists::Node<Ixon::BinderNode>» "Cons" [x_node, x_n0]))
      (ev_l : ObsFn W "Convert::binder_level" [x_node] h x_l m1 cs1)
      (ev_t : ObsFn W "Convert::convert_expr"
        [x_ty, x_sharing, x_bound, x_refs, x_recur_addrs, x_univs] m1 (.tuple [x_kt, x_bt]) m2 cs2)
      (ev_b : ObsFn W "Convert::convert_expr"
        [x_body, x_sharing, x_bound, x_refs, x_recur_addrs, x_univs] m2 (.tuple [x_kb, x_bb]) m3 cs3)
      (br_t : AnnotBranch x_ty x_sharing x_bound x_refs x_recur_addrs x_univs x_tbl
        x_kt x_bt x_n0 m3 x_kt2 x_n1 m4 cs4)
      (br_b : AnnotBranch x_body x_sharing x_bound x_refs x_recur_addrs x_univs x_tbl
        x_kb x_bb x_n1 m4 x_kb2 x_n2 m5 cs5)
      (hr : r = .tuple [.ptr (.enum Core.kexprEnum) m5.length, x_n2])
      (hh' : h' = m5 ++ [.construct Core.kexprEnum "Lam" [x_kt2, x_kb2, x_l]])
      (hcs : calls =
        (⟨"Convert::binder_level", [x_node], h⟩ : Call F) :: cs1 ++
        ((⟨"Convert::convert_expr",
            [x_ty, x_sharing, x_bound, x_refs, x_recur_addrs, x_univs], m1⟩ : Call F) :: cs2) ++
        ((⟨"Convert::convert_expr",
            [x_body, x_sharing, x_bound, x_refs, x_recur_addrs, x_univs], m2⟩ : Call F) :: cs3) ++
        cs4 ++ cs5)
  | All
      (x_ty x_body x_node x_n0 x_l x_kt x_bt x_kb x_bb x_kt2 x_n1 x_kb2 x_n2 : SourceValue F)
      (m1 m2 m3 m4 m5 : Heap F) (cs1 cs2 cs3 cs4 cs5 : List (Call F))
      (ld_e : loadValue h x_e = .ok (.construct "Ixon::Expr" "All" [x_ty, x_body]))
      (ld_nodes : loadValue h x_nodes =
        .ok (.construct Names.«Lists::Node<Ixon::BinderNode>» "Cons" [x_node, x_n0]))
      (ev_l : ObsFn W "Convert::binder_level" [x_node] h x_l m1 cs1)
      (ev_t : ObsFn W "Convert::convert_expr"
        [x_ty, x_sharing, x_bound, x_refs, x_recur_addrs, x_univs] m1 (.tuple [x_kt, x_bt]) m2 cs2)
      (ev_b : ObsFn W "Convert::convert_expr"
        [x_body, x_sharing, x_bound, x_refs, x_recur_addrs, x_univs] m2 (.tuple [x_kb, x_bb]) m3 cs3)
      (br_t : AnnotBranch x_ty x_sharing x_bound x_refs x_recur_addrs x_univs x_tbl
        x_kt x_bt x_n0 m3 x_kt2 x_n1 m4 cs4)
      (br_b : AnnotBranch x_body x_sharing x_bound x_refs x_recur_addrs x_univs x_tbl
        x_kb x_bb x_n1 m4 x_kb2 x_n2 m5 cs5)
      (hr : r = .tuple [.ptr (.enum Core.kexprEnum) m5.length, x_n2])
      (hh' : h' = m5 ++ [.construct Core.kexprEnum "Forall" [x_kt2, x_kb2, x_l]])
      (hcs : calls =
        (⟨"Convert::binder_level", [x_node], h⟩ : Call F) :: cs1 ++
        ((⟨"Convert::convert_expr",
            [x_ty, x_sharing, x_bound, x_refs, x_recur_addrs, x_univs], m1⟩ : Call F) :: cs2) ++
        ((⟨"Convert::convert_expr",
            [x_body, x_sharing, x_bound, x_refs, x_recur_addrs, x_univs], m2⟩ : Call F) :: cs3) ++
        cs4 ++ cs5)
  | Let
      (w_hdr x_ty x_val x_body x_kt x_bt x_kv x_bv x_kb x_bb
        x_kt2 x_n1 x_kv2 x_n2 x_kb2 x_n3 : SourceValue F)
      (m1 m2 m3 m4 m5 m6 : Heap F) (cs1 cs2 cs3 cs4 cs5 cs6 : List (Call F))
      (ld_e : loadValue h x_e = .ok (.construct "Ixon::Expr" "Let" [w_hdr, x_ty, x_val, x_body]))
      (ev_t : ObsFn W "Convert::convert_expr"
        [x_ty, x_sharing, x_bound, x_refs, x_recur_addrs, x_univs] h (.tuple [x_kt, x_bt]) m1 cs1)
      (ev_v : ObsFn W "Convert::convert_expr"
        [x_val, x_sharing, x_bound, x_refs, x_recur_addrs, x_univs] m1 (.tuple [x_kv, x_bv]) m2 cs2)
      (ev_b : ObsFn W "Convert::convert_expr"
        [x_body, x_sharing, x_bound, x_refs, x_recur_addrs, x_univs] m2 (.tuple [x_kb, x_bb]) m3 cs3)
      (br_t : AnnotBranch x_ty x_sharing x_bound x_refs x_recur_addrs x_univs x_tbl
        x_kt x_bt x_nodes m3 x_kt2 x_n1 m4 cs4)
      (br_v : AnnotBranch x_val x_sharing x_bound x_refs x_recur_addrs x_univs x_tbl
        x_kv x_bv x_n1 m4 x_kv2 x_n2 m5 cs5)
      (br_b : AnnotBranch x_body x_sharing x_bound x_refs x_recur_addrs x_univs x_tbl
        x_kb x_bb x_n2 m5 x_kb2 x_n3 m6 cs6)
      (hr : r = .tuple [.ptr (.enum Core.kexprEnum) m6.length, x_n3])
      (hh' : h' = m6 ++ [.construct Core.kexprEnum "Let" [x_kt2, x_kv2, x_kb2]])
      (hcs : calls =
        (⟨"Convert::convert_expr",
            [x_ty, x_sharing, x_bound, x_refs, x_recur_addrs, x_univs], h⟩ : Call F) :: cs1 ++
        ((⟨"Convert::convert_expr",
            [x_val, x_sharing, x_bound, x_refs, x_recur_addrs, x_univs], m1⟩ : Call F) :: cs2) ++
        ((⟨"Convert::convert_expr",
            [x_body, x_sharing, x_bound, x_refs, x_recur_addrs, x_univs], m2⟩ : Call F) :: cs3) ++
        cs4 ++ cs5 ++ cs6)
  | Prj
      (x_tidx x_fidx x_inner v_tidx x_taddr x_ki x_n1 v_fidx : SourceValue F)
      (m1 m2 m3 m4 : Heap F) (cs1 cs2 cs3 cs4 : List (Call F))
      (ld_e : loadValue h x_e = .ok (.construct "Ixon::Expr" "Prj" [x_tidx, x_fidx, x_inner]))
      (ev_tf : ObsFn W "UInt64::to_field" [x_tidx] h v_tidx m1 cs1)
      (ev_lk : ObsFn W Names.«Lists::lookup<&[Field; 32]>» [x_refs, v_tidx] m1 x_taddr m2 cs2)
      (ev_in : ObsFn W "Convert::convert_annotated"
        [x_inner, x_sharing, x_bound, x_refs, x_recur_addrs, x_univs, x_tbl, x_nodes]
        m2 (.tuple [x_ki, x_n1]) m3 cs3)
      (ev_ff : ObsFn W "UInt64::to_field" [x_fidx] m3 v_fidx m4 cs4)
      (hr : r = .tuple [.ptr (.enum Core.kexprEnum) m4.length, x_n1])
      (hh' : h' = m4 ++ [.construct Core.kexprEnum "Proj" [x_taddr, v_fidx, x_ki]])
      (hcs : calls =
        (⟨"UInt64::to_field", [x_tidx], h⟩ : Call F) :: cs1 ++
        ((⟨Names.«Lists::lookup<&[Field; 32]>», [x_refs, v_tidx], m1⟩ : Call F) :: cs2) ++
        ((⟨"Convert::convert_annotated",
            [x_inner, x_sharing, x_bound, x_refs, x_recur_addrs, x_univs, x_tbl, x_nodes], m2⟩ :
            Call F) :: cs3) ++
        ((⟨"UInt64::to_field", [x_fidx], m3⟩ : Call F) :: cs4))
  | Share
      (x_idx x_n p_drop x_s w_tail x_node x_n1 x_variant v_var x_enodes x_k : SourceValue F)
      (m1 m2 m3 m4 m5 : Heap F) (cs1 cs2 cs3 cs4 cs5 : List (Call F))
      (ld_e : loadValue h x_e = .ok (.construct "Ixon::Expr" "Share" [x_idx]))
      (ev_nf : ObsFn W "UInt64::to_field" [x_idx] h x_n m1 cs1)
      (ev_dr : ObsFn W Names.«Lists::drop<&Ixon::Expr>» [x_sharing, x_n] m1 p_drop m2 cs2)
      (ld_dr : loadValue m2 p_drop =
        .ok (.construct Names.«Lists::Node<&Ixon::Expr>» "Cons" [x_s, w_tail]))
      (ld_nodes : loadValue m2 x_nodes =
        .ok (.construct Names.«Lists::Node<Ixon::BinderNode>» "Cons" [x_node, x_n1]))
      (hnode : x_node = .construct "Ixon::BinderNode" "Share" [x_variant])
      (ev_vf : ObsFn W "UInt64::to_field" [x_variant] m2 v_var m3 cs3)
      (ev_bn : ObsFn W "Convert::binder_nodes" [x_tbl, .field 1, x_n, v_var] m3 x_enodes m4 cs4)
      (ev_cb : ObsFn W "Convert::convert_block"
        [x_s, x_sharing, x_n, x_refs, x_recur_addrs, x_univs, x_tbl, x_enodes] m4 x_k m5 cs5)
      (hr : r = .tuple [x_k, x_n1])
      (hh' : h' = m5)
      (hcs : calls =
        (⟨"UInt64::to_field", [x_idx], h⟩ : Call F) :: cs1 ++
        ((⟨Names.«Lists::drop<&Ixon::Expr>», [x_sharing, x_n], m1⟩ : Call F) :: cs2) ++
        ((⟨"UInt64::to_field", [x_variant], m2⟩ : Call F) :: cs3) ++
        ((⟨"Convert::binder_nodes", [x_tbl, .field 1, x_n, v_var], m3⟩ : Call F) :: cs4) ++
        ((⟨"Convert::convert_block",
            [x_s, x_sharing, x_n, x_refs, x_recur_addrs, x_univs, x_tbl, x_enodes], m4⟩ :
            Call F) :: cs5))

section AnnotObsMacros

local macro "ca_var" d:ident : tactic =>
  `(tactic| (obtain ⟨l_v, rfl, rfl⟩ := $d.var_inv; simp at l_v; subst l_v))

local macro "ca_arg_var" a:ident a':ident : tactic =>
  `(tactic| (
    obtain ⟨_, _, _, _, _, rfl, d_av, $a', rfl⟩ := $a.cons_inv
    ca_var d_av))

local macro "ca_tuple2_pat" mt:ident x:ident y:ident : tactic =>
  `(tactic| (
    obtain ⟨_, hv_t2, -, ml_t1⟩ := matchPattern_tuple_inv $mt
    subst hv_t2
    obtain ⟨$x, _, _, _, rfl, mt_t1, ml_t2, rfl⟩ := matchListWith_cons_inv ml_t1
    obtain rfl := matchPattern_bind_inv mt_t1
    obtain ⟨$y, _, _, _, rfl, mt_t2, ml_t3, rfl⟩ := matchListWith_cons_inv ml_t2
    obtain rfl := matchPattern_bind_inv mt_t2
    obtain ⟨rfl, rfl⟩ := matchListWith_nil_inv ml_t3))

local macro "ca_let_conv_expr" d:ident xk:ident xb:ident m:ident cs:ident ev:ident drest:ident : tactic =>
  `(tactic| (
    obtain ⟨_, $m, _, _, _, d_ce, mt_ce, $drest, rfl⟩ := $d.letValue_inv
    obtain ⟨_, _, _, $cs, a_ce0, $ev, rfl⟩ := d_ce.call_inv
    rw [instanceName_plain_some] at $ev
    ca_arg_var a_ce0 a_ce1
    ca_arg_var a_ce1 a_ce2
    ca_arg_var a_ce2 a_ce3
    ca_arg_var a_ce3 a_ce4
    ca_arg_var a_ce4 a_ce5
    ca_arg_var a_ce5 a_ce6
    obtain ⟨rfl, rfl, rfl⟩ := a_ce6.nil_inv
    ca_tuple2_pat mt_ce $xk $xb))

local macro "ca_let_annot_branch" d:ident xk2:ident xn:ident m:ident cs:ident br:ident drest:ident : tactic =>
  `(tactic| (
    obtain ⟨_, $m, _, $cs, _, d_ab, mt_ab, $drest, rfl⟩ := $d.letValue_inv
    ca_tuple2_pat mt_ab $xk2 $xn
    obtain ⟨_, _, _, _, _, _, d_sc, sel_ab, d_body_ab, rfl⟩ := d_ab.matchValue_inv
    ca_var d_sc
    have $br : AnnotBranch _ _ _ _ _ _ _ _ _ _ _ $xk2 $xn $m $cs := by
      rcases selectArm_cons_inv sel_ab with ⟨mt_ab0, rfl⟩ | ⟨nm_ab0, sel_ab1⟩
      · obtain ⟨hv_ab0, rfl⟩ := MatchesConst.some_inv (MatchesConst.literal 0) mt_ab0
        obtain ⟨_, a_ab0, heq_ab0⟩ := d_body_ab.tuple_inv
        ca_arg_var a_ab0 a_ab1
        ca_arg_var a_ab1 a_ab2
        obtain ⟨rfl, rfl, rfl⟩ := a_ab2.nil_inv
        simp only [Value.tuple.injEq, List.cons.injEq, and_true] at heq_ab0
        exact AnnotBranch.n0 hv_ab0 heq_ab0.1.symm heq_ab0.2.symm rfl rfl
      · have hne_ab0 := MatchesConst.none_inv (MatchesConst.literal 0) nm_ab0
        rcases selectArm_cons_inv sel_ab1 with ⟨mt_ab1, rfl⟩ | ⟨nm_ab1, _⟩
        · obtain rfl := matchPattern_wildcard_inv mt_ab1
          obtain ⟨_, _, _, cs_abr, a_abr0, ev_abr, rfl⟩ := d_body_ab.call_inv
          rw [instanceName_plain_some] at ev_abr
          ca_arg_var a_abr0 a_abr1
          ca_arg_var a_abr1 a_abr2
          ca_arg_var a_abr2 a_abr3
          ca_arg_var a_abr3 a_abr4
          ca_arg_var a_abr4 a_abr5
          ca_arg_var a_abr5 a_abr6
          ca_arg_var a_abr6 a_abr7
          ca_arg_var a_abr7 a_abr8
          obtain ⟨rfl, rfl, rfl⟩ := a_abr8.nil_inv
          exact AnnotBranch.other cs_abr hne_ab0 ev_abr
            (by simp only [List.nil_append])
        · exact (matchPattern_wildcard_none nm_ab1).elim))

set_option maxHeartbeats 40000000 in
/-- **Every observed derivation of `Convert::convert_annotated` takes one of its 6 paths.** -/
theorem convert_annotated_obs
    {x_e x_sharing x_bound x_refs x_recur_addrs x_univs x_tbl x_nodes : SourceValue F}
    {h h' : Heap F} {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "Convert::convert_annotated"
      [x_e, x_sharing, x_bound, x_refs, x_recur_addrs, x_univs, x_tbl, x_nodes] h r h' calls) :
    ConvertAnnotatedPath x_e x_sharing x_bound x_refs x_recur_addrs x_univs x_tbl x_nodes
      h r h' calls := by
  have d0 := ObsFn.function_inv (s := IxVM.source) IxVM.Convert.convert_annotated.lookup
    (by simp [IxVM.Convert.convert_annotated, ControlLower.hasControl]) ev
  simp only [IxVM.Convert.convert_annotated] at d0
  obtain ⟨v_scrut, m_scrut, bs_arm, body_arm, c_s1, c_s2, d_load, sel0, d_arm, rfl⟩ :=
    d0.matchValue_inv
  obtain ⟨p_e, d_evar, ld_e⟩ := d_load.load_inv
  ca_var d_evar
  -- Arm 1: App(f, a)
  rcases selectArm_cons_inv sel0 with ⟨mt0, rfl⟩ | ⟨_, sel1⟩
  · obtain ⟨_, hv0, -, ml0⟩ := matchPattern_construct_inv mt0
    rw [Names.n11871363439673646749] at hv0; subst hv0
    obtain ⟨x_f, _, _, _, rfl, mt0a, ml0b, rfl⟩ := matchListWith_cons_inv ml0
    obtain rfl := matchPattern_bind_inv mt0a
    obtain ⟨x_a, _, _, _, rfl, mt0b, ml0c, rfl⟩ := matchListWith_cons_inv ml0b
    obtain rfl := matchPattern_bind_inv mt0b
    obtain ⟨rfl, rfl⟩ := matchListWith_nil_inv ml0c
    ca_let_conv_expr d_arm x_kf x_bf m1 cs1 ev_f d1
    ca_let_conv_expr d1 x_ka x_ba m2 cs2 ev_a d2
    ca_let_annot_branch d2 x_kf2 x_n1 m3 cs3 br_f d3
    ca_let_annot_branch d3 x_ka2 x_n2 m4 cs4 br_a d4
    obtain ⟨_, a_ret0, rfl⟩ := d4.tuple_inv
    obtain ⟨_, _, _, _, _, rfl, d_st, a_ret1, rfl⟩ := a_ret0.cons_inv
    obtain ⟨_, _, d_con, rfl, hm_st⟩ := d_st.store_inv
    obtain ⟨_, a_con0, hcon⟩ := d_con.construct_inv
    rw [instanceName_plain_some] at hcon; subst hcon
    ca_arg_var a_con0 a_con1
    ca_arg_var a_con1 a_con2
    obtain ⟨rfl, rfl, rfl⟩ := a_con2.nil_inv
    ca_arg_var a_ret1 a_ret2
    obtain ⟨rfl, rfl, rfl⟩ := a_ret2.nil_inv
    exact ConvertAnnotatedPath.App x_f x_a x_kf x_bf x_ka x_ba x_kf2 x_n1 x_ka2 x_n2
      m1 m2 m3 m4 cs1 cs2 cs3 cs4 ld_e ev_f ev_a br_f br_a rfl hm_st
      (by simp only [List.append_assoc, List.cons_append, List.nil_append, List.append_nil])
  -- Arm 2: Lam(ty, body)
  rcases selectArm_cons_inv sel1 with ⟨mt1, rfl⟩ | ⟨_, sel2⟩
  · obtain ⟨_, hv1, -, ml1⟩ := matchPattern_construct_inv mt1
    rw [Names.n11871363439673646749] at hv1; subst hv1
    obtain ⟨x_ty, _, _, _, rfl, mt1a, ml1b, rfl⟩ := matchListWith_cons_inv ml1
    obtain rfl := matchPattern_bind_inv mt1a
    obtain ⟨x_body, _, _, _, rfl, mt1b, ml1c, rfl⟩ := matchListWith_cons_inv ml1b
    obtain rfl := matchPattern_bind_inv mt1b
    obtain ⟨rfl, rfl⟩ := matchListWith_nil_inv ml1c
    obtain ⟨_, _, _, _, _, d_ldn, mt_nd, d1, rfl⟩ := d_arm.letValue_inv
    obtain ⟨_, d_nvar, ld_nodes⟩ := d_ldn.load_inv
    ca_var d_nvar
    obtain ⟨_, hv_nd, -, ml_nd0⟩ := matchPattern_construct_inv mt_nd
    rw [Names.n5527369450665788998] at hv_nd; subst hv_nd
    obtain ⟨x_node, _, _, _, rfl, mt_nda, ml_nd1, rfl⟩ := matchListWith_cons_inv ml_nd0
    obtain rfl := matchPattern_bind_inv mt_nda
    obtain ⟨x_n0, _, _, _, rfl, mt_ndb, ml_nd2, rfl⟩ := matchListWith_cons_inv ml_nd1
    obtain rfl := matchPattern_bind_inv mt_ndb
    obtain ⟨rfl, rfl⟩ := matchListWith_nil_inv ml_nd2
    obtain ⟨x_l, m1, _, _, _, d_bl, mt_bl, d2, rfl⟩ := d1.letValue_inv
    obtain ⟨_, _, _, cs1, a_bl0, ev_l, rfl⟩ := d_bl.call_inv
    rw [instanceName_plain_some] at ev_l
    ca_arg_var a_bl0 a_bl1
    obtain ⟨rfl, rfl, rfl⟩ := a_bl1.nil_inv
    obtain rfl := matchPattern_bind_inv mt_bl
    ca_let_conv_expr d2 x_kt x_bt m2 cs2 ev_t d3
    ca_let_conv_expr d3 x_kb x_bb m3 cs3 ev_b d4
    ca_let_annot_branch d4 x_kt2 x_n1 m4 cs4 br_t d5
    ca_let_annot_branch d5 x_kb2 x_n2 m5 cs5 br_b d6
    obtain ⟨_, a_ret0, rfl⟩ := d6.tuple_inv
    obtain ⟨_, _, _, _, _, rfl, d_st, a_ret1, rfl⟩ := a_ret0.cons_inv
    obtain ⟨_, _, d_con, rfl, hm_st⟩ := d_st.store_inv
    obtain ⟨_, a_con0, hcon⟩ := d_con.construct_inv
    rw [instanceName_plain_some] at hcon; subst hcon
    ca_arg_var a_con0 a_con1
    ca_arg_var a_con1 a_con2
    ca_arg_var a_con2 a_con3
    obtain ⟨rfl, rfl, rfl⟩ := a_con3.nil_inv
    ca_arg_var a_ret1 a_ret2
    obtain ⟨rfl, rfl, rfl⟩ := a_ret2.nil_inv
    exact ConvertAnnotatedPath.Lam x_ty x_body x_node x_n0 x_l x_kt x_bt x_kb x_bb
      x_kt2 x_n1 x_kb2 x_n2 m1 m2 m3 m4 m5 cs1 cs2 cs3 cs4 cs5
      ld_e ld_nodes ev_l ev_t ev_b br_t br_b rfl hm_st
      (by simp only [List.append_assoc, List.cons_append, List.nil_append, List.append_nil])
  -- Arm 3: All(ty, body)
  rcases selectArm_cons_inv sel2 with ⟨mt2, rfl⟩ | ⟨_, sel3⟩
  · obtain ⟨_, hv2, -, ml2⟩ := matchPattern_construct_inv mt2
    rw [Names.n11871363439673646749] at hv2; subst hv2
    obtain ⟨x_ty, _, _, _, rfl, mt2a, ml2b, rfl⟩ := matchListWith_cons_inv ml2
    obtain rfl := matchPattern_bind_inv mt2a
    obtain ⟨x_body, _, _, _, rfl, mt2b, ml2c, rfl⟩ := matchListWith_cons_inv ml2b
    obtain rfl := matchPattern_bind_inv mt2b
    obtain ⟨rfl, rfl⟩ := matchListWith_nil_inv ml2c
    obtain ⟨_, _, _, _, _, d_ldn, mt_nd, d1, rfl⟩ := d_arm.letValue_inv
    obtain ⟨_, d_nvar, ld_nodes⟩ := d_ldn.load_inv
    ca_var d_nvar
    obtain ⟨_, hv_nd, -, ml_nd0⟩ := matchPattern_construct_inv mt_nd
    rw [Names.n5527369450665788998] at hv_nd; subst hv_nd
    obtain ⟨x_node, _, _, _, rfl, mt_nda, ml_nd1, rfl⟩ := matchListWith_cons_inv ml_nd0
    obtain rfl := matchPattern_bind_inv mt_nda
    obtain ⟨x_n0, _, _, _, rfl, mt_ndb, ml_nd2, rfl⟩ := matchListWith_cons_inv ml_nd1
    obtain rfl := matchPattern_bind_inv mt_ndb
    obtain ⟨rfl, rfl⟩ := matchListWith_nil_inv ml_nd2
    obtain ⟨x_l, m1, _, _, _, d_bl, mt_bl, d2, rfl⟩ := d1.letValue_inv
    obtain ⟨_, _, _, cs1, a_bl0, ev_l, rfl⟩ := d_bl.call_inv
    rw [instanceName_plain_some] at ev_l
    ca_arg_var a_bl0 a_bl1
    obtain ⟨rfl, rfl, rfl⟩ := a_bl1.nil_inv
    obtain rfl := matchPattern_bind_inv mt_bl
    ca_let_conv_expr d2 x_kt x_bt m2 cs2 ev_t d3
    ca_let_conv_expr d3 x_kb x_bb m3 cs3 ev_b d4
    ca_let_annot_branch d4 x_kt2 x_n1 m4 cs4 br_t d5
    ca_let_annot_branch d5 x_kb2 x_n2 m5 cs5 br_b d6
    obtain ⟨_, a_ret0, rfl⟩ := d6.tuple_inv
    obtain ⟨_, _, _, _, _, rfl, d_st, a_ret1, rfl⟩ := a_ret0.cons_inv
    obtain ⟨_, _, d_con, rfl, hm_st⟩ := d_st.store_inv
    obtain ⟨_, a_con0, hcon⟩ := d_con.construct_inv
    rw [instanceName_plain_some] at hcon; subst hcon
    ca_arg_var a_con0 a_con1
    ca_arg_var a_con1 a_con2
    ca_arg_var a_con2 a_con3
    obtain ⟨rfl, rfl, rfl⟩ := a_con3.nil_inv
    ca_arg_var a_ret1 a_ret2
    obtain ⟨rfl, rfl, rfl⟩ := a_ret2.nil_inv
    exact ConvertAnnotatedPath.All x_ty x_body x_node x_n0 x_l x_kt x_bt x_kb x_bb
      x_kt2 x_n1 x_kb2 x_n2 m1 m2 m3 m4 m5 cs1 cs2 cs3 cs4 cs5
      ld_e ld_nodes ev_l ev_t ev_b br_t br_b rfl hm_st
      (by simp only [List.append_assoc, List.cons_append, List.nil_append, List.append_nil])
  -- Arm 4: Let(_, ty, val, body)
  rcases selectArm_cons_inv sel3 with ⟨mt3, rfl⟩ | ⟨_, sel4⟩
  · obtain ⟨_, hv3, -, ml3⟩ := matchPattern_construct_inv mt3
    rw [Names.n11871363439673646749] at hv3; subst hv3
    obtain ⟨w_hdr, _, _, _, rfl, mt3a, ml3b, rfl⟩ := matchListWith_cons_inv ml3
    obtain rfl := matchPattern_wildcard_inv mt3a
    obtain ⟨x_ty, _, _, _, rfl, mt3b, ml3c, rfl⟩ := matchListWith_cons_inv ml3b
    obtain rfl := matchPattern_bind_inv mt3b
    obtain ⟨x_val, _, _, _, rfl, mt3c, ml3d, rfl⟩ := matchListWith_cons_inv ml3c
    obtain rfl := matchPattern_bind_inv mt3c
    obtain ⟨x_body, _, _, _, rfl, mt3d, ml3e, rfl⟩ := matchListWith_cons_inv ml3d
    obtain rfl := matchPattern_bind_inv mt3d
    obtain ⟨rfl, rfl⟩ := matchListWith_nil_inv ml3e
    ca_let_conv_expr d_arm x_kt x_bt m1 cs1 ev_t d1
    ca_let_conv_expr d1 x_kv x_bv m2 cs2 ev_v d2
    ca_let_conv_expr d2 x_kb x_bb m3 cs3 ev_b d3
    ca_let_annot_branch d3 x_kt2 x_n1 m4 cs4 br_t d4
    ca_let_annot_branch d4 x_kv2 x_n2 m5 cs5 br_v d5
    ca_let_annot_branch d5 x_kb2 x_n3 m6 cs6 br_b d6
    obtain ⟨_, a_ret0, rfl⟩ := d6.tuple_inv
    obtain ⟨_, _, _, _, _, rfl, d_st, a_ret1, rfl⟩ := a_ret0.cons_inv
    obtain ⟨_, _, d_con, rfl, hm_st⟩ := d_st.store_inv
    obtain ⟨_, a_con0, hcon⟩ := d_con.construct_inv
    rw [instanceName_plain_some] at hcon; subst hcon
    ca_arg_var a_con0 a_con1
    ca_arg_var a_con1 a_con2
    ca_arg_var a_con2 a_con3
    obtain ⟨rfl, rfl, rfl⟩ := a_con3.nil_inv
    ca_arg_var a_ret1 a_ret2
    obtain ⟨rfl, rfl, rfl⟩ := a_ret2.nil_inv
    exact ConvertAnnotatedPath.Let w_hdr x_ty x_val x_body x_kt x_bt x_kv x_bv x_kb x_bb
      x_kt2 x_n1 x_kv2 x_n2 x_kb2 x_n3 m1 m2 m3 m4 m5 m6 cs1 cs2 cs3 cs4 cs5 cs6
      ld_e ev_t ev_v ev_b br_t br_v br_b rfl hm_st
      (by simp only [List.append_assoc, List.cons_append, List.nil_append, List.append_nil])
  -- Arm 5: Prj(type_ref_idx, field_idx, inner)
  rcases selectArm_cons_inv sel4 with ⟨mt4, rfl⟩ | ⟨_, sel5⟩
  · obtain ⟨_, hv4, -, ml4⟩ := matchPattern_construct_inv mt4
    rw [Names.n11871363439673646749] at hv4; subst hv4
    obtain ⟨x_tidx, _, _, _, rfl, mt4a, ml4b, rfl⟩ := matchListWith_cons_inv ml4
    obtain rfl := matchPattern_bind_inv mt4a
    obtain ⟨x_fidx, _, _, _, rfl, mt4b, ml4c, rfl⟩ := matchListWith_cons_inv ml4b
    obtain rfl := matchPattern_bind_inv mt4b
    obtain ⟨x_inner, _, _, _, rfl, mt4c, ml4d, rfl⟩ := matchListWith_cons_inv ml4c
    obtain rfl := matchPattern_bind_inv mt4c
    obtain ⟨rfl, rfl⟩ := matchListWith_nil_inv ml4d
    -- `let type_addr = Lists::lookup(refs, UInt64::to_field(type_ref_idx));`
    obtain ⟨x_taddr, m2, _, _, _, d_lk, mt_lk, d1, rfl⟩ := d_arm.letValue_inv
    obtain ⟨_, _, _, cs2, a_lk0, ev_lk, rfl⟩ := d_lk.call_inv
    rw [Names.n16119986092388975791] at ev_lk
    ca_arg_var a_lk0 a_lk1
    obtain ⟨v_tidx, _, m1, _, _, rfl, d_tf, a_lk2, rfl⟩ := a_lk1.cons_inv
    obtain ⟨_, _, _, cs1, a_tf0, ev_tf, rfl⟩ := d_tf.call_inv
    rw [instanceName_plain_some] at ev_tf
    ca_arg_var a_tf0 a_tf1
    obtain ⟨rfl, rfl, rfl⟩ := a_tf1.nil_inv
    obtain ⟨rfl, rfl, rfl⟩ := a_lk2.nil_inv
    obtain rfl := matchPattern_bind_inv mt_lk
    -- `let (ki, n1) = convert_annotated(inner, ...)`
    obtain ⟨_, m3, _, _, _, d_ca, mt_ca, d2, rfl⟩ := d1.letValue_inv
    obtain ⟨_, _, _, cs3, a_ca0, ev_in, rfl⟩ := d_ca.call_inv
    rw [instanceName_plain_some] at ev_in
    ca_arg_var a_ca0 a_ca1
    ca_arg_var a_ca1 a_ca2
    ca_arg_var a_ca2 a_ca3
    ca_arg_var a_ca3 a_ca4
    ca_arg_var a_ca4 a_ca5
    ca_arg_var a_ca5 a_ca6
    ca_arg_var a_ca6 a_ca7
    ca_arg_var a_ca7 a_ca8
    obtain ⟨rfl, rfl, rfl⟩ := a_ca8.nil_inv
    ca_tuple2_pat mt_ca x_ki x_n1
    -- `((&(KernelTypes::KExprNode::Proj(type_addr, UInt64::to_field(field_idx), ki))), n1)`
    obtain ⟨_, a_ret0, rfl⟩ := d2.tuple_inv
    obtain ⟨_, _, _, _, _, rfl, d_st, a_ret1, rfl⟩ := a_ret0.cons_inv
    obtain ⟨_, _, d_con, rfl, hm_st⟩ := d_st.store_inv
    obtain ⟨_, a_con0, hcon⟩ := d_con.construct_inv
    rw [instanceName_plain_some] at hcon; subst hcon
    ca_arg_var a_con0 a_con1
    obtain ⟨v_fidx, _, m4, _, _, rfl, d_ff, a_con2, rfl⟩ := a_con1.cons_inv
    obtain ⟨_, _, _, cs4, a_ff0, ev_ff, rfl⟩ := d_ff.call_inv
    rw [instanceName_plain_some] at ev_ff
    ca_arg_var a_ff0 a_ff1
    obtain ⟨rfl, rfl, rfl⟩ := a_ff1.nil_inv
    ca_arg_var a_con2 a_con3
    obtain ⟨rfl, rfl, rfl⟩ := a_con3.nil_inv
    ca_arg_var a_ret1 a_ret2
    obtain ⟨rfl, rfl, rfl⟩ := a_ret2.nil_inv
    exact ConvertAnnotatedPath.Prj x_tidx x_fidx x_inner v_tidx x_taddr x_ki x_n1 v_fidx
      m1 m2 m3 m4 cs1 cs2 cs3 cs4 ld_e ev_tf ev_lk ev_in ev_ff rfl hm_st
      (by simp only [List.append_assoc, List.cons_append, List.nil_append, List.append_nil,
        instanceName_plain_some, Names.n16119986092388975791])
  -- Arm 6: Share(idx)
  rcases selectArm_cons_inv sel5 with ⟨mt5, rfl⟩ | ⟨_, sel6⟩
  · obtain ⟨_, hv5, -, ml5⟩ := matchPattern_construct_inv mt5
    rw [Names.n11871363439673646749] at hv5; subst hv5
    obtain ⟨x_idx, _, _, _, rfl, mt5a, ml5b, rfl⟩ := matchListWith_cons_inv ml5
    obtain rfl := matchPattern_bind_inv mt5a
    obtain ⟨rfl, rfl⟩ := matchListWith_nil_inv ml5b
    -- `let n = UInt64::to_field(idx);`
    obtain ⟨x_n, m1, _, _, _, d_nf, mt_nf, d1, rfl⟩ := d_arm.letValue_inv
    obtain ⟨_, _, _, cs1, a_nf0, ev_nf, rfl⟩ := d_nf.call_inv
    rw [instanceName_plain_some] at ev_nf
    ca_arg_var a_nf0 a_nf1
    obtain ⟨rfl, rfl, rfl⟩ := a_nf1.nil_inv
    obtain rfl := matchPattern_bind_inv mt_nf
    -- `let Lists::Node::Cons(s, _) = (*(Lists::drop(sharing, n)));`
    obtain ⟨_, m2, _, _, _, d_ldd, mt_dr, d2, rfl⟩ := d1.letValue_inv
    obtain ⟨p_drop, d_dr, ld_dr⟩ := d_ldd.load_inv
    obtain ⟨_, _, _, cs2, a_dr0, ev_dr, rfl⟩ := d_dr.call_inv
    rw [Names.n10967839274657083673] at ev_dr
    ca_arg_var a_dr0 a_dr1
    ca_arg_var a_dr1 a_dr2
    obtain ⟨rfl, rfl, rfl⟩ := a_dr2.nil_inv
    obtain ⟨_, hv_dr, -, ml_dr0⟩ := matchPattern_construct_inv mt_dr
    rw [Names.n16338221799578455114] at hv_dr; subst hv_dr
    obtain ⟨x_s, _, _, _, rfl, mt_dra, ml_dr1, rfl⟩ := matchListWith_cons_inv ml_dr0
    obtain rfl := matchPattern_bind_inv mt_dra
    obtain ⟨w_tail, _, _, _, rfl, mt_drb, ml_dr2, rfl⟩ := matchListWith_cons_inv ml_dr1
    obtain rfl := matchPattern_wildcard_inv mt_drb
    obtain ⟨rfl, rfl⟩ := matchListWith_nil_inv ml_dr2
    -- `let Lists::Node::Cons(node, n1) = (*(nodes));`
    obtain ⟨_, _, _, _, _, d_ldn, mt_nd, d3, rfl⟩ := d2.letValue_inv
    obtain ⟨_, d_nvar, ld_nodes⟩ := d_ldn.load_inv
    ca_var d_nvar
    obtain ⟨_, hv_nd, -, ml_nd0⟩ := matchPattern_construct_inv mt_nd
    rw [Names.n5527369450665788998] at hv_nd; subst hv_nd
    obtain ⟨x_node, _, _, _, rfl, mt_nda, ml_nd1, rfl⟩ := matchListWith_cons_inv ml_nd0
    obtain rfl := matchPattern_bind_inv mt_nda
    obtain ⟨x_n1, _, _, _, rfl, mt_ndb, ml_nd2, rfl⟩ := matchListWith_cons_inv ml_nd1
    obtain rfl := matchPattern_bind_inv mt_ndb
    obtain ⟨rfl, rfl⟩ := matchListWith_nil_inv ml_nd2
    -- `let Ixon::BinderNode::Share(variant) = node;`
    obtain ⟨_, _, _, _, _, d_ndv, mt_sh, d4, rfl⟩ := d3.letValue_inv
    ca_var d_ndv
    obtain ⟨_, hv_sh, -, ml_sh0⟩ := matchPattern_construct_inv mt_sh
    rw [Names.n7516136566660357059] at hv_sh
    obtain ⟨x_variant, _, _, _, rfl, mt_sha, ml_sh1, rfl⟩ := matchListWith_cons_inv ml_sh0
    obtain rfl := matchPattern_bind_inv mt_sha
    obtain ⟨rfl, rfl⟩ := matchListWith_nil_inv ml_sh1
    -- `let entry_nodes = binder_nodes(tbl, 1, n, UInt64::to_field(variant));`
    obtain ⟨x_enodes, m4, _, _, _, d_bn, mt_bn, d5, rfl⟩ := d4.letValue_inv
    obtain ⟨_, _, _, cs4, a_bn0, ev_bn, rfl⟩ := d_bn.call_inv
    rw [instanceName_plain_some] at ev_bn
    ca_arg_var a_bn0 a_bn1
    obtain ⟨_, _, _, _, _, rfl, d_lit1, a_bn2, rfl⟩ := a_bn1.cons_inv
    obtain ⟨rfl, rfl, rfl⟩ := d_lit1.literal_inv
    ca_arg_var a_bn2 a_bn3
    obtain ⟨v_var, _, m3, _, _, rfl, d_vf, a_bn4, rfl⟩ := a_bn3.cons_inv
    obtain ⟨_, _, _, cs3, a_vf0, ev_vf, rfl⟩ := d_vf.call_inv
    rw [instanceName_plain_some] at ev_vf
    ca_arg_var a_vf0 a_vf1
    obtain ⟨rfl, rfl, rfl⟩ := a_vf1.nil_inv
    obtain ⟨rfl, rfl, rfl⟩ := a_bn4.nil_inv
    obtain rfl := matchPattern_bind_inv mt_bn
    -- `(convert_block(s, sharing, n, refs, recur_addrs, univs, tbl, entry_nodes), n1)`
    obtain ⟨_, a_ret0, rfl⟩ := d5.tuple_inv
    obtain ⟨x_k, _, m5, _, _, rfl, d_cb, a_ret1, rfl⟩ := a_ret0.cons_inv
    obtain ⟨_, _, _, cs5, a_cb0, ev_cb, rfl⟩ := d_cb.call_inv
    rw [instanceName_plain_some] at ev_cb
    ca_arg_var a_cb0 a_cb1
    ca_arg_var a_cb1 a_cb2
    ca_arg_var a_cb2 a_cb3
    ca_arg_var a_cb3 a_cb4
    ca_arg_var a_cb4 a_cb5
    ca_arg_var a_cb5 a_cb6
    ca_arg_var a_cb6 a_cb7
    ca_arg_var a_cb7 a_cb8
    obtain ⟨rfl, rfl, rfl⟩ := a_cb8.nil_inv
    ca_arg_var a_ret1 a_ret2
    obtain ⟨rfl, rfl, rfl⟩ := a_ret2.nil_inv
    exact ConvertAnnotatedPath.Share x_idx x_n p_drop x_s w_tail x_node x_n1 x_variant v_var
      x_enodes x_k m1 m2 m3 m4 m5 cs1 cs2 cs3 cs4 cs5
      ld_e ev_nf ev_dr ld_dr ld_nodes hv_sh ev_vf ev_bn ev_cb rfl rfl
      (by simp only [List.append_assoc, List.cons_append, List.nil_append, List.append_nil,
        instanceName_plain_some, Names.n10967839274657083673])
  · exact (selectArm_nil_inv sel6).elim

end AnnotObsMacros

/-! ## `HashedPairs`, `PreShareOk`, and `RawConvExpr` -/

/-- Every `(addr, bytes)` pair in `pairs` was hashed in `cs` and hashes to `addr`. -/
def HashedPairs (cs : List (Call F)) (pairs : List (_root_.Address × ByteArray)) : Prop :=
  ∀ p ∈ pairs, Hashed cs p.2 ∧ Address.blake3Pure p.2 = p.1

theorem HashedPairs.nil {cs : List (Call F)} : HashedPairs cs [] :=
  fun _ hp => nomatch hp

theorem HashedPairs.sub {cs₁ cs₂ : List (Call F)} {pairs : List (_root_.Address × ByteArray)}
    (hsub : ∀ c ∈ cs₁, c ∈ cs₂) (hp : HashedPairs cs₁ pairs) : HashedPairs cs₂ pairs := by
  intro p hmem
  obtain ⟨⟨cl, hcl, rest⟩, haddr⟩ := hp p hmem
  exact ⟨⟨cl, hsub cl hcl, rest⟩, haddr⟩

theorem HashedPairs.append {cs : List (Call F)} {p₁ p₂ : List (_root_.Address × ByteArray)}
    (h₁ : HashedPairs cs p₁) (h₂ : HashedPairs cs p₂) : HashedPairs cs (p₁ ++ p₂) := by
  intro p hp
  rcases List.mem_append.mp hp with hm | hm
  · exact h₁ p hm
  · exact h₂ p hm

/-- Sharing-index bound established by `Convert::convert_expr` on every expression before entering
binders (`Lam`/`All`), ensuring every reachable `.share idx` outside `Lam`/`All` has
`idx.toNat < bound` and recursively satisfies `PreShareOk` at `idx.toNat`. -/
inductive PreShareOk (sharing : List Ixon.Expr) : Nat → Ixon.Expr → Prop where
  | var {b i} : PreShareOk sharing b (.var i)
  | sort {b i} : PreShareOk sharing b (.sort i)
  | ref {b i us} : PreShareOk sharing b (.ref i us)
  | recur {b i us} : PreShareOk sharing b (.recur i us)
  | str {b i} : PreShareOk sharing b (.str i)
  | nat {b i} : PreShareOk sharing b (.nat i)
  | lam {b ty body} : PreShareOk sharing b (.lam ty body)
  | all {b ty body} : PreShareOk sharing b (.all ty body)
  | prj {b t f inner} : PreShareOk sharing b inner → PreShareOk sharing b (.prj t f inner)
  | app {b f a} : PreShareOk sharing b f → PreShareOk sharing b a → PreShareOk sharing b (.app f a)
  | letE {b nd md ty val body} :
      PreShareOk sharing b ty → PreShareOk sharing b val → PreShareOk sharing b body →
      PreShareOk sharing b (.letE nd md ty val body)
  | share {b idx s} :
      idx.toNat < b → sharing[idx.toNat]? = some s → PreShareOk sharing idx.toNat s →
      PreShareOk sharing b (.share idx)

/-- Unconditional raw heap relation produced by `Convert` on an `Ixon.Expr` at sharing bound
`bound`, recording all loaded literal blobs in `blobs`. -/
inductive RawConvExpr (refs recurAddrs : List _root_.Address) (univs : List Ixon.Univ)
    (sharing : List Ixon.Expr) (blobs : List (_root_.Address × ByteArray)) (h : Heap F) :
    Nat → Ixon.Expr → SourceValue F → Prop where
  | var {bound addr : Nat} {idx : UInt64}
      (hidx : idx.toNat < 72057594037927936)
      (cell : h[addr]? = some (.construct Core.kexprEnum "BVar" [.field (idx.toNat : F)])) :
      RawConvExpr refs recurAddrs univs sharing blobs h bound (.var idx)
        (.ptr (.enum Core.kexprEnum) addr)
  | sort {bound addr : Nat} {uIdx : UInt64} {u : Ixon.Univ} {lp : SourceValue F}
      (huIdx : uIdx.toNat < 72057594037927936)
      (hu : univs[uIdx.toNat]? = some u)
      (rl : RawKLevel h (Ix.Kernel.Reader.convUniv id u) lp)
      (cell : h[addr]? = some (.construct Core.kexprEnum "Srt" [lp])) :
      RawConvExpr refs recurAddrs univs sharing blobs h bound (.sort uIdx)
        (.ptr (.enum Core.kexprEnum) addr)
  | ref {bound addr : Nat} {rIdx : UInt64} {uIdxs : Array UInt64}
      {a : _root_.Address} {d : Bytes.Address} {ap lsp : SourceValue F} {ls : List Core.KLevel}
      (hrIdx : rIdx.toNat < 72057594037927936)
      (href : refs[rIdx.toNat]? = some a)
      (hd : Core.ixAddr d = a)
      (ra : Bytes.RepAddressRef Core.addrTy h d ap)
      (hls : uIdxs.toList.mapM (fun i => univs[i.toNat]?.map (Ix.Kernel.Reader.convUniv id)) =
        some ls)
      (rls : RawKLevelList h ls lsp)
      (cell : h[addr]? = some (.construct Core.kexprEnum "Const" [ap, lsp])) :
      RawConvExpr refs recurAddrs univs sharing blobs h bound (.ref rIdx uIdxs)
        (.ptr (.enum Core.kexprEnum) addr)
  | recur {bound addr : Nat} {rIdx : UInt64} {uIdxs : Array UInt64}
      {a : _root_.Address} {d : Bytes.Address} {ap lsp : SourceValue F} {ls : List Core.KLevel}
      (hrIdx : rIdx.toNat < 72057594037927936)
      (hrec : recurAddrs[rIdx.toNat]? = some a)
      (hd : Core.ixAddr d = a)
      (ra : Bytes.RepAddressRef Core.addrTy h d ap)
      (hls : uIdxs.toList.mapM (fun i => univs[i.toNat]?.map (Ix.Kernel.Reader.convUniv id)) =
        some ls)
      (rls : RawKLevelList h ls lsp)
      (cell : h[addr]? = some (.construct Core.kexprEnum "Const" [ap, lsp])) :
      RawConvExpr refs recurAddrs univs sharing blobs h bound (.recur rIdx uIdxs)
        (.ptr (.enum Core.kexprEnum) addr)
  | prj {bound addr : Nat} {tIdx fIdx : UInt64} {inner : Ixon.Expr}
      {a : _root_.Address} {d : Bytes.Address} {ap ip : SourceValue F}
      (htIdx : tIdx.toNat < 72057594037927936)
      (hfIdx : fIdx.toNat < 72057594037927936)
      (href : refs[tIdx.toNat]? = some a)
      (hd : Core.ixAddr d = a)
      (ra : Bytes.RepAddressRef Core.addrTy h d ap)
      (rin : RawConvExpr refs recurAddrs univs sharing blobs h bound inner ip)
      (cell : h[addr]? = some (.construct Core.kexprEnum "Proj"
        [ap, .field (fIdx.toNat : F), ip])) :
      RawConvExpr refs recurAddrs univs sharing blobs h bound (.prj tIdx fIdx inner)
        (.ptr (.enum Core.kexprEnum) addr)
  | str {bound addr : Nat} {bIdx : UInt64} {a : _root_.Address}
      {bs : List UInt8} {s : String} {bp : SourceValue F}
      (hbIdx : bIdx.toNat < 72057594037927936)
      (href : refs[bIdx.toNat]? = some a)
      (hmem : (a, ⟨bs.toArray⟩) ∈ blobs)
      (rbs : Bytes.RepByteStream Core.byteListEnum h bs bp)
      (hs : Core.StrBytes s bs)
      (cell : h[addr]? =
        some (.construct Core.kexprEnum "Lit" [.construct Core.klitEnum "Str" [bp]])) :
      RawConvExpr refs recurAddrs univs sharing blobs h bound (.str bIdx)
        (.ptr (.enum Core.kexprEnum) addr)
  | nat {bound addr : Nat} {bIdx : UInt64} {a : _root_.Address}
      {bs : List UInt8} {limbs : List UInt64} {lp : SourceValue F}
      (hbIdx : bIdx.toNat < 72057594037927936)
      (href : refs[bIdx.toNat]? = some a)
      (hmem : (a, ⟨bs.toArray⟩) ∈ blobs)
      (hcanon : Ix.Kernel.Reader.canonicalNatural ⟨bs.toArray⟩ = true)
      (rlimbs : RepList Core.limbListEnum RepU64 h limbs lp)
      (hlast : limbs.getLast? ≠ some 0)
      (hval : Core.limbsVal limbs = Ix.Kernel.Reader.natural ⟨bs.toArray⟩)
      (cell : h[addr]? =
        some (.construct Core.kexprEnum "Lit" [.construct Core.klitEnum "Nat" [lp]])) :
      RawConvExpr refs recurAddrs univs sharing blobs h bound (.nat bIdx)
        (.ptr (.enum Core.kexprEnum) addr)
  | app {bound addr : Nat} {f arg : Ixon.Expr} {fp ap : SourceValue F}
      (rf : RawConvExpr refs recurAddrs univs sharing blobs h bound f fp)
      (ra : RawConvExpr refs recurAddrs univs sharing blobs h bound arg ap)
      (cell : h[addr]? = some (.construct Core.kexprEnum "App" [fp, ap])) :
      RawConvExpr refs recurAddrs univs sharing blobs h bound (.app f arg)
        (.ptr (.enum Core.kexprEnum) addr)
  | lam {bound addr : Nat} {ty body : Ixon.Expr} {tp bp lp : SourceValue F} {ℓ : Core.KLevel}
      (rl : KernelLevels.RepKLevel h ℓ lp)
      (rt : RawConvExpr refs recurAddrs univs sharing blobs h bound ty tp)
      (rb : RawConvExpr refs recurAddrs univs sharing blobs h bound body bp)
      (cell : h[addr]? = some (.construct Core.kexprEnum "Lam" [tp, bp, lp])) :
      RawConvExpr refs recurAddrs univs sharing blobs h bound (.lam ty body)
        (.ptr (.enum Core.kexprEnum) addr)
  | all {bound addr : Nat} {ty body : Ixon.Expr} {tp bp lp : SourceValue F} {ℓ : Core.KLevel}
      (rl : KernelLevels.RepKLevel h ℓ lp)
      (rt : RawConvExpr refs recurAddrs univs sharing blobs h bound ty tp)
      (rb : RawConvExpr refs recurAddrs univs sharing blobs h bound body bp)
      (cell : h[addr]? = some (.construct Core.kexprEnum "Forall" [tp, bp, lp])) :
      RawConvExpr refs recurAddrs univs sharing blobs h bound (.all ty body)
        (.ptr (.enum Core.kexprEnum) addr)
  | letE {bound addr : Nat} {nd : Bool} {md : Ixon.LetMode} {ty val body : Ixon.Expr}
      {tp vp bp : SourceValue F}
      (rt : RawConvExpr refs recurAddrs univs sharing blobs h bound ty tp)
      (rv : RawConvExpr refs recurAddrs univs sharing blobs h bound val vp)
      (rb : RawConvExpr refs recurAddrs univs sharing blobs h bound body bp)
      (cell : h[addr]? = some (.construct Core.kexprEnum "Let" [tp, vp, bp])) :
      RawConvExpr refs recurAddrs univs sharing blobs h bound (.letE nd md ty val body)
        (.ptr (.enum Core.kexprEnum) addr)
  | share {bound : Nat} {idx : UInt64} {s : Ixon.Expr} {kp : SourceValue F}
      (hidx : idx.toNat < bound)
      (hsh : sharing[idx.toNat]? = some s)
      (rs : RawConvExpr refs recurAddrs univs sharing blobs h idx.toNat s kp) :
      RawConvExpr refs recurAddrs univs sharing blobs h bound (.share idx) kp

theorem RawConvExpr.mono {refs recurAddrs : List _root_.Address} {univs : List Ixon.Univ}
    {sharing : List Ixon.Expr} {blobs₁ blobs₂ : List (_root_.Address × ByteArray)}
    {h₁ h₂ : Heap F} {bound : Nat} {e : Ixon.Expr} {kp : SourceValue F}
    (ext : Heap.Extends h₁ h₂)
    (hsub : ∀ p ∈ blobs₁, p ∈ blobs₂)
    (raw : RawConvExpr refs recurAddrs univs sharing blobs₁ h₁ bound e kp) :
    RawConvExpr refs recurAddrs univs sharing blobs₂ h₂ bound e kp := by
  induction raw with
  | var hidx cell => exact .var hidx (ext.getElem?_eq cell)
  | sort huIdx hu rl cell => exact .sort huIdx hu (rl.mono ext) (ext.getElem?_eq cell)
  | ref hrIdx href hd ra hls rls cell =>
    exact .ref hrIdx href hd (Bytes.repAddressRef_heapMono₂ _ ext ra) hls (rls.mono ext)
      (ext.getElem?_eq cell)
  | recur hrIdx hrec hd ra hls rls cell =>
    exact .recur hrIdx hrec hd (Bytes.repAddressRef_heapMono₂ _ ext ra) hls (rls.mono ext)
      (ext.getElem?_eq cell)
  | prj htIdx hfIdx href hd ra _ cell ih =>
    exact .prj htIdx hfIdx href hd (Bytes.repAddressRef_heapMono₂ _ ext ra) ih
      (ext.getElem?_eq cell)
  | str hbIdx href hmem rbs hs cell =>
    exact .str hbIdx href (hsub _ hmem) (Bytes.repByteStream_heapMono₂ _ ext rbs) hs
      (ext.getElem?_eq cell)
  | nat hbIdx href hmem hcanon rlimbs hlast hval cell =>
    exact .nat hbIdx href (hsub _ hmem) hcanon (repList_heapMono₂ _ repU64_heapMono₂ ext rlimbs)
      hlast hval (ext.getElem?_eq cell)
  | app _ _ cell ihf iha => exact .app ihf iha (ext.getElem?_eq cell)
  | lam rl _ _ cell iht ihb => exact .lam (rl.mono ext) iht ihb (ext.getElem?_eq cell)
  | all rl _ _ cell iht ihb => exact .all (rl.mono ext) iht ihb (ext.getElem?_eq cell)
  | letE _ _ _ cell iht ihv ihb => exact .letE iht ihv ihb (ext.getElem?_eq cell)
  | share hidx hsh _ ih => exact .share hidx hsh ih

/-! ## Operational proofs for `convert_expr`, `convert_annotated`, `convert_block`, `convert_root` -/

private theorem addrList_inst_eq :
    (Instance.mk "Lists::Node" [.ptr (.array .field 32)]).symbol = addressListEnum := by
  decide +kernel

private theorem addrLookup_inst_eq :
    (Instance.mk "Lists::lookup" [.ptr (.array .field 32)]).symbol =
      Names.«Lists::lookup<&[Field; 32]>» := by
  decide +kernel

private theorem exprList_inst_eq :
    (Instance.mk "Lists::Node" [.ptr (.named "Ixon::Expr" [])]).symbol = exprListEnum := by
  decide +kernel

private theorem exprDrop_inst_eq :
    (Instance.mk "Lists::drop" [.ptr (.named "Ixon::Expr" [])]).symbol =
      Names.«Lists::drop<&Ixon::Expr>» := by
  decide +kernel

private theorem lookup_addr_spec {addrs : List _root_.Address} {listPtr r : SourceValue F}
    {idx : UInt64} {h h' : Heap F} {cs : List (Call F)}
    (hidx : idx.toNat < 72057594037927936)
    (hlist : RepList addressListEnum RepIxonAddressRef h addrs listPtr)
    (ev : ObsFn W Names.«Lists::lookup<&[Field; 32]>» [listPtr, .field (idx.toNat : F)] h r h' cs) :
    h' = h ∧ ∃ (a : _root_.Address) (d : Bytes.Address),
      addrs[idx.toNat]? = some a ∧ Core.ixAddr d = a ∧ Bytes.RepAddressRef Core.addrTy h d r := by
  rw [← addrLookup_inst_eq] at ev
  have hlist' : RepList (Instance.mk "Lists::Node" [.ptr (.array .field 32)]).symbol
      RepIxonAddressRef h addrs listPtr := by
    rwa [addrList_inst_eq]
  obtain ⟨⟨a, hget, d, rfl, hd⟩, hh'⟩ := Lib.Lists.lookup_spec ev hlist'
  have hval : ((idx.toNat : F).val) = idx.toNat := ZMod.val_cast_of_lt (by omega)
  rw [hval] at hget
  exact ⟨hh', ixAddr d, d, hget, rfl, hd⟩

private theorem add_zero_one_eq_zero {b1 b2 : Nat} {v : SourceValue F}
    (hb1 : b1 = 0 ∨ b1 = 1) (hb2 : b2 = 0 ∨ b2 = 1)
    (hop : evalBinOp .add (.field (b1 : F)) (.field (b2 : F)) = .ok v) :
    (v = .field 0 → b1 = 0 ∧ b2 = 0) ∧ ∃ s : Nat, v = .field (s : F) ∧ s ≤ 2 := by
  simp only [evalBinOp, Except.ok.injEq] at hop
  subst hop
  rcases hb1 with rfl | rfl <;> rcases hb2 with rfl | rfl
  · exact ⟨fun _ => ⟨rfl, rfl⟩, 0, by simp, by omega⟩
  · refine ⟨fun h => ?_, 1, by simp, by omega⟩
    simp at h
  · refine ⟨fun h => ?_, 1, by simp, by omega⟩
    simp at h
  · refine ⟨fun h => ?_, 2, by push_cast; rfl, by omega⟩
    have h2 : ((1 : F) + 1) = (2 : F) := by norm_num
    rw [h2] at h
    have h0 := (natCast_eq_zero_iff (a := 2) (by omega)).mp (Value.field.inj h)
    omega

private theorem convert_expr_go (fuel : Nat) :
    ∀ {e : Ixon.Expr} {bound : Nat} {refs recurAddrs : List _root_.Address}
      {univs : List Ixon.Univ} {sharing : List Ixon.Expr}
      {ep shPtr refsPtr recPtr univsPtr r : SourceValue F}
      {h h' : Heap F} {calls : List (Call F)},
      calls.length ≤ fuel →
      bound < 4294967296 →
      RepExpr h e ep →
      RepShareVec h sharing shPtr →
      RepList addressListEnum RepIxonAddressRef h refs refsPtr →
      RepList addressListEnum RepIxonAddressRef h recurAddrs recPtr →
      RepList univListEnum RepUnivPtr h univs univsPtr →
      ObsFn W "Convert::convert_expr"
        [ep, shPtr, .field (bound : F), refsPtr, recPtr, univsPtr] h r h' calls →
      Heap.Extends h h' ∧ PreShareOk sharing bound e ∧
      ∃ (kp : SourceValue F) (b : Nat) (blobs : List (_root_.Address × ByteArray)),
        (b = 0 ∨ b = 1) ∧
        r = .tuple [kp, .field (b : F)] ∧
        HashedPairs calls blobs ∧
        (b = 0 → RawConvExpr refs recurAddrs univs sharing blobs h' bound e kp) := by
  induction fuel with
  | zero =>
    intro e bound refs recurAddrs univs sharing ep shPtr refsPtr recPtr univsPtr r h h' calls
      hfuel hbound hep _ _ _ _ ev
    cases «Convert::convert_expr».obs ev with
    | Lam _ _ m1268 ld12 he1266 hm1276 he1293 _ =>
      cases hep with
      | lam cell _ _ =>
        subst he1266 hm1276 he1293
        exact ⟨Heap.Extends.snoc _ _, .lam, _, 1, [], .inr rfl, rfl, .nil, fun h0 => nomatch h0⟩
      | sort cell | var cell | ref cell _ | recur cell _ | prj cell _ | str cell | nat cell
      | app cell _ _ | all cell _ _ | letE cell _ _ _ | share cell =>
        exact (Core.load_cell_ne cell ld12 (by decide)).elim
    | All _ _ m1320 ld12 he1318 hm1328 he1345 _ =>
      cases hep with
      | all cell _ _ =>
        subst he1318 hm1328 he1345
        exact ⟨Heap.Extends.snoc _ _, .all, _, 1, [], .inr rfl, rfl, .nil, fun h0 => nomatch h0⟩
      | sort cell | var cell | ref cell _ | recur cell _ | prj cell _ | str cell | nat cell
      | app cell _ _ | lam cell _ _ | letE cell _ _ _ | share cell =>
        exact (Core.load_cell_ne cell ld12 (by decide)).elim
    | Srt (hc114 := hc) .. | Var (hc173 := hc) .. | Ref (hc305 := hc) .. | Rec (hc437 := hc) ..
    | Prj_n0 (hc654 := hc) .. | Prj_other (hc678 := hc) .. | Str (hc821 := hc) ..
    | Nat (hc986 := hc) .. | App_n0 (hc1218 := hc) .. | App_other (hc1242 := hc) ..
    | Let_n0 (hc1681 := hc) .. | Let_other (hc1705 := hc) .. | Share (hc1889 := hc) .. =>
      rw [hc] at hfuel; simp at hfuel
  | succ fuel ih =>
    intro e bound refs recurAddrs univs sharing ep shPtr refsPtr recPtr univsPtr r h h' calls
      hfuel hbound hep hsh hrefs hrecs hunivs ev
    rcases «Convert::convert_expr».obs ev with
      ⟨x_u_idx, v25, m26, cs36, v40, m49, cs57, m74, v86, m88, cs96, ld12, ev59, ev38, he72,
        hm82, ev98, he113, hc114⟩ |
      ⟨x_idx, m133, v145, m147, cs155, ld12, he131, hm141, ev157, he172, hc173⟩ |
      ⟨x_ridx, x_uidxs, v191, m192, _, v206, m215, _, v234, m235, _, m270, ld12, ev225, ev204,
        ev247, he268, hm278, he304, _⟩ |
      ⟨x_ridx, x_uidxs, v323, m324, _, v338, m347, _, v366, m367, _, m402, ld12, ev357, ev336,
        ev379, he400, hm410, he436, _⟩ |
      ⟨x_tidx, x_fidx, x_inner, m461, cs471, x_ki, v549, m550, _, v564, m573, _, m598, v611,
        m621, _, ld12, ev473, ev583, ev562, he596, hm606, ev631, he653, hc654⟩ |
      ⟨x_tidx, x_fidx, x_inner, m461, cs471, x_ki, x_bi, ld12, ev473, hne655, he663, he677,
        hc678⟩ |
      ⟨x_bidx, v691, m692, cs702, v706, m715, cs723, v734, m735, cs745, v756, m757, cs767, m784,
        ld12, ev725, ev704, ev747, ev769, he782, hm792, he820, hc821⟩ |
      ⟨x_bidx, v834, m835, cs845, v849, m858, cs866, v877, m878, cs888, v899, m900, cs910, v921,
        m922, cs932, m949, ld12, ev868, ev847, ev890, ev912, ev934, he947, hm957, he985, hc986⟩ |
      ⟨x_f, x_a, m1005, cs1015, x_kf, x_bf, m1080, cs1090, x_ka, x_ba, m1183, ld12, ev1017,
        ev1092, op1170, he1181, hm1191, he1217, hc1218⟩ |
      ⟨x_f, x_a, m1005, cs1015, x_kf, x_bf, m1080, cs1090, x_ka, x_ba, v1154, ld12, ev1017,
        ev1092, op1170, hne1219, he1227, he1241, hc1242⟩ |
      ⟨_, _, m1268, ld12, he1266, hm1276, he1293, _⟩ |
      ⟨_, _, m1320, ld12, he1318, hm1328, he1345, _⟩ |
      ⟨_, x_ty, x_val, x_body, m1376, cs1386, x_kt, x_bt, m1451, cs1461, x_kv, x_bv, m1526,
        cs1536, x_kb, x_bb, x1609, m1638, ld12, ev1388, ev1463, ev1538, op1624, op1616, he1636,
        hm1646, he1680, hc1681⟩ |
      ⟨_, x_ty, x_val, x_body, m1376, cs1386, x_kt, x_bt, m1451, cs1461, x_kv, x_bv, m1526,
        cs1536, x_kb, x_bb, v1600, x1609, ld12, ev1388, ev1463, ev1538, op1624, op1616, hne1682,
        he1690, he1704, hc1705⟩ |
      ⟨x_idx, v1718, m1719, _, v1751, m1754, _, m1789, p1796, _, x_s, w1824, cs1838, ld12,
        ev1731, ev1764, heq1787, ev1804, ld1798, ev1840, hc1889⟩
    · -- Srt
      cases hep with
      | sort (idx := uIdx) cell =>
        have hxs := (Core.load_cell cell ld12).2
        simp only [List.cons.injEq, and_true] at hxs; subst hxs
        obtain ⟨hlt, hv40, hm49⟩ := Lib.u64_to_field_spec (Deserialize.repU64_u64Value h uIdx) ev59
        subst hv40 hm49
        rw [← univLookup_inst_eq] at ev38
        have hunivs' : RepList (Instance.mk "Lists::Node" [.ptr (.named "Ixon::Univ" [])]).symbol
            RepUnivPtr h univs univsPtr := by rwa [univList_inst_eq]
        obtain ⟨⟨u, hu_get, hu_rep⟩, hm26⟩ := Lib.Lists.lookup_spec ev38 hunivs'
        subst hm26
        have hval : ((uIdx.toNat : F).val) = uIdx.toNat := ZMod.val_cast_of_lt (by omega)
        rw [hval] at hu_get
        obtain ⟨ext1, rl⟩ := convert_univ_spec hu_rep ev98
        subst he72 hm82 he113
        have ext_fin := Heap.Extends.snoc m88 (.construct Core.kexprEnum "Srt" [v86])
        exact ⟨ext1.trans ext_fin, .sort, _, 0, [], .inl rfl, rfl, .nil,
          fun _ => .sort hlt hu_get (rl.mono ext_fin) (by simp)⟩
      | _ => exact (Core.load_cell_ne ‹_› ld12 (by decide)).elim
    · -- Var
      cases hep with
      | var (idx := idx) cell =>
        have hxs := (Core.load_cell cell ld12).2
        simp only [List.cons.injEq, and_true] at hxs; subst hxs
        obtain ⟨hlt, hv145, hm147⟩ := Lib.u64_to_field_spec (Deserialize.repU64_u64Value h idx) ev157
        subst hv145 hm147 he131 hm141 he172
        exact ⟨Heap.Extends.snoc _ _, .var, _, 0, [], .inl rfl, rfl, .nil,
          fun _ => .var hlt (by simp)⟩
      | _ => exact (Core.load_cell_ne ‹_› ld12 (by decide)).elim
    · -- Ref
      cases hep with
      | ref (idx := rIdx) (univs := uIdxs) cell listRep =>
        have hxs := (Core.load_cell cell ld12).2
        simp only [List.cons.injEq, and_true] at hxs; obtain ⟨rfl, rfl⟩ := hxs
        obtain ⟨hlt, hv206, hm215⟩ := Lib.u64_to_field_spec (Deserialize.repU64_u64Value h rIdx) ev225
        subst hv206 hm215
        obtain ⟨hm192, a, d, href_get, hd_eq, ha_rep⟩ := lookup_addr_spec hlt hrefs ev204
        subst hm192
        obtain ⟨ext1, ls, rls, hls⟩ := convert_univ_idxs_spec listRep hunivs ev247
        subst he268 hm278 he304
        have ext_fin := Heap.Extends.snoc m235 (.construct Core.kexprEnum "Const" [v191, v234])
        exact ⟨ext1.trans ext_fin, .ref, _, 0, [], .inl rfl, rfl, .nil,
          fun _ => .ref hlt href_get hd_eq
            (Bytes.repAddressRef_heapMono₂ _ (ext1.trans ext_fin) ha_rep)
            hls (rls.mono ext_fin) (by simp)⟩
      | _ => exact (Core.load_cell_ne ‹_› ld12 (by decide)).elim
    · -- Rec
      cases hep with
      | recur (idx := rIdx) (univs := uIdxs) cell listRep =>
        have hxs := (Core.load_cell cell ld12).2
        simp only [List.cons.injEq, and_true] at hxs; obtain ⟨rfl, rfl⟩ := hxs
        obtain ⟨hlt, hv338, hm347⟩ := Lib.u64_to_field_spec (Deserialize.repU64_u64Value h rIdx) ev357
        subst hv338 hm347
        obtain ⟨hm324, a, d, hrec_get, hd_eq, ha_rep⟩ := lookup_addr_spec hlt hrecs ev336
        subst hm324
        obtain ⟨ext1, ls, rls, hls⟩ := convert_univ_idxs_spec listRep hunivs ev379
        subst he400 hm410 he436
        have ext_fin := Heap.Extends.snoc m367 (.construct Core.kexprEnum "Const" [v323, v366])
        exact ⟨ext1.trans ext_fin, .recur, _, 0, [], .inl rfl, rfl, .nil,
          fun _ => .recur hlt hrec_get hd_eq
            (Bytes.repAddressRef_heapMono₂ _ (ext1.trans ext_fin) ha_rep)
            hls (rls.mono ext_fin) (by simp)⟩
      | _ => exact (Core.load_cell_ne ‹_› ld12 (by decide)).elim
    · -- Prj_n0
      cases hep with
      | prj (tIdx := tIdx) (fIdx := fIdx) cell valRep =>
        have hxs := (Core.load_cell cell ld12).2
        simp only [List.cons.injEq, and_true] at hxs; rcases hxs with ⟨rfl, rfl, rfl⟩
        have hlen1 : cs471.length ≤ fuel := by
          rw [hc654] at hfuel; simp only [List.length_cons, List.length_append] at hfuel; omega
        obtain ⟨ext1, hpre_in, kp_in, b_in, blobs_in, hb_in, hr_in, hhp_in, hraw_in⟩ :=
          ih hlen1 hbound valRep hsh hrefs hrecs hunivs ev473
        simp only [Value.tuple.injEq, List.cons.injEq, and_true] at hr_in
        obtain ⟨rfl, hb0_eq⟩ := hr_in
        have hb0 : b_in = 0 := by rcases hb_in with rfl | rfl; · rfl; · simp at hb0_eq
        obtain ⟨ht_lt, hv564, hm573⟩ :=
          Lib.u64_to_field_spec (Deserialize.repU64_u64Value m461 tIdx) ev583
        subst hv564 hm573
        obtain ⟨hm550, a, d, href_get, hd_eq, ha_rep⟩ :=
          lookup_addr_spec ht_lt (repList_heapMono₂ _ repIxonAddressRef_heapMono₂ ext1 hrefs) ev562
        subst hm550
        obtain ⟨hf_lt, hv611, hm621⟩ :=
          Lib.u64_to_field_spec (Deserialize.repU64_u64Value m461 fIdx) ev631
        subst hv611 hm621 he596 hm606 he653
        have ext_fin := Heap.Extends.snoc m461
          (.construct Core.kexprEnum "Proj" [v549, .field (fIdx.toNat : F), kp_in])
        have hhp' : HashedPairs calls blobs_in :=
          hhp_in.sub (by rw [hc654]; intro c hc; simp [hc])
        exact ⟨ext1.trans ext_fin, .prj hpre_in, _, 0, blobs_in, .inl rfl, rfl, hhp',
          fun _ => .prj ht_lt hf_lt href_get hd_eq
            (Bytes.repAddressRef_heapMono₂ _ ext_fin ha_rep)
            ((hraw_in hb0).mono ext_fin (fun _ h => h)) (by simp)⟩
      | _ => exact (Core.load_cell_ne ‹_› ld12 (by decide)).elim
    · -- Prj_other
      cases hep with
      | prj cell valRep =>
        have hxs := (Core.load_cell cell ld12).2
        simp only [List.cons.injEq, and_true] at hxs; rcases hxs with ⟨rfl, rfl, rfl⟩
        have hlen1 : cs471.length ≤ fuel := by
          rw [hc678] at hfuel; simp only [List.length_cons, List.length_append] at hfuel; omega
        obtain ⟨ext1, hpre_in, kp_in, b_in, blobs_in, _, _, hhp_in, _⟩ :=
          ih hlen1 hbound valRep hsh hrefs hrecs hunivs ev473
        subst he663 he677
        exact ⟨ext1, .prj hpre_in, _, 1, blobs_in, .inr rfl, rfl,
          hhp_in.sub (by rw [hc678]; intro c hc; simp [hc]), fun h0 => nomatch h0⟩
      | _ => exact (Core.load_cell_ne ‹_› ld12 (by decide)).elim
    · -- Str
      cases hep with
      | str (idx := bIdx) cell =>
        have hxs := (Core.load_cell cell ld12).2
        simp only [List.cons.injEq, and_true] at hxs; subst hxs
        obtain ⟨hb_lt, hv706, hm715⟩ :=
          Lib.u64_to_field_spec (Deserialize.repU64_u64Value h bIdx) ev725
        subst hv706 hm715
        obtain ⟨hm692, a, d, href_get, hd_eq, ha_rep⟩ := lookup_addr_spec hb_lt hrefs ev704
        subst hm692
        obtain ⟨ext_blob, bs, hst, hhashed, hblake⟩ := load_verified_blob_addr ha_rep ev747
        have hst' : Bytes.RepByteStream Core.byteListEnum m735 bs v734 := by
          simpa [Stream, Core.byteListEnum] using hst
        obtain ⟨hm757, s, hs⟩ := utf8_validate_spec hst' ev769
        subst hm757 he782 hm792 he820
        have ext_fin := Heap.Extends.snoc m735
          (.construct Core.kexprEnum "Lit" [.construct Core.klitEnum "Str" [v734]])
        have hhashed_calls : Hashed calls ⟨bs.toArray⟩ := by
          obtain ⟨cl, hcl, rest⟩ := hhashed
          exact ⟨cl, by rw [hc821]; simp [hcl], rest⟩
        have hhp : HashedPairs calls [(a, ⟨bs.toArray⟩)] := by
          intro p hp
          simp only [List.mem_singleton] at hp; subst hp
          exact ⟨hhashed_calls, hblake.trans hd_eq⟩
        exact ⟨ext_blob.trans ext_fin, .str, _, 0, [(a, ⟨bs.toArray⟩)], .inl rfl, rfl, hhp,
          fun _ => .str hb_lt href_get (by simp)
            (Bytes.repByteStream_heapMono₂ _ ext_fin hst') hs (by simp)⟩
      | _ => exact (Core.load_cell_ne ‹_› ld12 (by decide)).elim
    · -- Nat
      cases hep with
      | nat (idx := bIdx) cell =>
        have hxs := (Core.load_cell cell ld12).2
        simp only [List.cons.injEq, and_true] at hxs; subst hxs
        obtain ⟨hb_lt, hv849, hm858⟩ :=
          Lib.u64_to_field_spec (Deserialize.repU64_u64Value h bIdx) ev868
        subst hv849 hm858
        obtain ⟨hm835, a, d, href_get, hd_eq, ha_rep⟩ := lookup_addr_spec hb_lt hrefs ev847
        subst hm835
        obtain ⟨ext_blob, bs, hst, hhashed, hblake⟩ := load_verified_blob_addr ha_rep ev890
        have hst' : Bytes.RepByteStream Core.byteListEnum m878 bs v877 := by
          simpa [Stream, Core.byteListEnum] using hst
        obtain ⟨hcanon, hm900⟩ := assert_nat_blob_canonical_spec hst' ev912
        subst hm900
        obtain ⟨ext_limbs, limbs, rlimbs, hlast, hval⟩ := bytes_to_limbs_spec hst' ev934
        subst he947 hm957 he985
        have ext_fin := Heap.Extends.snoc m922
          (.construct Core.kexprEnum "Lit" [.construct Core.klitEnum "Nat" [v921]])
        have hhashed_calls : Hashed calls ⟨bs.toArray⟩ := by
          obtain ⟨cl, hcl, rest⟩ := hhashed
          exact ⟨cl, by rw [hc986]; simp [hcl], rest⟩
        have hhp : HashedPairs calls [(a, ⟨bs.toArray⟩)] := by
          intro p hp
          simp only [List.mem_singleton] at hp; subst hp
          exact ⟨hhashed_calls, hblake.trans hd_eq⟩
        exact ⟨(ext_blob.trans ext_limbs).trans ext_fin, .nat, _, 0, [(a, ⟨bs.toArray⟩)],
          .inl rfl, rfl, hhp,
          fun _ => .nat hb_lt href_get (by simp) hcanon
            (repList_heapMono₂ _ repU64_heapMono₂ ext_fin rlimbs) hlast hval (by simp)⟩
      | _ => exact (Core.load_cell_ne ‹_› ld12 (by decide)).elim
    · -- App_n0
      cases hep with
      | app cell fnRep argRep =>
        have hxs := (Core.load_cell cell ld12).2
        simp only [List.cons.injEq, and_true] at hxs; obtain ⟨rfl, rfl⟩ := hxs
        have hlen1 : cs1015.length ≤ fuel := by
          rw [hc1218] at hfuel; simp only [List.length_cons, List.length_append] at hfuel; omega
        have hlen2 : cs1090.length ≤ fuel := by
          rw [hc1218] at hfuel; simp only [List.length_cons, List.length_append] at hfuel; omega
        obtain ⟨ext1, hpre_f, kf, bf, blobs_f, hbf, hrf, hhp_f, hraw_f⟩ :=
          ih hlen1 hbound fnRep hsh hrefs hrecs hunivs ev1017
        simp only [Value.tuple.injEq, List.cons.injEq, and_true] at hrf; obtain ⟨rfl, rfl⟩ := hrf
        obtain ⟨ext2, hpre_a, ka, ba, blobs_a, hba, hra, hhp_a, hraw_a⟩ :=
          ih hlen2 hbound (argRep.mono ext1) (RepShareVec.mono ext1 hsh)
            (repList_heapMono₂ _ repIxonAddressRef_heapMono₂ ext1 hrefs)
            (repList_heapMono₂ _ repIxonAddressRef_heapMono₂ ext1 hrecs)
            (repList_heapMono₂ _ repUnivPtr_heapMono₂ ext1 hunivs) ev1092
        simp only [Value.tuple.injEq, List.cons.injEq, and_true] at hra; obtain ⟨rfl, rfl⟩ := hra
        obtain ⟨hb0, _⟩ := add_zero_one_eq_zero hbf hba op1170
        obtain ⟨hbf0, hba0⟩ := hb0 rfl
        subst he1181 hm1191 he1217
        have ext_fin := Heap.Extends.snoc m1080 (.construct Core.kexprEnum "App" [kf, ka])
        have hhp : HashedPairs calls (blobs_f ++ blobs_a) :=
          HashedPairs.append
            (hhp_f.sub (by rw [hc1218]; intro c hc; simp [hc]))
            (hhp_a.sub (by rw [hc1218]; intro c hc; simp [hc]))
        exact ⟨(ext1.trans ext2).trans ext_fin, .app hpre_f hpre_a, _, 0, blobs_f ++ blobs_a,
          .inl rfl, rfl, hhp,
          fun _ => .app
            ((hraw_f hbf0).mono (ext2.trans ext_fin) (fun _ hm => List.mem_append_left _ hm))
            ((hraw_a hba0).mono ext_fin (fun _ hm => List.mem_append_right _ hm)) (by simp)⟩
      | _ => exact (Core.load_cell_ne ‹_› ld12 (by decide)).elim
    · -- App_other
      cases hep with
      | app cell fnRep argRep =>
        have hxs := (Core.load_cell cell ld12).2
        simp only [List.cons.injEq, and_true] at hxs; obtain ⟨rfl, rfl⟩ := hxs
        have hlen1 : cs1015.length ≤ fuel := by
          rw [hc1242] at hfuel; simp only [List.length_cons, List.length_append] at hfuel; omega
        have hlen2 : cs1090.length ≤ fuel := by
          rw [hc1242] at hfuel; simp only [List.length_cons, List.length_append] at hfuel; omega
        obtain ⟨ext1, hpre_f, _, _, blobs_f, _, _, hhp_f, _⟩ :=
          ih hlen1 hbound fnRep hsh hrefs hrecs hunivs ev1017
        obtain ⟨ext2, hpre_a, _, _, blobs_a, _, _, hhp_a, _⟩ :=
          ih hlen2 hbound (argRep.mono ext1) (RepShareVec.mono ext1 hsh)
            (repList_heapMono₂ _ repIxonAddressRef_heapMono₂ ext1 hrefs)
            (repList_heapMono₂ _ repIxonAddressRef_heapMono₂ ext1 hrecs)
            (repList_heapMono₂ _ repUnivPtr_heapMono₂ ext1 hunivs) ev1092
        subst he1227 he1241
        have hhp : HashedPairs calls (blobs_f ++ blobs_a) :=
          HashedPairs.append
            (hhp_f.sub (by rw [hc1242]; intro c hc; simp [hc]))
            (hhp_a.sub (by rw [hc1242]; intro c hc; simp [hc]))
        exact ⟨ext1.trans ext2, .app hpre_f hpre_a, _, 1, blobs_f ++ blobs_a,
          .inr rfl, rfl, hhp, fun h0 => nomatch h0⟩
      | _ => exact (Core.load_cell_ne ‹_› ld12 (by decide)).elim
    · -- Lam
      cases hep with
      | lam cell _ _ =>
        subst he1266 hm1276 he1293
        exact ⟨Heap.Extends.snoc _ _, .lam, _, 1, [], .inr rfl, rfl, .nil, fun h0 => nomatch h0⟩
      | _ => exact (Core.load_cell_ne ‹_› ld12 (by decide)).elim
    · -- All
      cases hep with
      | all cell _ _ =>
        subst he1318 hm1328 he1345
        exact ⟨Heap.Extends.snoc _ _, .all, _, 1, [], .inr rfl, rfl, .nil, fun h0 => nomatch h0⟩
      | _ => exact (Core.load_cell_ne ‹_› ld12 (by decide)).elim
    · -- Let_n0
      cases hep with
      | letE cell tyRep valRep bodyRep =>
        have hxs := (Core.load_cell cell ld12).2
        simp only [List.cons.injEq, and_true] at hxs; rcases hxs with ⟨_, rfl, rfl, rfl⟩
        have hlen1 : cs1386.length ≤ fuel := by
          rw [hc1681] at hfuel; simp only [List.length_cons, List.length_append] at hfuel; omega
        have hlen2 : cs1461.length ≤ fuel := by
          rw [hc1681] at hfuel; simp only [List.length_cons, List.length_append] at hfuel; omega
        have hlen3 : cs1536.length ≤ fuel := by
          rw [hc1681] at hfuel; simp only [List.length_cons, List.length_append] at hfuel; omega
        obtain ⟨ext1, hpre_t, kt, bt, blobs_t, hbt, hrt, hhp_t, hraw_t⟩ :=
          ih hlen1 hbound tyRep hsh hrefs hrecs hunivs ev1388
        simp only [Value.tuple.injEq, List.cons.injEq, and_true] at hrt; obtain ⟨rfl, rfl⟩ := hrt
        obtain ⟨ext2, hpre_v, kv, bv, blobs_v, hbv, hrv, hhp_v, hraw_v⟩ :=
          ih hlen2 hbound (valRep.mono ext1) (RepShareVec.mono ext1 hsh)
            (repList_heapMono₂ _ repIxonAddressRef_heapMono₂ ext1 hrefs)
            (repList_heapMono₂ _ repIxonAddressRef_heapMono₂ ext1 hrecs)
            (repList_heapMono₂ _ repUnivPtr_heapMono₂ ext1 hunivs) ev1463
        simp only [Value.tuple.injEq, List.cons.injEq, and_true] at hrv; obtain ⟨rfl, rfl⟩ := hrv
        have ext12 := ext1.trans ext2
        obtain ⟨ext3, hpre_b, kb, bb, blobs_b, hbb, hrb, hhp_b, hraw_b⟩ :=
          ih hlen3 hbound (bodyRep.mono ext12) (RepShareVec.mono ext12 hsh)
            (repList_heapMono₂ _ repIxonAddressRef_heapMono₂ ext12 hrefs)
            (repList_heapMono₂ _ repIxonAddressRef_heapMono₂ ext12 hrecs)
            (repList_heapMono₂ _ repUnivPtr_heapMono₂ ext12 hunivs) ev1538
        simp only [Value.tuple.injEq, List.cons.injEq, and_true] at hrb; obtain ⟨rfl, rfl⟩ := hrb
        obtain ⟨hbtv0, s12, hs12, hs12_le⟩ := add_zero_one_eq_zero hbt hbv op1624
        subst hs12
        simp only [evalBinOp, Except.ok.injEq, Value.field.injEq] at op1616
        have hs_all0 : s12 = 0 ∧ bb = 0 := by
          rcases hbb with rfl | rfl
          · simp only [Nat.cast_zero, add_zero] at op1616
            exact ⟨(natCast_eq_zero_iff (by omega)).mp op1616, rfl⟩
          · have hP : 4 < IxVM.P := by decide
            have hlt_s : s12 + 1 < IxVM.P := by omega
            have hcast : ((s12 : F) + (1 : Nat)) = ((s12 + 1 : Nat) : F) := by push_cast; rfl
            rw [hcast] at op1616
            have hz := (natCast_eq_zero_iff hlt_s).mp op1616
            omega
        obtain ⟨hbt0, hbv0⟩ := hbtv0 (by rw [hs_all0.1, Nat.cast_zero])
        subst he1636 hm1646 he1680
        have ext_fin := Heap.Extends.snoc m1526 (.construct Core.kexprEnum "Let" [kt, kv, kb])
        have hhp : HashedPairs calls ((blobs_t ++ blobs_v) ++ blobs_b) :=
          HashedPairs.append
            (HashedPairs.append
              (hhp_t.sub (by rw [hc1681]; intro c hc; simp [hc]))
              (hhp_v.sub (by rw [hc1681]; intro c hc; simp [hc])))
            (hhp_b.sub (by rw [hc1681]; intro c hc; simp [hc]))
        exact ⟨((ext1.trans ext2).trans ext3).trans ext_fin, .letE hpre_t hpre_v hpre_b,
          _, 0, (blobs_t ++ blobs_v) ++ blobs_b, .inl rfl, rfl, hhp,
          fun _ => .letE
            ((hraw_t hbt0).mono ((ext2.trans ext3).trans ext_fin)
              (fun _ hm => List.mem_append_left _ (List.mem_append_left _ hm)))
            ((hraw_v hbv0).mono (ext3.trans ext_fin)
              (fun _ hm => List.mem_append_left _ (List.mem_append_right _ hm)))
            ((hraw_b hs_all0.2).mono ext_fin
              (fun _ hm => List.mem_append_right _ hm)) (by simp)⟩
      | _ => exact (Core.load_cell_ne ‹_› ld12 (by decide)).elim
    · -- Let_other
      cases hep with
      | letE cell tyRep valRep bodyRep =>
        have hxs := (Core.load_cell cell ld12).2
        simp only [List.cons.injEq, and_true] at hxs; rcases hxs with ⟨_, rfl, rfl, rfl⟩
        have hlen1 : cs1386.length ≤ fuel := by
          rw [hc1705] at hfuel; simp only [List.length_cons, List.length_append] at hfuel; omega
        have hlen2 : cs1461.length ≤ fuel := by
          rw [hc1705] at hfuel; simp only [List.length_cons, List.length_append] at hfuel; omega
        have hlen3 : cs1536.length ≤ fuel := by
          rw [hc1705] at hfuel; simp only [List.length_cons, List.length_append] at hfuel; omega
        obtain ⟨ext1, hpre_t, _, _, blobs_t, _, _, hhp_t, _⟩ :=
          ih hlen1 hbound tyRep hsh hrefs hrecs hunivs ev1388
        obtain ⟨ext2, hpre_v, _, _, blobs_v, _, _, hhp_v, _⟩ :=
          ih hlen2 hbound (valRep.mono ext1) (RepShareVec.mono ext1 hsh)
            (repList_heapMono₂ _ repIxonAddressRef_heapMono₂ ext1 hrefs)
            (repList_heapMono₂ _ repIxonAddressRef_heapMono₂ ext1 hrecs)
            (repList_heapMono₂ _ repUnivPtr_heapMono₂ ext1 hunivs) ev1463
        have ext12 := ext1.trans ext2
        obtain ⟨ext3, hpre_b, _, _, blobs_b, _, _, hhp_b, _⟩ :=
          ih hlen3 hbound (bodyRep.mono ext12) (RepShareVec.mono ext12 hsh)
            (repList_heapMono₂ _ repIxonAddressRef_heapMono₂ ext12 hrefs)
            (repList_heapMono₂ _ repIxonAddressRef_heapMono₂ ext12 hrecs)
            (repList_heapMono₂ _ repUnivPtr_heapMono₂ ext12 hunivs) ev1538
        subst he1690 he1704
        have hhp : HashedPairs calls ((blobs_t ++ blobs_v) ++ blobs_b) :=
          HashedPairs.append
            (HashedPairs.append
              (hhp_t.sub (by rw [hc1705]; intro c hc; simp [hc]))
              (hhp_v.sub (by rw [hc1705]; intro c hc; simp [hc])))
            (hhp_b.sub (by rw [hc1705]; intro c hc; simp [hc]))
        exact ⟨(ext1.trans ext2).trans ext3, .letE hpre_t hpre_v hpre_b,
          _, 1, (blobs_t ++ blobs_v) ++ blobs_b, .inr rfl, rfl, hhp, fun h0 => nomatch h0⟩
      | _ => exact (Core.load_cell_ne ‹_› ld12 (by decide)).elim
    · -- Share
      cases hep with
      | share (idx := idx) cell =>
        have hxs := (Core.load_cell cell ld12).2
        simp only [List.cons.injEq, and_true] at hxs; subst hxs
        obtain ⟨hidx56, hv1718, hm1719⟩ :=
          Lib.u64_to_field_spec (Deserialize.repU64_u64Value h idx) ev1731
        subst hv1718 hm1719
        obtain ⟨a_lt, b_lt, ha32, hb32, ha_eq, hb_eq, hr_lt, hm1754⟩ :=
          lt_fields_both_spec ev1764
        subst hm1754
        have ha_idx : idx.toNat = a_lt :=
          (natCast_eq_iff (by omega) (by omega)).mp (Value.field.inj ha_eq)
        have hb_bnd : bound = b_lt :=
          (natCast_eq_iff (by omega) (by omega)).mp (Value.field.inj hb_eq)
        subst ha_idx hb_bnd
        rw [hr_lt] at heq1787
        have hidx_lt : idx.toNat < bound := by
          by_cases hlt : idx.toNat < bound
          · exact hlt
          · simp [hlt] at heq1787
        rw [← exprDrop_inst_eq] at ev1804
        have hsh' : RepList (Instance.mk "Lists::Node" [.ptr (.named "Ixon::Expr" [])]).symbol
            RepExpr h sharing shPtr := by rwa [exprList_inst_eq]
        obtain ⟨_, hdrop, hm1789⟩ := Lib.Lists.drop_spec idx.toNat
          (ZMod.val_cast_of_lt (by omega)) ev1804 hsh'
        subst hm1789
        rw [exprList_inst_eq, exprListEnum_eq] at hdrop
        have hval_idx : ((idx.toNat : F).val) = idx.toNat := ZMod.val_cast_of_lt (by omega)
        rw [hval_idx] at hdrop
        obtain ⟨s, rest_sh, hdrop_eq, hs_rep, _⟩ := Core.RepList.cons_of_load hdrop ld1798
        have hsh_get : sharing[idx.toNat]? = some s := by
          rw [← List.head?_drop, hdrop_eq]; rfl
        have hlen_rec : cs1838.length ≤ fuel := by
          rw [hc1889] at hfuel; simp only [List.length_cons, List.length_append] at hfuel; omega
        obtain ⟨ext_rec, hpre_s, kp, b, blobs, hb, hr, hhp, hraw_s⟩ :=
          ih hlen_rec (by omega) hs_rep hsh hrefs hrecs hunivs ev1840
        exact ⟨ext_rec, .share hidx_lt hsh_get hpre_s, kp, b, blobs, hb, hr,
          hhp.sub (by rw [hc1889]; intro c hc; simp [hc]),
          fun hb0 => .share hidx_lt hsh_get (hraw_s hb0)⟩
      | _ => exact (Core.load_cell_ne ‹_› ld12 (by decide)).elim

/-- `Convert::convert_expr` validates `PreShareOk`, records all loaded literal blobs in
`HashedPairs`, and when `b = 0` constructs a `RawConvExpr` representation. -/
theorem convert_expr_spec {e : Ixon.Expr} {bound : Nat}
    {refs recurAddrs : List _root_.Address} {univs : List Ixon.Univ} {sharing : List Ixon.Expr}
    {ep shPtr refsPtr recPtr univsPtr r : SourceValue F}
    {h h' : Heap F} {calls : List (Call F)}
    (hbound : bound < 4294967296)
    (hep : RepExpr h e ep)
    (hsh : RepShareVec h sharing shPtr)
    (hrefs : RepList addressListEnum RepIxonAddressRef h refs refsPtr)
    (hrecs : RepList addressListEnum RepIxonAddressRef h recurAddrs recPtr)
    (hunivs : RepList univListEnum RepUnivPtr h univs univsPtr)
    (ev : ObsFn W "Convert::convert_expr"
      [ep, shPtr, .field (bound : F), refsPtr, recPtr, univsPtr] h r h' calls) :
    Heap.Extends h h' ∧ PreShareOk sharing bound e ∧
    ∃ (kp : SourceValue F) (b : Nat) (blobs : List (_root_.Address × ByteArray)),
      (b = 0 ∨ b = 1) ∧
      r = .tuple [kp, .field (b : F)] ∧
      HashedPairs calls blobs ∧
      (b = 0 → RawConvExpr refs recurAddrs univs sharing blobs h' bound e kp) :=
  convert_expr_go calls.length (Nat.le_refl _) hbound hep hsh hrefs hrecs hunivs ev

private theorem convert_annotated_go (fuel : Nat) :
    ∀ {e : Ixon.Expr} {bound : Nat} {refs recurAddrs : List _root_.Address}
      {univs : List Ixon.Univ} {sharing : List Ixon.Expr} {ns : List Ixon.BinderNode}
      {ep shPtr refsPtr recPtr univsPtr tbl nodesPtr r : SourceValue F}
      {h h' : Heap F} {calls : List (Call F)},
      calls.length ≤ fuel →
      bound < 4294967296 →
      PreShareOk sharing bound e →
      RepExpr h e ep →
      RepShareVec h sharing shPtr →
      RepList addressListEnum RepIxonAddressRef h refs refsPtr →
      RepList addressListEnum RepIxonAddressRef h recurAddrs recPtr →
      RepList univListEnum RepUnivPtr h univs univsPtr →
      RepBinderTree 4294967296 h tbl →
      RepList binderNodeListEnum RepBinderNode h ns nodesPtr →
      (∀ nd ∈ ns, BinderNodeParamsLt 4294967296 nd) →
      ObsFn W "Convert::convert_annotated"
        [ep, shPtr, .field (bound : F), refsPtr, recPtr, univsPtr, tbl, nodesPtr] h r h' calls →
      Heap.Extends h h' ∧
      ∃ (kp nodesOut : SourceValue F) (ns' : List Ixon.BinderNode)
        (blobs : List (_root_.Address × ByteArray)),
        r = .tuple [kp, nodesOut] ∧
        RepList binderNodeListEnum RepBinderNode h' ns' nodesOut ∧
        (∀ nd ∈ ns', BinderNodeParamsLt 4294967296 nd) ∧
        HashedPairs calls blobs ∧
        RawConvExpr refs recurAddrs univs sharing blobs h' bound e kp := by
  induction fuel with
  | zero =>
    intro e bound refs recurAddrs univs sharing ns ep shPtr refsPtr recPtr univsPtr tbl nodesPtr r
      h h' calls hfuel _ _ _ _ _ _ _ _ _ _ ev
    cases convert_annotated_obs ev with
    | App (hcs := hcs) .. | Lam (hcs := hcs) .. | All (hcs := hcs) ..
    | Let (hcs := hcs) .. | Prj (hcs := hcs) .. | Share (hcs := hcs) .. =>
      rw [hcs] at hfuel; simp at hfuel
  | succ fuel ih =>
    intro e bound refs recurAddrs univs sharing ns ep shPtr refsPtr recPtr univsPtr tbl nodesPtr r
      h h' calls hfuel hbound hpre hep hsh hrefs hrecs hunivs htbl hnodes hplt ev
    have branch_spec : ∀ {sub : Ixon.Expr} {subPtr kf kp2 nin nout : SourceValue F} {bf : Nat}
        {ns_in : List Ixon.BinderNode} {blobs_ce : List (_root_.Address × ByteArray)}
        {m_in m_out : Heap F} {cs_br : List (Call F)},
        cs_br.length ≤ fuel + 1 →
        PreShareOk sharing bound sub →
        RepExpr m_in sub subPtr →
        RepShareVec m_in sharing shPtr →
        RepList addressListEnum RepIxonAddressRef m_in refs refsPtr →
        RepList addressListEnum RepIxonAddressRef m_in recurAddrs recPtr →
        RepList univListEnum RepUnivPtr m_in univs univsPtr →
        RepBinderTree 4294967296 m_in tbl →
        RepList binderNodeListEnum RepBinderNode m_in ns_in nin →
        (∀ nd ∈ ns_in, BinderNodeParamsLt 4294967296 nd) →
        (bf = 0 ∨ bf = 1) →
        (bf = 0 → RawConvExpr refs recurAddrs univs sharing blobs_ce m_in bound sub kf) →
        AnnotBranch subPtr shPtr (.field (bound : F)) refsPtr recPtr univsPtr tbl
          kf (.field (bf : F)) nin m_in kp2 nout m_out cs_br →
        Heap.Extends m_in m_out ∧
        ∃ (ns_out : List Ixon.BinderNode) (blobs_br : List (_root_.Address × ByteArray)),
          RepList binderNodeListEnum RepBinderNode m_out ns_out nout ∧
          (∀ nd ∈ ns_out, BinderNodeParamsLt 4294967296 nd) ∧
          HashedPairs cs_br blobs_br ∧
          RawConvExpr refs recurAddrs univs sharing (blobs_ce ++ blobs_br) m_out bound sub kp2 := by
      intro sub subPtr kf kp2 nin nout bf ns_in blobs_ce m_in m_out cs_br
        hlen_br hpre_sub hsub_rep hsh_m hrefs_m hrecs_m hunivs_m htbl_m hnin hplt_in
        hbf hraw_ce br
      cases br with
      | n0 hbf_eq hkp2 hnout hm hcs_br =>
        subst hkp2 hnout hm hcs_br
        have hbf0 : bf = 0 := by rcases hbf with rfl | rfl; · rfl; · simp at hbf_eq
        exact ⟨Heap.Extends.refl _, ns_in, [], hnin, hplt_in, .nil,
          (hraw_ce hbf0).mono (Heap.Extends.refl _) (fun _ hm => List.mem_append_left _ hm)⟩
      | other cs_rec _ ev_rec hcs_br =>
        have hlen_rec : cs_rec.length ≤ fuel := by
          rw [hcs_br] at hlen_br; simp only [List.length_cons] at hlen_br; omega
        obtain ⟨ext_r, kp2', nout', ns_out, blobs_r, htup, hnout, hplt_out, hhp_r, hraw_r⟩ :=
          ih hlen_rec hbound hpre_sub hsub_rep hsh_m hrefs_m hrecs_m hunivs_m htbl_m
            hnin hplt_in ev_rec
        simp only [Value.tuple.injEq, List.cons.injEq, and_true] at htup
        obtain ⟨rfl, rfl⟩ := htup
        exact ⟨ext_r, ns_out, blobs_r, hnout, hplt_out,
          hhp_r.sub (by rw [hcs_br]; intro c hc; simp [hc]),
          hraw_r.mono (Heap.Extends.refl _) (fun _ hm => List.mem_append_right _ hm)⟩
    rcases convert_annotated_obs ev with
      ⟨x_f, x_a, x_kf, x_bf, x_ka, x_ba, x_kf2, x_n1, x_ka2, x_n2, m1, m2, m3, m4,
        cs1, cs2, cs3, cs4, ld_e, ev_f, ev_a, br_f, br_a, hr, hh', hcs⟩ |
      ⟨x_ty, x_body, x_node, x_n0, x_l, x_kt, x_bt, x_kb, x_bb, x_kt2, x_n1, x_kb2, x_n2,
        m1, m2, m3, m4, m5, cs1, cs2, cs3, cs4, cs5, ld_e, ld_nodes, ev_l, ev_t, ev_b,
        br_t, br_b, hr, hh', hcs⟩ |
      ⟨x_ty, x_body, x_node, x_n0, x_l, x_kt, x_bt, x_kb, x_bb, x_kt2, x_n1, x_kb2, x_n2,
        m1, m2, m3, m4, m5, cs1, cs2, cs3, cs4, cs5, ld_e, ld_nodes, ev_l, ev_t, ev_b,
        br_t, br_b, hr, hh', hcs⟩ |
      ⟨w_hdr, x_ty, x_val, x_body, x_kt, x_bt, x_kv, x_bv, x_kb, x_bb,
        x_kt2, x_n1, x_kv2, x_n2, x_kb2, x_n3, m1, m2, m3, m4, m5, m6,
        cs1, cs2, cs3, cs4, cs5, cs6, ld_e, ev_t, ev_v, ev_b, br_t, br_v, br_b, hr, hh', hcs⟩ |
      ⟨x_tidx, x_fidx, x_inner, v_tidx, x_taddr, x_ki, x_n1, v_fidx, m1, m2, m3, m4,
        cs1, cs2, cs3, cs4, ld_e, ev_tf, ev_lk, ev_in, ev_ff, hr, hh', hcs⟩ |
      ⟨x_idx, x_n, p_drop, x_s, w_tail, x_node, x_n1, x_variant, v_var, x_enodes, x_k,
        m1, m2, m3, m4, m5, cs1, cs2, cs3, cs4, cs5, ld_e, ev_nf, ev_dr, ld_dr, ld_nodes,
        hnode, ev_vf, ev_bn, ev_cb, hr, hh', hcs⟩
    · -- App
      cases hep with
      | app cell fnRep argRep =>
        have hxs := (Core.load_cell cell ld_e).2
        simp only [List.cons.injEq, and_true] at hxs; obtain ⟨rfl, rfl⟩ := hxs
        obtain ⟨ext1, hpre_f, kf, bf, blobs_f, hbf, hrf, hhp_f, hraw_f⟩ :=
          convert_expr_spec hbound fnRep hsh hrefs hrecs hunivs ev_f
        simp only [Value.tuple.injEq, List.cons.injEq, and_true] at hrf; obtain ⟨rfl, rfl⟩ := hrf
        obtain ⟨ext2, hpre_a, ka, ba, blobs_a, hba, hra, hhp_a, hraw_a⟩ :=
          convert_expr_spec hbound (argRep.mono ext1) (RepShareVec.mono ext1 hsh)
            (repList_heapMono₂ _ repIxonAddressRef_heapMono₂ ext1 hrefs)
            (repList_heapMono₂ _ repIxonAddressRef_heapMono₂ ext1 hrecs)
            (repList_heapMono₂ _ repUnivPtr_heapMono₂ ext1 hunivs) ev_a
        simp only [Value.tuple.injEq, List.cons.injEq, and_true] at hra; obtain ⟨rfl, rfl⟩ := hra
        have ext12 := ext1.trans ext2
        have hcs3 : cs3.length ≤ fuel + 1 := by
          rw [hcs] at hfuel; simp only [List.length_cons, List.length_append] at hfuel; omega
        have hcs4 : cs4.length ≤ fuel + 1 := by
          rw [hcs] at hfuel; simp only [List.length_cons, List.length_append] at hfuel; omega
        obtain ⟨ext3, ns1, blobs_bf, hns1, hplt1, hhp_bf, hraw_f2⟩ :=
          branch_spec hcs3 hpre_f (fnRep.mono ext12) (RepShareVec.mono ext12 hsh)
            (repList_heapMono₂ _ repIxonAddressRef_heapMono₂ ext12 hrefs)
            (repList_heapMono₂ _ repIxonAddressRef_heapMono₂ ext12 hrecs)
            (repList_heapMono₂ _ repUnivPtr_heapMono₂ ext12 hunivs)
            (htbl.mono ext12)
            (repList_heapMono₂ _ repBinderNode_heapMono₂ ext12 hnodes) hplt
            hbf (fun h0 => (hraw_f h0).mono ext2 (fun _ hm => hm)) br_f
        have ext13 := ext12.trans ext3
        obtain ⟨ext4, ns2, blobs_ba, hns2, hplt2, hhp_ba, hraw_a2⟩ :=
          branch_spec hcs4 hpre_a (argRep.mono ext13) (RepShareVec.mono ext13 hsh)
            (repList_heapMono₂ _ repIxonAddressRef_heapMono₂ ext13 hrefs)
            (repList_heapMono₂ _ repIxonAddressRef_heapMono₂ ext13 hrecs)
            (repList_heapMono₂ _ repUnivPtr_heapMono₂ ext13 hunivs)
            (htbl.mono ext13) hns1 hplt1
            hba (fun h0 => (hraw_a h0).mono ext3 (fun _ hm => hm)) br_a
        subst hr hh'
        have ext_fin := Heap.Extends.snoc m4 (.construct Core.kexprEnum "App" [x_kf2, x_ka2])
        let allBlobs := (blobs_f ++ blobs_bf) ++ (blobs_a ++ blobs_ba)
        have hhp_all : HashedPairs calls allBlobs :=
          HashedPairs.append
            (HashedPairs.append
              (hhp_f.sub (by rw [hcs]; intro c hc; simp [hc]))
              (hhp_bf.sub (by rw [hcs]; intro c hc; simp [hc])))
            (HashedPairs.append
              (hhp_a.sub (by rw [hcs]; intro c hc; simp [hc]))
              (hhp_ba.sub (by rw [hcs]; intro c hc; simp [hc])))
        exact ⟨(ext13.trans ext4).trans ext_fin, _, x_n2, ns2, allBlobs, rfl,
          repList_heapMono₂ _ repBinderNode_heapMono₂ ext_fin hns2, hplt2, hhp_all,
          .app (hraw_f2.mono (ext4.trans ext_fin) (fun _ hm => List.mem_append_left _ hm))
            (hraw_a2.mono ext_fin (fun _ hm => List.mem_append_right _ hm)) (by simp)⟩
      | _ => exact (Core.load_cell_ne ‹_› ld_e (by decide)).elim
    · -- Lam
      cases hep with
      | lam cell tyRep bodyRep =>
        have hxs := (Core.load_cell cell ld_e).2
        simp only [List.cons.injEq, and_true] at hxs; obtain ⟨rfl, rfl⟩ := hxs
        have hnodes' := hnodes
        rw [binderNodeListEnum_eq] at hnodes'
        obtain ⟨nd0, ns0, rfl, hnd0, hns0⟩ := Core.RepList.cons_of_load hnodes' ld_nodes
        rw [← binderNodeListEnum_eq] at hns0
        obtain ⟨ext1, ℓ, hℓ⟩ := binder_level_spec hnd0 (hplt nd0 (by simp)) ev_l
        obtain ⟨ext2, hpre_t, kt, bt, blobs_t, hbt, hrt, hhp_t, hraw_t⟩ :=
          convert_expr_spec hbound (tyRep.mono ext1) (RepShareVec.mono ext1 hsh)
            (repList_heapMono₂ _ repIxonAddressRef_heapMono₂ ext1 hrefs)
            (repList_heapMono₂ _ repIxonAddressRef_heapMono₂ ext1 hrecs)
            (repList_heapMono₂ _ repUnivPtr_heapMono₂ ext1 hunivs) ev_t
        simp only [Value.tuple.injEq, List.cons.injEq, and_true] at hrt; obtain ⟨rfl, rfl⟩ := hrt
        have ext12 := ext1.trans ext2
        obtain ⟨ext3, hpre_b, kb, bb, blobs_b, hbb, hrb, hhp_b, hraw_b⟩ :=
          convert_expr_spec hbound (bodyRep.mono ext12) (RepShareVec.mono ext12 hsh)
            (repList_heapMono₂ _ repIxonAddressRef_heapMono₂ ext12 hrefs)
            (repList_heapMono₂ _ repIxonAddressRef_heapMono₂ ext12 hrecs)
            (repList_heapMono₂ _ repUnivPtr_heapMono₂ ext12 hunivs) ev_b
        simp only [Value.tuple.injEq, List.cons.injEq, and_true] at hrb; obtain ⟨rfl, rfl⟩ := hrb
        have ext13 := ext12.trans ext3
        have hcs4 : cs4.length ≤ fuel + 1 := by
          rw [hcs] at hfuel; simp only [List.length_cons, List.length_append] at hfuel; omega
        have hcs5 : cs5.length ≤ fuel + 1 := by
          rw [hcs] at hfuel; simp only [List.length_cons, List.length_append] at hfuel; omega
        obtain ⟨ext4, ns1, blobs_bt, hns1, hplt1, hhp_bt, hraw_t2⟩ :=
          branch_spec hcs4 hpre_t (tyRep.mono ext13) (RepShareVec.mono ext13 hsh)
            (repList_heapMono₂ _ repIxonAddressRef_heapMono₂ ext13 hrefs)
            (repList_heapMono₂ _ repIxonAddressRef_heapMono₂ ext13 hrecs)
            (repList_heapMono₂ _ repUnivPtr_heapMono₂ ext13 hunivs)
            (htbl.mono ext13)
            (repList_heapMono₂ _ repBinderNode_heapMono₂ ext13 hns0)
            (fun nd hnd => hplt nd (List.mem_cons_of_mem _ hnd))
            hbt (fun h0 => (hraw_t h0).mono ext3 (fun _ hm => hm)) br_t
        have ext14 := ext13.trans ext4
        obtain ⟨ext5, ns2, blobs_bb, hns2, hplt2, hhp_bb, hraw_b2⟩ :=
          branch_spec hcs5 hpre_b (bodyRep.mono ext14) (RepShareVec.mono ext14 hsh)
            (repList_heapMono₂ _ repIxonAddressRef_heapMono₂ ext14 hrefs)
            (repList_heapMono₂ _ repIxonAddressRef_heapMono₂ ext14 hrecs)
            (repList_heapMono₂ _ repUnivPtr_heapMono₂ ext14 hunivs)
            (htbl.mono ext14) hns1 hplt1
            hbb (fun h0 => (hraw_b h0).mono ext4 (fun _ hm => hm)) br_b
        subst hr hh'
        have ext_fin := Heap.Extends.snoc m5 (.construct Core.kexprEnum "Lam" [x_kt2, x_kb2, x_l])
        let allBlobs := (blobs_t ++ blobs_bt) ++ (blobs_b ++ blobs_bb)
        have hhp_all : HashedPairs calls allBlobs :=
          HashedPairs.append
            (HashedPairs.append
              (hhp_t.sub (by rw [hcs]; intro c hc; simp [hc]))
              (hhp_bt.sub (by rw [hcs]; intro c hc; simp [hc])))
            (HashedPairs.append
              (hhp_b.sub (by rw [hcs]; intro c hc; simp [hc]))
              (hhp_bb.sub (by rw [hcs]; intro c hc; simp [hc])))
        exact ⟨(ext14.trans ext5).trans ext_fin, _, x_n2, ns2, allBlobs, rfl,
          repList_heapMono₂ _ repBinderNode_heapMono₂ ext_fin hns2, hplt2, hhp_all,
          .lam (hℓ.mono ((((ext2.trans ext3).trans ext4).trans ext5).trans ext_fin))
            (hraw_t2.mono (ext5.trans ext_fin) (fun _ hm => List.mem_append_left _ hm))
            (hraw_b2.mono ext_fin (fun _ hm => List.mem_append_right _ hm)) (by simp)⟩
      | _ => exact (Core.load_cell_ne ‹_› ld_e (by decide)).elim
    · -- All
      cases hep with
      | all cell tyRep bodyRep =>
        have hxs := (Core.load_cell cell ld_e).2
        simp only [List.cons.injEq, and_true] at hxs; obtain ⟨rfl, rfl⟩ := hxs
        have hnodes' := hnodes
        rw [binderNodeListEnum_eq] at hnodes'
        obtain ⟨nd0, ns0, rfl, hnd0, hns0⟩ := Core.RepList.cons_of_load hnodes' ld_nodes
        rw [← binderNodeListEnum_eq] at hns0
        obtain ⟨ext1, ℓ, hℓ⟩ := binder_level_spec hnd0 (hplt nd0 (by simp)) ev_l
        obtain ⟨ext2, hpre_t, kt, bt, blobs_t, hbt, hrt, hhp_t, hraw_t⟩ :=
          convert_expr_spec hbound (tyRep.mono ext1) (RepShareVec.mono ext1 hsh)
            (repList_heapMono₂ _ repIxonAddressRef_heapMono₂ ext1 hrefs)
            (repList_heapMono₂ _ repIxonAddressRef_heapMono₂ ext1 hrecs)
            (repList_heapMono₂ _ repUnivPtr_heapMono₂ ext1 hunivs) ev_t
        simp only [Value.tuple.injEq, List.cons.injEq, and_true] at hrt; obtain ⟨rfl, rfl⟩ := hrt
        have ext12 := ext1.trans ext2
        obtain ⟨ext3, hpre_b, kb, bb, blobs_b, hbb, hrb, hhp_b, hraw_b⟩ :=
          convert_expr_spec hbound (bodyRep.mono ext12) (RepShareVec.mono ext12 hsh)
            (repList_heapMono₂ _ repIxonAddressRef_heapMono₂ ext12 hrefs)
            (repList_heapMono₂ _ repIxonAddressRef_heapMono₂ ext12 hrecs)
            (repList_heapMono₂ _ repUnivPtr_heapMono₂ ext12 hunivs) ev_b
        simp only [Value.tuple.injEq, List.cons.injEq, and_true] at hrb; obtain ⟨rfl, rfl⟩ := hrb
        have ext13 := ext12.trans ext3
        have hcs4 : cs4.length ≤ fuel + 1 := by
          rw [hcs] at hfuel; simp only [List.length_cons, List.length_append] at hfuel; omega
        have hcs5 : cs5.length ≤ fuel + 1 := by
          rw [hcs] at hfuel; simp only [List.length_cons, List.length_append] at hfuel; omega
        obtain ⟨ext4, ns1, blobs_bt, hns1, hplt1, hhp_bt, hraw_t2⟩ :=
          branch_spec hcs4 hpre_t (tyRep.mono ext13) (RepShareVec.mono ext13 hsh)
            (repList_heapMono₂ _ repIxonAddressRef_heapMono₂ ext13 hrefs)
            (repList_heapMono₂ _ repIxonAddressRef_heapMono₂ ext13 hrecs)
            (repList_heapMono₂ _ repUnivPtr_heapMono₂ ext13 hunivs)
            (htbl.mono ext13)
            (repList_heapMono₂ _ repBinderNode_heapMono₂ ext13 hns0)
            (fun nd hnd => hplt nd (List.mem_cons_of_mem _ hnd))
            hbt (fun h0 => (hraw_t h0).mono ext3 (fun _ hm => hm)) br_t
        have ext14 := ext13.trans ext4
        obtain ⟨ext5, ns2, blobs_bb, hns2, hplt2, hhp_bb, hraw_b2⟩ :=
          branch_spec hcs5 hpre_b (bodyRep.mono ext14) (RepShareVec.mono ext14 hsh)
            (repList_heapMono₂ _ repIxonAddressRef_heapMono₂ ext14 hrefs)
            (repList_heapMono₂ _ repIxonAddressRef_heapMono₂ ext14 hrecs)
            (repList_heapMono₂ _ repUnivPtr_heapMono₂ ext14 hunivs)
            (htbl.mono ext14) hns1 hplt1
            hbb (fun h0 => (hraw_b h0).mono ext4 (fun _ hm => hm)) br_b
        subst hr hh'
        have ext_fin := Heap.Extends.snoc m5 (.construct Core.kexprEnum "Forall" [x_kt2, x_kb2, x_l])
        let allBlobs := (blobs_t ++ blobs_bt) ++ (blobs_b ++ blobs_bb)
        have hhp_all : HashedPairs calls allBlobs :=
          HashedPairs.append
            (HashedPairs.append
              (hhp_t.sub (by rw [hcs]; intro c hc; simp [hc]))
              (hhp_bt.sub (by rw [hcs]; intro c hc; simp [hc])))
            (HashedPairs.append
              (hhp_b.sub (by rw [hcs]; intro c hc; simp [hc]))
              (hhp_bb.sub (by rw [hcs]; intro c hc; simp [hc])))
        exact ⟨(ext14.trans ext5).trans ext_fin, _, x_n2, ns2, allBlobs, rfl,
          repList_heapMono₂ _ repBinderNode_heapMono₂ ext_fin hns2, hplt2, hhp_all,
          .all (hℓ.mono ((((ext2.trans ext3).trans ext4).trans ext5).trans ext_fin))
            (hraw_t2.mono (ext5.trans ext_fin) (fun _ hm => List.mem_append_left _ hm))
            (hraw_b2.mono ext_fin (fun _ hm => List.mem_append_right _ hm)) (by simp)⟩
      | _ => exact (Core.load_cell_ne ‹_› ld_e (by decide)).elim
    · -- Let
      cases hep with
      | letE cell tyRep valRep bodyRep =>
        have hxs := (Core.load_cell cell ld_e).2
        simp only [List.cons.injEq, and_true] at hxs; rcases hxs with ⟨_, rfl, rfl, rfl⟩
        obtain ⟨ext1, hpre_t, kt, bt, blobs_t, hbt, hrt, hhp_t, hraw_t⟩ :=
          convert_expr_spec hbound tyRep hsh hrefs hrecs hunivs ev_t
        simp only [Value.tuple.injEq, List.cons.injEq, and_true] at hrt; obtain ⟨rfl, rfl⟩ := hrt
        obtain ⟨ext2, hpre_v, kv, bv, blobs_v, hbv, hrv, hhp_v, hraw_v⟩ :=
          convert_expr_spec hbound (valRep.mono ext1) (RepShareVec.mono ext1 hsh)
            (repList_heapMono₂ _ repIxonAddressRef_heapMono₂ ext1 hrefs)
            (repList_heapMono₂ _ repIxonAddressRef_heapMono₂ ext1 hrecs)
            (repList_heapMono₂ _ repUnivPtr_heapMono₂ ext1 hunivs) ev_v
        simp only [Value.tuple.injEq, List.cons.injEq, and_true] at hrv; obtain ⟨rfl, rfl⟩ := hrv
        have ext12 := ext1.trans ext2
        obtain ⟨ext3, hpre_b, kb, bb, blobs_b, hbb, hrb, hhp_b, hraw_b⟩ :=
          convert_expr_spec hbound (bodyRep.mono ext12) (RepShareVec.mono ext12 hsh)
            (repList_heapMono₂ _ repIxonAddressRef_heapMono₂ ext12 hrefs)
            (repList_heapMono₂ _ repIxonAddressRef_heapMono₂ ext12 hrecs)
            (repList_heapMono₂ _ repUnivPtr_heapMono₂ ext12 hunivs) ev_b
        simp only [Value.tuple.injEq, List.cons.injEq, and_true] at hrb; obtain ⟨rfl, rfl⟩ := hrb
        have ext13 := ext12.trans ext3
        have hcs4 : cs4.length ≤ fuel + 1 := by
          rw [hcs] at hfuel; simp only [List.length_cons, List.length_append] at hfuel; omega
        have hcs5 : cs5.length ≤ fuel + 1 := by
          rw [hcs] at hfuel; simp only [List.length_cons, List.length_append] at hfuel; omega
        have hcs6 : cs6.length ≤ fuel + 1 := by
          rw [hcs] at hfuel; simp only [List.length_cons, List.length_append] at hfuel; omega
        obtain ⟨ext4, ns1, blobs_bt, hns1, hplt1, hhp_bt, hraw_t2⟩ :=
          branch_spec hcs4 hpre_t (tyRep.mono ext13) (RepShareVec.mono ext13 hsh)
            (repList_heapMono₂ _ repIxonAddressRef_heapMono₂ ext13 hrefs)
            (repList_heapMono₂ _ repIxonAddressRef_heapMono₂ ext13 hrecs)
            (repList_heapMono₂ _ repUnivPtr_heapMono₂ ext13 hunivs)
            (htbl.mono ext13)
            (repList_heapMono₂ _ repBinderNode_heapMono₂ ext13 hnodes) hplt
            hbt (fun h0 => (hraw_t h0).mono (ext2.trans ext3) (fun _ hm => hm)) br_t
        have ext14 := ext13.trans ext4
        obtain ⟨ext5, ns2, blobs_bv, hns2, hplt2, hhp_bv, hraw_v2⟩ :=
          branch_spec hcs5 hpre_v (valRep.mono ext14) (RepShareVec.mono ext14 hsh)
            (repList_heapMono₂ _ repIxonAddressRef_heapMono₂ ext14 hrefs)
            (repList_heapMono₂ _ repIxonAddressRef_heapMono₂ ext14 hrecs)
            (repList_heapMono₂ _ repUnivPtr_heapMono₂ ext14 hunivs)
            (htbl.mono ext14) hns1 hplt1
            hbv (fun h0 => (hraw_v h0).mono (ext3.trans ext4) (fun _ hm => hm)) br_v
        have ext15 := ext14.trans ext5
        obtain ⟨ext6, ns3, blobs_bb, hns3, hplt3, hhp_bb, hraw_b2⟩ :=
          branch_spec hcs6 hpre_b (bodyRep.mono ext15) (RepShareVec.mono ext15 hsh)
            (repList_heapMono₂ _ repIxonAddressRef_heapMono₂ ext15 hrefs)
            (repList_heapMono₂ _ repIxonAddressRef_heapMono₂ ext15 hrecs)
            (repList_heapMono₂ _ repUnivPtr_heapMono₂ ext15 hunivs)
            (htbl.mono ext15) hns2 hplt2
            hbb (fun h0 => (hraw_b h0).mono (ext4.trans ext5) (fun _ hm => hm)) br_b
        subst hr hh'
        have ext_fin := Heap.Extends.snoc m6 (.construct Core.kexprEnum "Let" [x_kt2, x_kv2, x_kb2])
        let allBlobs := ((blobs_t ++ blobs_bt) ++ (blobs_v ++ blobs_bv)) ++ (blobs_b ++ blobs_bb)
        have hhp_all : HashedPairs calls allBlobs :=
          HashedPairs.append
            (HashedPairs.append
              (HashedPairs.append
                (hhp_t.sub (by rw [hcs]; intro c hc; simp [hc]))
                (hhp_bt.sub (by rw [hcs]; intro c hc; simp [hc])))
              (HashedPairs.append
                (hhp_v.sub (by rw [hcs]; intro c hc; simp [hc]))
                (hhp_bv.sub (by rw [hcs]; intro c hc; simp [hc]))))
            (HashedPairs.append
              (hhp_b.sub (by rw [hcs]; intro c hc; simp [hc]))
              (hhp_bb.sub (by rw [hcs]; intro c hc; simp [hc])))
        exact ⟨(ext15.trans ext6).trans ext_fin, _, x_n3, ns3, allBlobs, rfl,
          repList_heapMono₂ _ repBinderNode_heapMono₂ ext_fin hns3, hplt3, hhp_all,
          .letE
            (hraw_t2.mono ((ext5.trans ext6).trans ext_fin)
              (fun _ hm => List.mem_append_left _ (List.mem_append_left _ hm)))
            (hraw_v2.mono (ext6.trans ext_fin)
              (fun _ hm => List.mem_append_left _ (List.mem_append_right _ hm)))
            (hraw_b2.mono ext_fin (fun _ hm => List.mem_append_right _ hm)) (by simp)⟩
      | _ => exact (Core.load_cell_ne ‹_› ld_e (by decide)).elim
    · -- Prj
      cases hep with
      | prj (tIdx := tIdx) (fIdx := fIdx) cell valRep =>
        have hxs := (Core.load_cell cell ld_e).2
        simp only [List.cons.injEq, and_true] at hxs; rcases hxs with ⟨rfl, rfl, rfl⟩
        cases hpre with
        | prj hpre_in =>
          obtain ⟨ht_lt, hv_tidx, hm1⟩ :=
            Lib.u64_to_field_spec (Deserialize.repU64_u64Value h tIdx) ev_tf
          subst hv_tidx hm1
          obtain ⟨hm2, a, d, href_get, hd_eq, ha_rep⟩ := lookup_addr_spec ht_lt hrefs ev_lk
          subst hm2
          have hcs3 : cs3.length ≤ fuel := by
            rw [hcs] at hfuel; simp only [List.length_cons, List.length_append] at hfuel; omega
          obtain ⟨ext3, ki', n1', ns1, blobs_in, htup, hns1, hplt1, hhp_in, hraw_in⟩ :=
            ih hcs3 hbound hpre_in valRep hsh hrefs hrecs hunivs htbl hnodes hplt ev_in
          simp only [Value.tuple.injEq, List.cons.injEq, and_true] at htup; obtain ⟨rfl, rfl⟩ := htup
          obtain ⟨hf_lt, hv_fidx, hm4⟩ :=
            Lib.u64_to_field_spec (Deserialize.repU64_u64Value m3 fIdx) ev_ff
          subst hv_fidx hm4 hr hh'
          have ext_fin := Heap.Extends.snoc m3
            (.construct Core.kexprEnum "Proj" [x_taddr, .field (fIdx.toNat : F), ki'])
          exact ⟨ext3.trans ext_fin, _, n1', ns1, blobs_in, rfl,
            repList_heapMono₂ _ repBinderNode_heapMono₂ ext_fin hns1, hplt1,
            hhp_in.sub (by rw [hcs]; intro c hc; simp [hc]),
            .prj ht_lt hf_lt href_get hd_eq
              (Bytes.repAddressRef_heapMono₂ _ (ext3.trans ext_fin) ha_rep)
              (hraw_in.mono ext_fin (fun _ hm => hm)) (by simp)⟩
      | _ => exact (Core.load_cell_ne ‹_› ld_e (by decide)).elim
    · -- Share
      cases hep with
      | share (idx := idx) cell =>
        have hxs := (Core.load_cell cell ld_e).2
        simp only [List.cons.injEq, and_true] at hxs; subst hxs
        cases hpre with
        | share hidx_lt hsh_get hpre_s =>
          obtain ⟨hidx56, hx_n, hm1⟩ :=
            Lib.u64_to_field_spec (Deserialize.repU64_u64Value h idx) ev_nf
          subst hx_n hm1
          rw [← exprDrop_inst_eq] at ev_dr
          have hsh' : RepList (Instance.mk "Lists::Node" [.ptr (.named "Ixon::Expr" [])]).symbol
              RepExpr h sharing shPtr := by rwa [exprList_inst_eq]
          obtain ⟨_, hdrop, hm2⟩ := Lib.Lists.drop_spec idx.toNat
            (ZMod.val_cast_of_lt (by omega)) ev_dr hsh'
          subst hm2
          rw [exprList_inst_eq, exprListEnum_eq] at hdrop
          have hval_idx : ((idx.toNat : F).val) = idx.toNat := ZMod.val_cast_of_lt (by omega)
          rw [hval_idx] at hdrop
          obtain ⟨s', _, hdrop_eq, hs_rep, _⟩ := Core.RepList.cons_of_load hdrop ld_dr
          have hsh_get' : sharing[idx.toNat]? = some s' := by
            rw [← List.head?_drop, hdrop_eq]; rfl
          have hs_eq : s' = s := Option.some.inj (hsh_get'.symm.trans hsh_get)
          subst hs_eq
          have hnodes' := hnodes
          rw [binderNodeListEnum_eq] at hnodes'
          obtain ⟨nd0, ns1, rfl, hnd0, hns1⟩ := Core.RepList.cons_of_load hnodes' ld_nodes
          rw [← binderNodeListEnum_eq] at hns1
          cases hnd0 with
          | never _ => simp at hnode
          | zero _ => simp at hnode
          | ifAllZero _ _ => simp at hnode
          | undecided _ => simp at hnode
          | share var0 =>
            simp only [Value.construct.injEq, List.cons.injEq, true_and, and_true] at hnode
            subst hnode
            obtain ⟨_, hv_var, hm3⟩ :=
              Lib.u64_to_field_spec (Deserialize.repU64_u64Value h var0) ev_vf
            subst hv_var hm3
            obtain ⟨hm4, ns_entry, hns_entry, hplt_entry⟩ := binder_nodes_spec htbl ev_bn
            subst hm4
            obtain ⟨m_cb, cs_ca, x_k_cb, x_rest_cb, ev_ca, _, he_k, he_h, hc_cb⟩ :=
              «Convert::convert_block».obs ev_cb
            subst he_k he_h hr hh'
            have hcs_ca : cs_ca.length ≤ fuel := by
              rw [hcs, hc_cb] at hfuel
              simp only [List.length_cons, List.length_append] at hfuel
              omega
            obtain ⟨ext_ca, kp_s, _, _, blobs_s, htup_s, _, _, hhp_s, hraw_s⟩ :=
              ih hcs_ca (by omega) hpre_s hs_rep hsh hrefs hrecs hunivs htbl
                hns_entry hplt_entry ev_ca
            simp only [Value.tuple.injEq, List.cons.injEq, and_true] at htup_s
            obtain ⟨rfl, _⟩ := htup_s
            exact ⟨ext_ca, kp_s, x_n1, ns1, blobs_s, rfl,
              repList_heapMono₂ _ repBinderNode_heapMono₂ ext_ca hns1,
              (fun nd hnd => hplt nd (List.mem_cons_of_mem _ hnd)),
              hhp_s.sub (by rw [hcs, hc_cb]; intro c hc; simp [hc]),
              .share hidx_lt hsh_get hraw_s⟩
      | _ => exact (Core.load_cell_ne ‹_› ld_e (by decide)).elim

/-- `Convert::convert_annotated` converts an expression containing binders (pre-validated by
`PreShareOk`) into a `RawConvExpr` value and returns the remaining binder nodes. -/
theorem convert_annotated_spec {e : Ixon.Expr} {bound : Nat}
    {refs recurAddrs : List _root_.Address} {univs : List Ixon.Univ}
    {sharing : List Ixon.Expr} {ns : List Ixon.BinderNode}
    {ep shPtr refsPtr recPtr univsPtr tbl nodesPtr r : SourceValue F}
    {h h' : Heap F} {calls : List (Call F)}
    (hbound : bound < 4294967296)
    (hpre : PreShareOk sharing bound e)
    (hep : RepExpr h e ep)
    (hsh : RepShareVec h sharing shPtr)
    (hrefs : RepList addressListEnum RepIxonAddressRef h refs refsPtr)
    (hrecs : RepList addressListEnum RepIxonAddressRef h recurAddrs recPtr)
    (hunivs : RepList univListEnum RepUnivPtr h univs univsPtr)
    (htbl : RepBinderTree 4294967296 h tbl)
    (hnodes : RepList binderNodeListEnum RepBinderNode h ns nodesPtr)
    (hplt : ∀ nd ∈ ns, BinderNodeParamsLt 4294967296 nd)
    (ev : ObsFn W "Convert::convert_annotated"
      [ep, shPtr, .field (bound : F), refsPtr, recPtr, univsPtr, tbl, nodesPtr] h r h' calls) :
    Heap.Extends h h' ∧
    ∃ (kp nodesOut : SourceValue F) (ns' : List Ixon.BinderNode)
      (blobs : List (_root_.Address × ByteArray)),
      r = .tuple [kp, nodesOut] ∧
      RepList binderNodeListEnum RepBinderNode h' ns' nodesOut ∧
      (∀ nd ∈ ns', BinderNodeParamsLt 4294967296 nd) ∧
      HashedPairs calls blobs ∧
      RawConvExpr refs recurAddrs univs sharing blobs h' bound e kp :=
  convert_annotated_go calls.length (Nat.le_refl _) hbound hpre hep hsh hrefs hrecs hunivs
    htbl hnodes hplt ev

/-- `Convert::convert_block` converts a block's expression and checks that all its binder nodes
were consumed. -/
theorem convert_block_spec {e : Ixon.Expr} {bound : Nat}
    {refs recurAddrs : List _root_.Address} {univs : List Ixon.Univ}
    {sharing : List Ixon.Expr} {ns : List Ixon.BinderNode}
    {ep shPtr refsPtr recPtr univsPtr tbl nodesPtr r : SourceValue F}
    {h h' : Heap F} {calls : List (Call F)}
    (hbound : bound < 4294967296)
    (hpre : PreShareOk sharing bound e)
    (hep : RepExpr h e ep)
    (hsh : RepShareVec h sharing shPtr)
    (hrefs : RepList addressListEnum RepIxonAddressRef h refs refsPtr)
    (hrecs : RepList addressListEnum RepIxonAddressRef h recurAddrs recPtr)
    (hunivs : RepList univListEnum RepUnivPtr h univs univsPtr)
    (htbl : RepBinderTree 4294967296 h tbl)
    (hnodes : RepList binderNodeListEnum RepBinderNode h ns nodesPtr)
    (hplt : ∀ nd ∈ ns, BinderNodeParamsLt 4294967296 nd)
    (ev : ObsFn W "Convert::convert_block"
      [ep, shPtr, .field (bound : F), refsPtr, recPtr, univsPtr, tbl, nodesPtr] h r h' calls) :
    Heap.Extends h h' ∧ ∃ blobs : List (_root_.Address × ByteArray),
      HashedPairs calls blobs ∧
      RawConvExpr refs recurAddrs univs sharing blobs h' bound e r := by
  obtain ⟨m2, cs12, x_k, x_rest, ev14, _, he108, he109, hc110⟩ :=
    «Convert::convert_block».obs ev
  subst he108 he109
  obtain ⟨ext, kp, _, _, blobs, htup, _, _, hhp, hraw⟩ :=
    convert_annotated_spec hbound hpre hep hsh hrefs hrecs hunivs htbl hnodes hplt ev14
  simp only [Value.tuple.injEq, List.cons.injEq, and_true] at htup
  obtain ⟨rfl, _⟩ := htup
  exact ⟨ext, blobs, hhp.sub (by rw [hc110]; intro c hc; simp [hc]), hraw⟩

/-- `Convert::convert_root` converts a top-level expression of a record into a `RawConvExpr` at
bound `4294967295`. -/
theorem convert_root_spec {e : Ixon.Expr}
    {refs recurAddrs : List _root_.Address} {univs : List Ixon.Univ} {sharing : List Ixon.Expr}
    {ep shPtr refsPtr recPtr univsPtr tbl rIdx r : SourceValue F}
    {h h' : Heap F} {calls : List (Call F)}
    (hep : RepExpr h e ep)
    (hsh : RepShareVec h sharing shPtr)
    (hrefs : RepList addressListEnum RepIxonAddressRef h refs refsPtr)
    (hrecs : RepList addressListEnum RepIxonAddressRef h recurAddrs recPtr)
    (hunivs : RepList univListEnum RepUnivPtr h univs univsPtr)
    (htbl : RepBinderTree 4294967296 h tbl)
    (ev : ObsFn W "Convert::convert_root"
      [ep, shPtr, refsPtr, recPtr, univsPtr, tbl, rIdx] h r h' calls) :
    Heap.Extends h h' ∧ ∃ blobs : List (_root_.Address × ByteArray),
      HashedPairs calls blobs ∧
      RawConvExpr refs recurAddrs univs sharing blobs h' 4294967295 e r := by
  have hbnd : (4294967295 : Nat) < 4294967296 := by omega
  rcases «Convert::convert_root».obs ev with
    ⟨m2, cs12, x_k, ev14, he90, he91, hc92⟩ |
    ⟨m2, cs12, x_k, x_b, cs100, v110, m160, cs168, ev14, _, ev170, ev102, hc201⟩
  · have ev14' : ObsFn W "Convert::convert_expr"
        [ep, shPtr, .field ((4294967295 : Nat) : F), refsPtr, recPtr, univsPtr]
        h (.tuple [x_k, .field 0]) m2 cs12 := ev14
    subst he90 he91
    obtain ⟨ext, _, kp, b, blobs, hb, htup, hhp, hraw⟩ :=
      convert_expr_spec hbnd hep hsh hrefs hrecs hunivs ev14'
    simp only [Value.tuple.injEq, List.cons.injEq, and_true] at htup
    obtain ⟨rfl, hb0_eq⟩ := htup
    have hb0 : b = 0 := by rcases hb with rfl | rfl; · rfl; · simp at hb0_eq
    exact ⟨ext, blobs, hhp.sub (by rw [hc92]; intro c hc; simp [hc]), hraw hb0⟩
  · have ev14' : ObsFn W "Convert::convert_expr"
        [ep, shPtr, .field ((4294967295 : Nat) : F), refsPtr, recPtr, univsPtr]
        h (.tuple [x_k, x_b]) m2 cs12 := ev14
    obtain ⟨ext1, hpre, _, _, blobs1, _, _, hhp1, _⟩ :=
      convert_expr_spec hbnd hep hsh hrefs hrecs hunivs ev14'
    obtain ⟨hm160, ns, hns, hplt⟩ := binder_nodes_spec (htbl.mono ext1) ev170
    subst hm160
    have ev102' : ObsFn W "Convert::convert_block"
        [ep, shPtr, .field ((4294967295 : Nat) : F), refsPtr, recPtr, univsPtr, tbl, v110]
        m2 r h' cs100 := ev102
    obtain ⟨ext2, blobs2, hhp2, hraw2⟩ :=
      convert_block_spec hbnd hpre (hep.mono ext1) (RepShareVec.mono ext1 hsh)
        (repList_heapMono₂ _ repIxonAddressRef_heapMono₂ ext1 hrefs)
        (repList_heapMono₂ _ repIxonAddressRef_heapMono₂ ext1 hrecs)
        (repList_heapMono₂ _ repUnivPtr_heapMono₂ ext1 hunivs)
        (htbl.mono ext1) hns hplt ev102'
    refine ⟨ext1.trans ext2, blobs1 ++ blobs2,
      HashedPairs.append
        (hhp1.sub (by rw [hc201]; intro c hc; simp [hc]))
        (hhp2.sub (by rw [hc201]; intro c hc; simp [hc])),
      hraw2.mono (Heap.Extends.refl _) (fun _ hm => List.mem_append_right _ hm)⟩

/-! ## De Bruijn shifting / substitution congruence for `Annotates` -/

private theorem liftLooseBVars_comm {md : Ix.Kernel.Mode} (a₁ a₂ : Nat) :
    ∀ (e : Ix.Kernel.Expr md) (c₁ c₂ : Nat),
      c₁ ≤ c₂ →
      Ix.Kernel.Expr.liftLooseBVars a₁ c₁ (Ix.Kernel.Expr.liftLooseBVars a₂ c₂ e) =
        Ix.Kernel.Expr.liftLooseBVars a₂ (c₂ + a₁) (Ix.Kernel.Expr.liftLooseBVars a₁ c₁ e) := by
  intro e
  induction e with
  | bvar i =>
    intro c₁ c₂ hle
    by_cases h2 : c₂ ≤ i
    · have h1 : c₁ ≤ i := Nat.le_trans hle h2
      have h2' : c₂ + a₁ ≤ i + a₁ := by omega
      simp [Ix.Kernel.Expr.liftLooseBVars, h1, h2, h2', Nat.add_right_comm]
    · by_cases h1 : c₁ ≤ i
      · have h2' : ¬ (c₂ + a₁ ≤ i + a₁) := by omega
        simp [Ix.Kernel.Expr.liftLooseBVars, h1, h2, h2']
      · have h2' : ¬ (c₂ + a₁ ≤ i) := by omega
        simp [Ix.Kernel.Expr.liftLooseBVars, h1, h2, h2']
  | fvar _ _ _ => intro _ _ _; rfl
  | sort _ => intro _ _ _; rfl
  | const _ _ => intro _ _ _; rfl
  | lit _ => intro _ _ _; rfl
  | app f a ihf iha =>
    intro c₁ c₂ hle
    simp [Ix.Kernel.Expr.liftLooseBVars, ihf _ _ hle, iha _ _ hle]
  | lam ty body m iht ihb =>
    intro c₁ c₂ hle
    simp only [Ix.Kernel.Expr.liftLooseBVars, iht _ _ hle]
    rw [ihb (c₁ + 1) (c₂ + 1) (by omega), show c₂ + 1 + a₁ = c₂ + a₁ + 1 by omega]
  | forallE ty body m iht ihb =>
    intro c₁ c₂ hle
    simp only [Ix.Kernel.Expr.liftLooseBVars, iht _ _ hle]
    rw [ihb (c₁ + 1) (c₂ + 1) (by omega), show c₂ + 1 + a₁ = c₂ + a₁ + 1 by omega]
  | letE ty val body m iht ihv ihb =>
    intro c₁ c₂ hle
    simp only [Ix.Kernel.Expr.liftLooseBVars, iht _ _ hle, ihv _ _ hle]
    rw [ihb (c₁ + 1) (c₂ + 1) (by omega), show c₂ + 1 + a₁ = c₂ + a₁ + 1 by omega]
  | proj s i e ih =>
    intro c₁ c₂ hle
    simp [Ix.Kernel.Expr.liftLooseBVars, ih _ _ hle]

private theorem liftLooseBVars_add {md : Ix.Kernel.Mode} (a₁ a₂ : Nat) :
    ∀ (e : Ix.Kernel.Expr md) (c : Nat),
      Ix.Kernel.Expr.liftLooseBVars a₁ c (Ix.Kernel.Expr.liftLooseBVars a₂ c e) =
        Ix.Kernel.Expr.liftLooseBVars (a₂ + a₁) c e := by
  intro e
  induction e with
  | bvar i =>
    intro c
    by_cases hc : c ≤ i
    · have hc' : c ≤ i + a₂ := by omega
      simp [Ix.Kernel.Expr.liftLooseBVars, hc, hc', Nat.add_assoc]
    · simp [Ix.Kernel.Expr.liftLooseBVars, hc]
  | fvar _ _ _ | sort _ | const _ _ | lit _ => intro _; rfl
  | app f a ihf iha => intro c; simp [Ix.Kernel.Expr.liftLooseBVars, ihf, iha]
  | lam ty body m iht ihb => intro c; simp [Ix.Kernel.Expr.liftLooseBVars, iht, ihb]
  | forallE ty body m iht ihb => intro c; simp [Ix.Kernel.Expr.liftLooseBVars, iht, ihb]
  | letE ty val body m iht ihv ihb =>
    intro c; simp [Ix.Kernel.Expr.liftLooseBVars, iht, ihv, ihb]
  | proj s i e ih => intro c; simp [Ix.Kernel.Expr.liftLooseBVars, ih]

private theorem liftLooseBVars_instantiate1Lift {md : Ix.Kernel.Mode} (amount : Nat)
    (v : Ix.Kernel.Expr md) :
    ∀ (e : Ix.Kernel.Expr md) (d u : Nat),
      Ix.Kernel.Expr.liftLooseBVars amount (d + u) (e.instantiate1Lift v d) =
        (Ix.Kernel.Expr.liftLooseBVars amount (d + u + 1) e).instantiate1Lift
          (Ix.Kernel.Expr.liftLooseBVars amount u v) d := by
  intro e
  induction e with
  | bvar i =>
    intro d u
    by_cases hid : i = d
    · subst hid
      have hnc : ¬ (i + u + 1 ≤ i) := by omega
      simp only [Ix.Kernel.Expr.instantiate1Lift, ↓reduceIte, Ix.Kernel.Expr.liftLooseBVars, hnc]
      rw [Nat.add_comm i u, liftLooseBVars_comm amount i v 0 u (Nat.zero_le _), Nat.zero_add]
    · by_cases hgt : i > d
      · by_cases hge : d + u + 1 ≤ i
        · have hge' : d + u ≤ i - 1 := by omega
          have hne' : i + amount ≠ d := by omega
          have hgt' : i + amount > d := by omega
          simp only [Ix.Kernel.Expr.instantiate1Lift, hid, hgt, ↓reduceIte,
            Ix.Kernel.Expr.liftLooseBVars, hge, hge', hne', hgt']
          exact congrArg Ix.Kernel.Expr.bvar (by omega)
        · have hge' : ¬ (d + u ≤ i - 1) := by omega
          simp [Ix.Kernel.Expr.instantiate1Lift, hid, hgt, Ix.Kernel.Expr.liftLooseBVars, hge, hge']
      · have hge : ¬ (d + u + 1 ≤ i) := by omega
        have hge' : ¬ (d + u ≤ i) := by omega
        simp [Ix.Kernel.Expr.instantiate1Lift, hid, hgt, Ix.Kernel.Expr.liftLooseBVars, hge, hge']
  | fvar _ _ _ | sort _ | const _ _ | lit _ => intro _ _; rfl
  | app f a ihf iha =>
    intro d u
    simp [Ix.Kernel.Expr.instantiate1Lift, Ix.Kernel.Expr.liftLooseBVars, ihf, iha]
  | lam ty body m iht ihb =>
    intro d u
    simp only [Ix.Kernel.Expr.instantiate1Lift, Ix.Kernel.Expr.liftLooseBVars, iht]
    rw [show d + u + 1 = (d + 1) + u by omega, ihb (d + 1) u]
  | forallE ty body m iht ihb =>
    intro d u
    simp only [Ix.Kernel.Expr.instantiate1Lift, Ix.Kernel.Expr.liftLooseBVars, iht]
    rw [show d + u + 1 = (d + 1) + u by omega, ihb (d + 1) u]
  | letE ty val body m iht ihv ihb =>
    intro d u
    simp only [Ix.Kernel.Expr.instantiate1Lift, Ix.Kernel.Expr.liftLooseBVars, iht, ihv]
    rw [show d + u + 1 = (d + 1) + u by omega, ihb (d + 1) u]
  | proj s i e ih =>
    intro d u
    simp [Ix.Kernel.Expr.instantiate1Lift, Ix.Kernel.Expr.liftLooseBVars, ih]

private theorem instantiate1Lift_liftLooseBVars_above {md : Ix.Kernel.Mode}
    (v : Ix.Kernel.Expr md) (k : Nat) :
    ∀ (e : Ix.Kernel.Expr md) (c : Nat),
      (Ix.Kernel.Expr.liftLooseBVars (k + 1) c e).instantiate1Lift v (c + k) =
        Ix.Kernel.Expr.liftLooseBVars k c e := by
  intro e
  induction e with
  | bvar i =>
    intro c
    by_cases hc : c ≤ i
    · have hne : i + (k + 1) ≠ c + k := by omega
      have hgt : i + (k + 1) > c + k := by omega
      simp only [Ix.Kernel.Expr.liftLooseBVars, hc, ↓reduceIte,
        Ix.Kernel.Expr.instantiate1Lift, hne, hgt]
      exact congrArg Ix.Kernel.Expr.bvar (by omega)
    · have hne : i ≠ c + k := by omega
      have hgt : ¬ (i > c + k) := by omega
      simp [Ix.Kernel.Expr.liftLooseBVars, hc, Ix.Kernel.Expr.instantiate1Lift, hne, hgt]
  | fvar _ _ _ | sort _ | const _ _ | lit _ => intro _; rfl
  | app f a ihf iha =>
    intro c; simp [Ix.Kernel.Expr.liftLooseBVars, Ix.Kernel.Expr.instantiate1Lift, ihf, iha]
  | lam ty body m iht ihb =>
    intro c
    simp only [Ix.Kernel.Expr.liftLooseBVars, Ix.Kernel.Expr.instantiate1Lift, iht]
    rw [show c + k + 1 = (c + 1) + k by omega, ihb (c + 1)]
  | forallE ty body m iht ihb =>
    intro c
    simp only [Ix.Kernel.Expr.liftLooseBVars, Ix.Kernel.Expr.instantiate1Lift, iht]
    rw [show c + k + 1 = (c + 1) + k by omega, ihb (c + 1)]
  | letE ty val body m iht ihv ihb =>
    intro c
    simp only [Ix.Kernel.Expr.liftLooseBVars, Ix.Kernel.Expr.instantiate1Lift, iht, ihv]
    rw [show c + k + 1 = (c + 1) + k by omega, ihb (c + 1)]
  | proj s i e ih =>
    intro c; simp [Ix.Kernel.Expr.liftLooseBVars, Ix.Kernel.Expr.instantiate1Lift, ih]

private theorem instantiate1Lift_liftLooseBVars_comm {md : Ix.Kernel.Mode}
    (v : Ix.Kernel.Expr md) (k : Nat) :
    ∀ (w : Ix.Kernel.Expr md) (c u : Nat),
      (Ix.Kernel.Expr.liftLooseBVars k c w).instantiate1Lift v (c + k + u) =
        Ix.Kernel.Expr.liftLooseBVars k c (w.instantiate1Lift v (c + u)) := by
  intro w
  induction w with
  | bvar j =>
    intro c u
    by_cases hju : j = c + u
    · subst hju
      have hc : c ≤ c + u := by omega
      have heq : c + u + k = c + k + u := by omega
      simp only [Ix.Kernel.Expr.liftLooseBVars, hc, ↓reduceIte,
        Ix.Kernel.Expr.instantiate1Lift, heq]
      rw [← liftLooseBVars_comm k (c + u) v 0 c (Nat.zero_le _), liftLooseBVars_add]
    · by_cases hgt : j > c + u
      · have hc : c ≤ j := by omega
        have hc' : c ≤ j - 1 := by omega
        have hne' : j + k ≠ c + k + u := by omega
        have hgt' : j + k > c + k + u := by omega
        simp only [Ix.Kernel.Expr.liftLooseBVars, hc, ↓reduceIte,
          Ix.Kernel.Expr.instantiate1Lift, hju, hgt, hc', hne', hgt']
        exact congrArg Ix.Kernel.Expr.bvar (by omega)
      · by_cases hc : c ≤ j
        · have hne' : j + k ≠ c + k + u := by omega
          have hgt' : ¬ (j + k > c + k + u) := by omega
          simp [Ix.Kernel.Expr.liftLooseBVars, hc, Ix.Kernel.Expr.instantiate1Lift,
            hju, hgt, hne', hgt']
        · have hne' : j ≠ c + k + u := by omega
          have hgt' : ¬ (j > c + k + u) := by omega
          simp [Ix.Kernel.Expr.liftLooseBVars, hc, Ix.Kernel.Expr.instantiate1Lift,
            hju, hgt, hne', hgt']
  | fvar _ _ _ | sort _ | const _ _ | lit _ => intro _ _; rfl
  | app f a ihf iha =>
    intro c u; simp [Ix.Kernel.Expr.liftLooseBVars, Ix.Kernel.Expr.instantiate1Lift, ihf, iha]
  | lam ty body m iht ihb =>
    intro c u
    simp only [Ix.Kernel.Expr.liftLooseBVars, Ix.Kernel.Expr.instantiate1Lift, iht]
    rw [show c + k + u + 1 = (c + 1) + k + u by omega,
      show c + u + 1 = (c + 1) + u by omega, ihb (c + 1) u]
  | forallE ty body m iht ihb =>
    intro c u
    simp only [Ix.Kernel.Expr.liftLooseBVars, Ix.Kernel.Expr.instantiate1Lift, iht]
    rw [show c + k + u + 1 = (c + 1) + k + u by omega,
      show c + u + 1 = (c + 1) + u by omega, ihb (c + 1) u]
  | letE ty val body m iht ihv ihb =>
    intro c u
    simp only [Ix.Kernel.Expr.liftLooseBVars, Ix.Kernel.Expr.instantiate1Lift, iht, ihv]
    rw [show c + k + u + 1 = (c + 1) + k + u by omega,
      show c + u + 1 = (c + 1) + u by omega, ihb (c + 1) u]
  | proj s i e ih =>
    intro c u; simp [Ix.Kernel.Expr.liftLooseBVars, Ix.Kernel.Expr.instantiate1Lift, ih]

private theorem instantiate1Lift_comm {md : Ix.Kernel.Mode} (w v : Ix.Kernel.Expr md) :
    ∀ (e : Ix.Kernel.Expr md) (k u : Nat),
      (e.instantiate1Lift w k).instantiate1Lift v (k + u) =
        (e.instantiate1Lift v (k + 1 + u)).instantiate1Lift (w.instantiate1Lift v u) k := by
  intro e
  induction e with
  | bvar i =>
    intro k u
    by_cases hik : i = k
    · subst hik
      have hne : i ≠ i + 1 + u := by omega
      have hgt : ¬ (i > i + 1 + u) := by omega
      simp only [Ix.Kernel.Expr.instantiate1Lift, ↓reduceIte, hne, hgt]
      have hcomm := instantiate1Lift_liftLooseBVars_comm v i w 0 u
      simpa using hcomm
    · by_cases hgt : i > k
      · by_cases hiu : i = k + 1 + u
        · subst hiu
          have heq1 : k + 1 + u - 1 = k + u := by omega
          simp only [Ix.Kernel.Expr.instantiate1Lift, hik, hgt, ↓reduceIte, heq1]
          have habove := instantiate1Lift_liftLooseBVars_above (w.instantiate1Lift v u) (k + u) v 0
          rw [Nat.zero_add, show k + u + 1 = k + 1 + u by omega] at habove
          have hcomm := liftLooseBVars_comm k u v 0 0 (Nat.le_refl _)
          -- Direct equality `liftLooseBVars (k + u) 0 v` on both sides
          exact habove.symm
        · by_cases hgtu : i > k + 1 + u
          · have hne1 : i - 1 ≠ k + u := by omega
            have hgt1 : i - 1 > k + u := by omega
            have hne2 : i - 1 ≠ k := by omega
            have hgt2 : i - 1 > k := by omega
            simp [Ix.Kernel.Expr.instantiate1Lift, hik, hgt, hiu, hgtu, hne1, hgt1, hne2, hgt2]
          · have hne1 : i - 1 ≠ k + u := by omega
            have hgt1 : ¬ (i - 1 > k + u) := by omega
            simp [Ix.Kernel.Expr.instantiate1Lift, hik, hgt, hiu, hgtu, hne1, hgt1]
      · have hne1 : i ≠ k + u := by omega
        have hgt1 : ¬ (i > k + u) := by omega
        have hne2 : i ≠ k + 1 + u := by omega
        have hgt2 : ¬ (i > k + 1 + u) := by omega
        simp [Ix.Kernel.Expr.instantiate1Lift, hik, hgt, hne1, hgt1, hne2, hgt2]
  | fvar _ _ _ | sort _ | const _ _ | lit _ => intro _ _; rfl
  | app f a ihf iha =>
    intro k u; simp [Ix.Kernel.Expr.instantiate1Lift, ihf, iha]
  | lam ty body m iht ihb =>
    intro k u
    simp only [Ix.Kernel.Expr.instantiate1Lift, iht]
    rw [show k + u + 1 = (k + 1) + u by omega,
      show k + 1 + u + 1 = (k + 1) + 1 + u by omega, ihb (k + 1) u]
  | forallE ty body m iht ihb =>
    intro k u
    simp only [Ix.Kernel.Expr.instantiate1Lift, iht]
    rw [show k + u + 1 = (k + 1) + u by omega,
      show k + 1 + u + 1 = (k + 1) + 1 + u by omega, ihb (k + 1) u]
  | letE ty val body m iht ihv ihb =>
    intro k u
    simp only [Ix.Kernel.Expr.instantiate1Lift, iht, ihv]
    rw [show k + u + 1 = (k + 1) + u by omega,
      show k + 1 + u + 1 = (k + 1) + 1 + u by omega, ihb (k + 1) u]
  | proj s i e ih =>
    intro k u; simp [Ix.Kernel.Expr.instantiate1Lift, ih]

/-- `Annotates` is preserved by `Expr.liftLooseBVars`. -/
theorem annotates_liftLooseBVars {e' e : Core.KExpr} (h : IxVM.Consistency.Annotates e' e) :
    ∀ amount c,
      IxVM.Consistency.Annotates
        (Ix.Kernel.Expr.liftLooseBVars amount c e')
        (Ix.Kernel.Expr.liftLooseBVars amount c e) := by
  induction h with
  | bvar => intro amount c; simp only [Ix.Kernel.Expr.liftLooseBVars]; split <;> exact .bvar
  | fvar _ ih => intro amount c; exact .fvar (ih amount c)
  | sort => intro _ _; exact .sort
  | const => intro _ _; exact .const
  | lit => intro _ _; exact .lit
  | app _ _ ihf iha => intro amount c; exact .app (ihf amount c) (iha amount c)
  | lam _ _ iht ihb => intro amount c; exact .lam (iht amount c) (ihb amount (c + 1))
  | forallE _ _ iht ihb => intro amount c; exact .forallE (iht amount c) (ihb amount (c + 1))
  | proj _ ih => intro amount c; exact .proj (ih amount c)
  | @letE _ ty v b m _ ih =>
    intro amount c
    apply IxVM.Consistency.Annotates.letE
    have hcomm := liftLooseBVars_instantiate1Lift amount v b 0 c
    rw [Nat.zero_add] at hcomm
    rw [← hcomm]
    exact ih amount c

/-- `Annotates` is preserved by `Expr.instantiate1Lift`. -/
theorem annotates_instantiate1Lift {b' b v' v : Core.KExpr}
    (hb : IxVM.Consistency.Annotates b' b)
    (hv : IxVM.Consistency.Annotates v' v) :
    ∀ d, IxVM.Consistency.Annotates (b'.instantiate1Lift v' d) (b.instantiate1Lift v d) := by
  induction hb with
  | @bvar i =>
    intro d
    simp only [Ix.Kernel.Expr.instantiate1Lift]
    by_cases hid : i = d
    · simp only [hid, ↓reduceIte]
      exact annotates_liftLooseBVars hv d 0
    · by_cases hgt : i > d
      · simp [hid, hgt]; exact .bvar
      · simp [hid, hgt]; exact .bvar
  | fvar hty => intro _; exact .fvar hty
  | sort => intro _; exact .sort
  | const => intro _; exact .const
  | lit => intro _; exact .lit
  | app _ _ ihf iha => intro d; exact .app (ihf d) (iha d)
  | lam _ _ iht ihb => intro d; exact .lam (iht d) (ihb (d + 1))
  | forallE _ _ iht ihb => intro d; exact .forallE (iht d) (ihb (d + 1))
  | proj _ ih => intro d; exact .proj (ih d)
  | @letE _ ty w body m _ ih =>
    intro d
    apply IxVM.Consistency.Annotates.letE
    have hcomm := instantiate1Lift_comm w v body 0 d
    rw [Nat.zero_add, show 0 + 1 + d = d + 1 by omega] at hcomm
    rw [← hcomm]
    exact ih d

/-! ## Bridge from `RawConvExpr` to `Reader.convExpr`, `Annotates`, `posOf`, and `Tm` / `TmC` -/

/-- Pure specification of the sharing table built by `MemberReader.mk'`. -/
def buildShareTblGo (ecx : Ix.Kernel.Reader.ECx .anon)
    (acc : Array (Ix.Kernel.Reader.ReadM Core.KExpr)) :
    List Ixon.Expr → Array (Ix.Kernel.Reader.ReadM Core.KExpr)
  | [] => acc
  | e :: es => buildShareTblGo ecx (acc.push (Ix.Kernel.Reader.convExpr ecx acc e)) es

def buildShareTbl (ecx : Ix.Kernel.Reader.ECx .anon) (es : List Ixon.Expr) :
    Array (Ix.Kernel.Reader.ReadM Core.KExpr) :=
  buildShareTblGo ecx #[] es

private theorem buildShareTblGo_size (ecx : Ix.Kernel.Reader.ECx .anon) :
    ∀ (es : List Ixon.Expr) (acc : Array (Ix.Kernel.Reader.ReadM Core.KExpr)),
      (buildShareTblGo ecx acc es).size = acc.size + es.length
  | [], acc => by simp [buildShareTblGo]
  | e :: es, acc => by
    simp only [buildShareTblGo, buildShareTblGo_size ecx es, Array.size_push, List.length_cons]
    omega

private theorem buildShareTblGo_prefix (ecx : Ix.Kernel.Reader.ECx .anon) :
    ∀ (es : List Ixon.Expr) (acc : Array (Ix.Kernel.Reader.ReadM Core.KExpr)) (i : Nat)
      (hi : i < acc.size),
      (buildShareTblGo ecx acc es)[i]? = acc[i]?
  | [], _, _, _ => rfl
  | e :: es, acc, i, hi => by
    simp only [buildShareTblGo]
    rw [buildShareTblGo_prefix ecx es _ i (by simp; omega)]
    rw [Array.getElem?_push, if_neg (by omega)]

private theorem buildShareTblGo_append (ecx : Ix.Kernel.Reader.ECx .anon) :
    ∀ (es₁ es₂ : List Ixon.Expr) (acc : Array (Ix.Kernel.Reader.ReadM Core.KExpr)),
      buildShareTblGo ecx acc (es₁ ++ es₂) =
        buildShareTblGo ecx (buildShareTblGo ecx acc es₁) es₂
  | [], _, _ => rfl
  | _ :: es₁, es₂, acc => buildShareTblGo_append ecx es₁ es₂ _

theorem buildShareTbl_size (ecx : Ix.Kernel.Reader.ECx .anon) (es : List Ixon.Expr) :
    (buildShareTbl ecx es).size = es.length := by
  simpa [buildShareTbl] using buildShareTblGo_size ecx es #[]

theorem buildShareTbl_take_getElem? (ecx : Ix.Kernel.Reader.ECx .anon)
    (sharing : List Ixon.Expr) {n i : Nat} {s : Ixon.Expr}
    (hi_n : i < n) (hsh : sharing[i]? = some s) :
    (buildShareTbl ecx (sharing.take n))[i]? =
      some (Ix.Kernel.Reader.convExpr ecx (buildShareTbl ecx (sharing.take i)) s) := by
  have hi_len : i < sharing.length := List.getElem?_eq_some_iff.mp ⟨s, hsh⟩ |>.1
  have htake_split : sharing.take n =
      sharing.take i ++ (s :: (sharing.drop (i + 1)).take (n - 1 - i)) := by
    have h1 : sharing.take n = (sharing.take i ++ sharing.drop i).take n := by
      rw [List.take_append_drop]
    have hdrop_cons : sharing.drop i = s :: sharing.drop (i + 1) := by
      rw [List.drop_eq_getElem_cons hi_len]
      have hs_eq : sharing[i] = s := Option.some.inj ((List.getElem?_eq_getElem hi_len).symm.trans hsh)
      rw [hs_eq]
    rw [h1, hdrop_cons, List.take_append]
    simp only [List.length_take, Nat.min_eq_left (Nat.le_of_lt hi_len)]
    have hsub : n - i = (n - 1 - i) + 1 := by omega
    rw [List.take_of_le (by simp; omega), hsub, List.take_succ_cons]
  unfold buildShareTbl
  rw [htake_split, buildShareTblGo_append]
  simp only [buildShareTblGo]
  have hsz_i : (buildShareTblGo ecx #[] (sharing.take i)).size = i := by
    rw [buildShareTblGo_size]; simp [Nat.min_eq_left (Nat.le_of_lt hi_len)]
  rw [buildShareTblGo_prefix ecx _ _ i (by simp [hsz_i])]
  rw [Array.getElem?_push, if_pos hsz_i.symm]

/-- `MemberReader.mk'` builds `buildShareTbl mr.ecx src.sharing.toList`. -/
theorem memberReader_mk'_eq (cx : Ix.Kernel.Reader.Ctx .anon) (src : Ixon.Constant)
    (param : Nat → Ix.Kernel.LevelParam)
    (self : Nat → Option (Ix.Kernel.Reader.ReadM Core.KKey)) :
    let mr := Ix.Kernel.Reader.MemberReader.mk' cx src param self
    mr.ecx = ⟨cx, src, src.univs.map (Ix.Kernel.Reader.convUniv param), self⟩ ∧
    mr.tbl = buildShareTbl
      ⟨cx, src, src.univs.map (Ix.Kernel.Reader.convUniv param), self⟩
      src.sharing.toList := by
  refine ⟨rfl, ?_⟩
  show Id.run _ = _
  -- `for entry in src.sharing` over `Array` lowers to `Array.forIn` = `List.foldl`
  have hfold : ∀ (es : List Ixon.Expr) (acc : Array (Ix.Kernel.Reader.ReadM Core.KExpr)),
      es.foldl (fun tbl entry =>
        tbl.push (Ix.Kernel.Reader.convExpr
          ⟨cx, src, src.univs.map (Ix.Kernel.Reader.convUniv param), self⟩ tbl entry)) acc =
        buildShareTblGo
          ⟨cx, src, src.univs.map (Ix.Kernel.Reader.convUniv param), self⟩ acc es := by
    intro es
    induction es with
    | nil => intro _; rfl
    | cons e es ih => intro acc; simp [List.foldl, buildShareTblGo, ih]
  unfold Ix.Kernel.Reader.MemberReader.mk' buildShareTbl
  simp [ Array.mkEmpty, hfold ]

private theorem except_bind_eq_ok {ε α β : Type} {m : Except ε α} {f : α → Except ε β} {b : β}
    (h : (m >>= f) = .ok b) : ∃ a, m = .ok a ∧ f a = .ok b := by
  cases m with
  | error e => simp [bind, Except.bind] at h
  | ok a => exact ⟨a, rfl, h⟩

private theorem levels_conv_bridge {ps : List Ix.Kernel.LevelParam}
    (hperm : ps.Perm (List.range ps.length)) (hps_lt : ps.length < 4294967296)
    {univs : List Ixon.Univ} {ecx : Ix.Kernel.Reader.ECx .anon}
    (hunivs : ecx.univs = univs.toArray.map (Ix.Kernel.Reader.convUniv (Ix.Kernel.Reader.recParam ps)))
    {idxs : List UInt64} {ls_id ls_rd : List Core.KLevel}
    (hls_id : idxs.mapM (fun i => univs[i.toNat]?.map (Ix.Kernel.Reader.convUniv id)) = some ls_id)
    (hls_rd : idxs.mapM ecx.level = .ok ls_rd)
    (hdef : ls_rd.all (Ix.Kernel.Level.allParamsDefined ps) = true) :
    ls_rd.map (Ix.Kernel.Level.subst ps (Core.posLevels ps)) = ls_id ∧
    ∀ l ∈ ls_id, KernelLevels.ParamsLt 4294967296 l := by
  induction idxs generalizing ls_id ls_rd with
  | nil =>
    simp only [List.mapM_nil, Option.some.injEq] at hls_id
    have hrd_nil : ls_rd = [] := by
      cases hls_rd; rfl
    subst hls_id hrd_nil
    exact ⟨rfl, fun _ h => nomatch h⟩
  | cons i rest ih =>
    simp only [List.mapM_cons, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hls_id
    obtain ⟨l1, ⟨u, hu_get, rfl⟩, ls_id_rest, hrest_id, rfl⟩ := hls_id
    simp only [List.mapM_cons] at hls_rd
    obtain ⟨l_rd1, hl_rd1, hbind_rest⟩ := except_bind_eq_ok hls_rd
    obtain ⟨ls_rd_rest, hrest_rd, hret⟩ := except_bind_eq_ok hbind_rest
    injection hret with hls_rd_eq; subst hls_rd_eq
    have hl_rd1_eq : l_rd1 = Ix.Kernel.Reader.convUniv (Ix.Kernel.Reader.recParam ps) u := by
      unfold Ix.Kernel.Reader.ECx.level at hl_rd1
      rw [hunivs] at hl_rd1
      have hget_arr : (univs.toArray.map (Ix.Kernel.Reader.convUniv (Ix.Kernel.Reader.recParam ps)))[i.toNat]? =
          some (Ix.Kernel.Reader.convUniv (Ix.Kernel.Reader.recParam ps) u) := by
        simp [hu_get]
      rw [hget_arr] at hl_rd1
      injection hl_rd1
    subst hl_rd1_eq
    simp only [List.all_cons, Bool.and_eq_true] at hdef
    obtain ⟨heq1, hplt1⟩ := convUniv_posOf_eq hperm hps_lt hdef.1
    obtain ⟨heq_rest, hplt_rest⟩ := ih hrest_id hrest_rd hdef.2
    refine ⟨by simp [heq1, heq_rest], ?_⟩
    intro l hl
    rcases List.mem_cons.mp hl with rfl | hmem
    · exact hplt1
    · exact hplt_rest l hmem

/-- **Master expression bridge (`RawConvExpr.toTm`)**: if `Reader.convExpr` succeeds on `e`
producing `E_rd` with loose bound variables below `k` and level parameters in `ps`, then `kp`
represents `Core.posOf ps E'` (`Tm κ d Γ h k (Core.posOf ps E') kp`) for an expression `E'`
satisfying `Annotates E' E_rd`. -/
theorem RawConvExpr.toTm {κ : _root_.Address → Core.KKey}
    {ps : List Ix.Kernel.LevelParam}
    (hperm : ps.Perm (List.range ps.length)) (hps_lt : ps.length < 4294967296)
    {refs recurAddrs : List _root_.Address} {univs : List Ixon.Univ}
    {sharing : List Ixon.Expr} {blobs : List (_root_.Address × ByteArray)}
    {ecx : Ix.Kernel.Reader.ECx .anon}
    (hrefs : ecx.src.refs.toList = refs)
    (hunivs : ecx.univs = univs.toArray.map (Ix.Kernel.Reader.convUniv (Ix.Kernel.Reader.recParam ps)))
    (hkeyAt : ∀ a k, ecx.cx.keyAt a = .ok k → k = κ a)
    (hself : ∀ i a m k, recurAddrs[i]? = some a → ecx.self i = some m → m = .ok k → k = κ a)
    (hblob : ∀ a bs, (a, bs) ∈ blobs → ecx.cx.blob a = some bs)
    {h : Heap F} {bound : Nat} {e : Ixon.Expr} {kp : SourceValue F}
    (raw : RawConvExpr refs recurAddrs univs sharing blobs h bound e kp) :
    ∀ {n k : Nat} {E_rd : Core.KExpr},
      n ≤ sharing.length →
      min bound sharing.length ≤ n →
      Ix.Kernel.Reader.convExpr ecx (buildShareTbl ecx (sharing.take n)) e = .ok E_rd →
      E_rd.looseBVarsBounded k = true →
      E_rd.allLevelParamsDefined ps = true →
      ∃ E' : Core.KExpr,
        IxVM.Consistency.Annotates E' E_rd ∧
        ∀ d Γ, Core.Tm κ d Γ h k (Core.posOf ps E') kp := by
  induction raw with
  | @var bound addr idx hidx cell =>
    intro n k E_rd _ _ hconv hlbb _
    simp only [Ix.Kernel.Reader.convExpr, pure, Except.pure, Except.ok.injEq,
      Ix.Kernel.Expr.mkBvar_eq] at hconv
    subst hconv
    simp only [Ix.Kernel.Expr.looseBVarsBounded, decide_eq_true_eq] at hlbb
    refine ⟨.bvar idx.toNat, .bvar, fun d Γ => ?_⟩
    have hval : ZMod.val (idx.toNat : F) = idx.toNat := ZMod.val_cast_of_lt (by omega)
    have htm : Core.Tm κ d Γ h k (.bvar (ZMod.val (idx.toNat : F)))
        (.ptr (.enum Core.kexprEnum) addr) :=
      .bvarLocal cell (by rw [hval]; omega) (by rw [hval]; exact hlbb)
    rwa [hval] at htm
  | @sort bound addr uIdx u lp huIdx hu rl cell =>
    intro n k E_rd _ _ hconv _ hdef
    simp only [Ix.Kernel.Reader.convExpr] at hconv
    obtain ⟨u_rd, hu_rd, hret⟩ := except_bind_eq_ok hconv
    injection hret with hE; subst hE
    have hu_eq : u_rd = Ix.Kernel.Reader.convUniv (Ix.Kernel.Reader.recParam ps) u := by
      unfold Ix.Kernel.Reader.ECx.level at hu_rd
      rw [hunivs] at hu_rd
      have hget : (univs.toArray.map (Ix.Kernel.Reader.convUniv (Ix.Kernel.Reader.recParam ps)))[uIdx.toNat]? =
          some (Ix.Kernel.Reader.convUniv (Ix.Kernel.Reader.recParam ps) u) := by
        simp [hu]
      rw [hget] at hu_rd
      injection hu_rd
    subst hu_eq
    simp only [Ix.Kernel.Expr.allLevelParamsDefined] at hdef
    obtain ⟨hpos_eq, hplt⟩ := convUniv_posOf_eq hperm hps_lt hdef
    refine ⟨.sort (Ix.Kernel.Reader.convUniv (Ix.Kernel.Reader.recParam ps) u), .sort, fun d Γ => ?_⟩
    unfold Core.posOf Ix.Kernel.Expr.instantiateLevelParams
    rw [hpos_eq]
    exact .sort cell (rl.toRepKLevel hplt) (Core.LvEq.refl _)
  | @ref bound addr rIdx uIdxs a d ap lsp ls hrIdx href hd ra hls rls cell =>
    intro n k E_rd _ _ hconv _ hdef
    simp only [Ix.Kernel.Reader.convExpr] at hconv
    obtain ⟨k_rd, hk_rd, hbind2⟩ := except_bind_eq_ok hconv
    obtain ⟨ls_rd, hls_rd, hret⟩ := except_bind_eq_ok hbind2
    injection hret with hE; subst hE
    have hk_eq : k_rd = κ a := by
      unfold Ix.Kernel.Reader.ECx.keyAt at hk_rd
      have href_arr : ecx.src.refs[rIdx.toNat]? = some a := by
        rw [← Array.getElem?_toList, hrefs, href]
      rw [href_arr] at hk_rd
      exact hkeyAt a k_rd hk_rd
    subst hk_eq
    simp only [Ix.Kernel.Expr.allLevelParamsDefined] at hdef
    obtain ⟨hpos_ls, hplt_ls⟩ :=
      levels_conv_bridge hperm hps_lt hunivs hls hls_rd hdef
    refine ⟨.const (κ a) ls_rd, .const, fun d0 Γ => ?_⟩
    unfold Core.posOf Ix.Kernel.Expr.instantiateLevelParams
    rw [hpos_ls, ← hd]
    exact .const cell ra (rls.toRepKLevelList hplt_ls) (Core.LvEqList.refl _)
  | @recur bound addr rIdx uIdxs a d ap lsp ls hrIdx hrec hd ra hls rls cell =>
    intro n k E_rd _ _ hconv _ hdef
    simp only [Ix.Kernel.Reader.convExpr] at hconv
    cases hself_opt : ecx.self rIdx.toNat with
    | none => simp [hself_opt, Ix.Kernel.Reader.malformed, throw, Except.error] at hconv
    | some m_self =>
      simp only [hself_opt] at hconv
      obtain ⟨k_rd, hk_rd, hbind2⟩ := except_bind_eq_ok hconv
      obtain ⟨ls_rd, hls_rd, hret⟩ := except_bind_eq_ok hbind2
      injection hret with hE; subst hE
      have hk_eq : k_rd = κ a := hself rIdx.toNat a m_self k_rd hrec hself_opt hk_rd
      subst hk_eq
      simp only [Ix.Kernel.Expr.allLevelParamsDefined] at hdef
      obtain ⟨hpos_ls, hplt_ls⟩ :=
        levels_conv_bridge hperm hps_lt hunivs hls hls_rd hdef
      refine ⟨.const (κ a) ls_rd, .const, fun d0 Γ => ?_⟩
      unfold Core.posOf Ix.Kernel.Expr.instantiateLevelParams
      rw [hpos_ls, ← hd]
      exact .const cell ra (rls.toRepKLevelList hplt_ls) (Core.LvEqList.refl _)
  | @prj bound addr tIdx fIdx inner a d ap ip htIdx hfIdx href hd ra _ cell ih =>
    intro n k E_rd hn_le hbnd_le hconv hlbb hdef
    simp only [Ix.Kernel.Reader.convExpr] at hconv
    obtain ⟨k_rd, hk_rd, hbind2⟩ := except_bind_eq_ok hconv
    obtain ⟨Ein_rd, hEin_rd, hret⟩ := except_bind_eq_ok hbind2
    injection hret with hE; subst hE
    have hk_eq : k_rd = κ a := by
      unfold Ix.Kernel.Reader.ECx.keyAt at hk_rd
      have href_arr : ecx.src.refs[tIdx.toNat]? = some a := by
        rw [← Array.getElem?_toList, hrefs, href]
      rw [href_arr] at hk_rd
      exact hkeyAt a k_rd hk_rd
    subst hk_eq
    simp only [Ix.Kernel.Expr.looseBVarsBounded] at hlbb
    simp only [Ix.Kernel.Expr.allLevelParamsDefined] at hdef
    obtain ⟨Ein', hA_in, hTm_in⟩ := ih hn_le hbnd_le hEin_rd hlbb hdef
    refine ⟨.proj (κ a) fIdx.toNat Ein', .proj hA_in, fun d0 Γ => ?_⟩
    unfold Core.posOf Ix.Kernel.Expr.instantiateLevelParams
    have hf_val : ZMod.val (fIdx.toNat : F) = fIdx.toNat := ZMod.val_cast_of_lt (by omega)
    rw [← hd, ← hf_val]
    exact .proj cell ra (hTm_in d0 Γ)
  | @str bound addr bIdx a bs s bp hbIdx href hmem rbs hs cell =>
    intro n k E_rd _ _ hconv _ _
    simp only [Ix.Kernel.Reader.convExpr] at hconv
    obtain ⟨b_arr, hb_at, hrest⟩ := except_bind_eq_ok hconv
    have hb_eq : b_arr = ⟨bs.toArray⟩ := by
      unfold Ix.Kernel.Reader.ECx.blobAt at hb_at
      have href_arr : ecx.src.refs[bIdx.toNat]? = some a := by
        rw [← Array.getElem?_toList, hrefs, href]
      rw [href_arr, hblob a ⟨bs.toArray⟩ hmem] at hb_at
      injection hb_at
    subst hb_eq
    have hs_utf8 : String.fromUTF8? ⟨bs.toArray⟩ = some s := hs
    rw [hs_utf8] at hrest
    injection hrest with hE; subst hE
    exact ⟨.lit (.strVal s), .lit, fun d0 Γ => .litStr cell rbs hs⟩
  | @nat bound addr bIdx a bs limbs lp hbIdx href hmem hcanon rlimbs hlast hval cell =>
    intro n k E_rd _ _ hconv _ _
    simp only [Ix.Kernel.Reader.convExpr] at hconv
    obtain ⟨n_rd, hn_at, hret⟩ := except_bind_eq_ok hconv
    injection hret with hE; subst hE
    have hn_eq : n_rd = Core.limbsVal limbs := by
      unfold Ix.Kernel.Reader.ECx.natAt Ix.Kernel.Reader.ECx.blobAt at hn_at
      have href_arr : ecx.src.refs[bIdx.toNat]? = some a := by
        rw [← Array.getElem?_toList, hrefs, href]
      rw [href_arr] at hn_at
      simp only [bind, Except.bind, hblob a ⟨bs.toArray⟩ hmem, hcanon, ↓reduceIte,
        pure, Except.pure, Except.ok.injEq] at hn_at
      exact hn_at.symm.trans hval.symm
    subst hn_eq
    exact ⟨.lit (.natVal (Core.limbsVal limbs)), .lit,
      fun d0 Γ => .litNat cell rlimbs hlast⟩
  | @app bound addr f arg fp ap _ _ cell ihf iha =>
    intro n k E_rd hn_le hbnd_le hconv hlbb hdef
    simp only [Ix.Kernel.Reader.convExpr] at hconv
    obtain ⟨Ef_rd, hEf, hbind2⟩ := except_bind_eq_ok hconv
    obtain ⟨Ea_rd, hEa, hret⟩ := except_bind_eq_ok hbind2
    injection hret with hE; subst hE
    simp only [Ix.Kernel.Expr.looseBVarsBounded, Bool.and_eq_true] at hlbb
    simp only [Ix.Kernel.Expr.allLevelParamsDefined, Bool.and_eq_true] at hdef
    obtain ⟨Ef', hAf, hTmf⟩ := ihf hn_le hbnd_le hEf hlbb.1 hdef.1
    obtain ⟨Ea', hAa, hTma⟩ := iha hn_le hbnd_le hEa hlbb.2 hdef.2
    exact ⟨.app Ef' Ea', .app hAf hAa, fun d0 Γ => .app cell (hTmf d0 Γ) (hTma d0 Γ)⟩
  | @lam bound addr ty body tp bp lp ℓ rl _ _ cell iht ihb =>
    intro n k E_rd hn_le hbnd_le hconv hlbb hdef
    simp only [Ix.Kernel.Reader.convExpr] at hconv
    obtain ⟨Et_rd, hEt, hbind2⟩ := except_bind_eq_ok hconv
    obtain ⟨Eb_rd, hEb, hret⟩ := except_bind_eq_ok hbind2
    injection hret with hE; subst hE
    simp only [Ix.Kernel.Expr.looseBVarsBounded, Bool.and_eq_true] at hlbb
    simp only [Ix.Kernel.Expr.allLevelParamsDefined, Bool.and_eq_true] at hdef
    obtain ⟨Et', hAt, hTmt⟩ := iht hn_le hbnd_le hEt hlbb.1 hdef.1.1
    obtain ⟨Eb', hAb, hTmb⟩ := ihb hn_le hbnd_le hEb hlbb.2 hdef.1.2
    refine ⟨.lam Et' Eb' (Core.bmeta (invPosLevel ps ℓ)), .lam hAt hAb, fun d0 Γ => ?_⟩
    unfold Core.posOf Ix.Kernel.Expr.instantiateLevelParams
    rw [substPW_posLevels_bmeta hperm ℓ]
    exact .lam cell (hTmt d0 Γ) (hTmb d0 Γ) rl
  | @all bound addr ty body tp bp lp ℓ rl _ _ cell iht ihb =>
    intro n k E_rd hn_le hbnd_le hconv hlbb hdef
    simp only [Ix.Kernel.Reader.convExpr] at hconv
    obtain ⟨Et_rd, hEt, hbind2⟩ := except_bind_eq_ok hconv
    obtain ⟨Eb_rd, hEb, hret⟩ := except_bind_eq_ok hbind2
    injection hret with hE; subst hE
    simp only [Ix.Kernel.Expr.looseBVarsBounded, Bool.and_eq_true] at hlbb
    simp only [Ix.Kernel.Expr.allLevelParamsDefined, Bool.and_eq_true] at hdef
    obtain ⟨Et', hAt, hTmt⟩ := iht hn_le hbnd_le hEt hlbb.1 hdef.1.1
    obtain ⟨Eb', hAb, hTmb⟩ := ihb hn_le hbnd_le hEb hlbb.2 hdef.1.2
    refine ⟨.forallE Et' Eb' (Core.bmeta (invPosLevel ps ℓ)), .forallE hAt hAb, fun d0 Γ => ?_⟩
    unfold Core.posOf Ix.Kernel.Expr.instantiateLevelParams
    rw [substPW_posLevels_bmeta hperm ℓ]
    exact .forallE cell (hTmt d0 Γ) (hTmb d0 Γ) rl
  | @letE bound addr nd md ty val body tp vp bp _ _ _ cell iht ihv ihb =>
    intro n k E_rd hn_le hbnd_le hconv hlbb hdef
    simp only [Ix.Kernel.Reader.convExpr] at hconv
    obtain ⟨Et_rd, hEt, hbind2⟩ := except_bind_eq_ok hconv
    obtain ⟨Ev_rd, hEv, hbind3⟩ := except_bind_eq_ok hbind2
    obtain ⟨Eb_rd, hEb, hret⟩ := except_bind_eq_ok hbind3
    injection hret with hE; subst hE
    simp only [Ix.Kernel.Expr.looseBVarsBounded, Bool.and_eq_true] at hlbb
    simp only [Ix.Kernel.Expr.allLevelParamsDefined, Bool.and_eq_true] at hdef
    obtain ⟨Et', _, hTmt⟩ := iht hn_le hbnd_le hEt hlbb.1.1 hdef.1.1
    obtain ⟨Ev', hAv, hTmv⟩ := ihv hn_le hbnd_le hEv hlbb.1.2 hdef.1.2
    obtain ⟨Eb', hAb, hTmb⟩ := ihb hn_le hbnd_le hEb hlbb.2 hdef.2
    refine ⟨Eb'.instantiate1Lift Ev' 0,
      .letE (annotates_instantiate1Lift hAb hAv 0), fun d0 Γ => ?_⟩
    have hilp : Core.posOf ps (Eb'.instantiate1Lift Ev' 0) =
        Core.instShift (Core.posOf ps Ev') 0 (Core.posOf ps Eb') :=
      Core.SubstAux.ilp_instShift ps (Core.posLevels ps) Ev' Eb' 0
    rw [hilp]
    exact .letE cell (hTmt d0 Γ) (hTmv d0 Γ) (hTmb d0 Γ)
  | @share bound idx s kp hidx hsh _ ih =>
    intro n k E_rd hn_le hbnd_le hconv hlbb hdef
    have hidx_len : idx.toNat < sharing.length := List.getElem?_eq_some_iff.mp ⟨s, hsh⟩ |>.1
    have hidx_n : idx.toNat < n := by omega
    simp only [Ix.Kernel.Reader.convExpr] at hconv
    rw [buildShareTbl_take_getElem? ecx sharing hidx_n hsh] at hconv
    exact ih (Nat.le_of_lt hidx_len) (Nat.min_le_left _ _) hconv hlbb hdef

/-- **Closed root bridge (`RawConvExpr.toTmC`)**: directly connects a root `RawConvExpr` and a
`MemberReader.read` evaluation of `e` (closed and with defined level parameters) to `Annotates`
and `Core.TmC`. -/
theorem RawConvExpr.toTmC {κ : _root_.Address → Core.KKey}
    {ps : List Ix.Kernel.LevelParam}
    (hperm : ps.Perm (List.range ps.length)) (hps_lt : ps.length < 4294967296)
    {cx : Ix.Kernel.Reader.Ctx .anon} {src : Ixon.Constant}
    {self : Nat → Option (Ix.Kernel.Reader.ReadM Core.KKey)}
    {recurAddrs : List _root_.Address} {blobs : List (_root_.Address × ByteArray)}
    (hkeyAt : ∀ a k, cx.keyAt a = .ok k → k = κ a)
    (hself : ∀ i a m k, recurAddrs[i]? = some a → self i = some m → m = .ok k → k = κ a)
    (hblob : ∀ a bs, (a, bs) ∈ blobs → cx.blob a = some bs)
    {h : Heap F} {e : Ixon.Expr} {kp : SourceValue F} {E_rd : Core.KExpr}
    (raw : RawConvExpr src.refs.toList recurAddrs src.univs.toList src.sharing.toList blobs
      h 4294967295 e kp)
    (hread : (Ix.Kernel.Reader.MemberReader.mk' cx src (Ix.Kernel.Reader.recParam ps) self).read e =
      .ok E_rd)
    (hlbb : E_rd.looseBVarsBounded 0 = true)
    (hdef : E_rd.allLevelParamsDefined ps = true) :
    ∃ E' : Core.KExpr,
      IxVM.Consistency.Annotates E' E_rd ∧
      Core.TmC κ h (Core.posOf ps E') kp := by
  obtain ⟨hecx, htbl⟩ := memberReader_mk'_eq cx src (Ix.Kernel.Reader.recParam ps) self
  unfold Ix.Kernel.Reader.MemberReader.read at hread
  rw [hecx, htbl, ← List.take_length (l := src.sharing.toList)] at hread
  exact raw.toTm hperm hps_lt rfl (by simp) hkeyAt hself hblob
    (Nat.le_refl _) (Nat.min_le_right _ _) hread hlbb hdef

end IxVM.Refinement.L1
