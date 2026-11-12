import IxVMRefinement.L1.Blake3
import IxVMRefinement.Obs.IxByteStream
import IxVMRefinement.Obs.IxVMCompat

/-! # Byte streams read from the host at source level

The bytes are hints (`ixvm.io.read`), each checked as a byte by `UInt8::from_field` or, two at
a time, `UInt8::from_fields`; nothing about their values is assumed. What the circuit fixes is
the shape: `IxByteStream::read_byte_stream(channel, idx, len)` builds a stream of exactly `len`
bytes (`read_byte_stream_spec`), and `IxByteStream::read_finite_byte_stream` range-checks `len`
below `2^32` first (`UInt32::less_than_fields(0, len)`, `lt_fields_zero_spec`), so it returns a
stream of `len < 2^32` bytes (`read_finite_byte_stream_spec`). `IxVMCompat::io_get_info` returns
an arbitrary hint and leaves the heap unchanged (`io_get_info_spec`).
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
open Aiur.Library.Blake3 (wordOfBytes)

/-- The cast of naturals below `3 * 2^32` into the field is injective. -/
theorem natCast_inj3 {a b : Nat} (ha : a < 3 * 4294967296) (hb : b < 3 * 4294967296)
    (h : (a : F) = (b : F)) : a = b :=
  Aiur.Library.U32.Goldilocks.compatible ha hb h

theorem base_cast : (((Aiur.Library.U32.base : Nat) : F)) = 4294967296 := by
  simp [Aiur.Library.U32.base]

/-- **`UInt32::less_than_fields(0, x)`** range-checks `x` below `2^32` and tests `0 < x`. -/
theorem lt_fields_zero_spec {x r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (ev : ObsFn W "UInt32::less_than_fields" [.field 0, x] h r h' cs) :
    ∃ n : Nat, n < 4294967296 ∧ x = .field (n : F) ∧ r = .field (if 0 < n then 1 else 0) ∧
      h' = h := by
  obtain ⟨k10, v31, m32, cs42, v45, v56, m57, cs67, v70, v81, m82, cs92, v95, v118, m127, cs135,
    v159, m168, cs176, v188, x196, x204, x212, m214, cs223, v247, y256, ty12, pr54, ev44, pr79,
    ev69, pr104, ev94, ev137, heq146, ev178, heq187, ev225, op219, op211, op203, op271, op262,
    heq279, he281, he282, -⟩ := «UInt32::less_than_fields».obs ev
  obtain ⟨c0, c1, c2, c3, rfl, hm32⟩ := u32_fromFields ev44
  subst m32
  obtain ⟨d0, d1, d2, d3, rfl, hm57⟩ := u32_fromFields ev69
  subst m57
  obtain ⟨e0, e1, e2, e3, rfl, hm82⟩ := u32_fromFields ev94
  subst m82
  obtain ⟨rfl, hm127⟩ := u32_compact ev137
  subst m127
  obtain ⟨rfl, hm168⟩ := u32_compact ev178
  subst m168
  obtain ⟨rfl, hm214⟩ := u32_compact ev225
  subst m214
  subst heq187
  obtain rfl := binop_add op219
  obtain rfl := binop_sub op211
  obtain rfl := binop_div base_ne_zero op203
  obtain rfl := binop_sub op271
  obtain rfl := binop_mul op262
  have hz : ((0 : Nat) : F) = ((wordOfBytes c0 c1 c2 c3).toNat : F) := by
    rw [Nat.cast_zero]
    exact Value.field.inj heq146
  have hwl := word_lt (wordOfBytes c0 c1 c2 c3)
  simp only [Aiur.Library.U32.base] at hwl
  have hl0 : (wordOfBytes c0 c1 c2 c3).toNat = 0 :=
    (natCast_inj3 (a := 0) (by omega) (by omega) hz).symm
  have valid := Value.field.inj heq279
  rw [← base_cast] at valid
  have res := Aiur.Library.U32.compare_fields_sound Aiur.Library.U32.Goldilocks.compatible
    (0 : F) ((wordOfBytes e0 e1 e2 e3).toNat : F)
    (leftWord := (wordOfBytes c0 c1 c2 c3).toNat) (rightWord := (wordOfBytes e0 e1 e2 e3).toNat)
    (difference := (wordOfBytes d0 d1 d2 d3).toNat)
    (word_lt _) (word_lt _) (word_lt _) (by rw [hl0]; simp) rfl valid
  rw [base_cast, hl0] at res
  refine ⟨(wordOfBytes e0 e1 e2 e3).toNat, ?_, rfl, ?_, he282⟩
  · have := word_lt (wordOfBytes e0 e1 e2 e3)
    simpa [Aiur.Library.U32.base] using this
  · rw [he281, res]

/-! ## `IxByteStream::read_byte_stream` -/

theorem field_ne_of_ne {a b : Nat} (ha : a < 4294967296) (hb : b < 4294967296) (hab : a ≠ b)
    (h : (a : F) = (b : F)) : False :=
  hab (natCast_inj3 (by omega) (by omega) h)

theorem field_eq_lit {n : Nat} (hn : n < 4294967296) {k : Nat} (hk : k < 4) {x : F}
    (hx : x = (k : F)) (h : (.field (n : F) : SourceValue F) = .field x) : n = k := by
  subst hx
  exact natCast_inj3 (by omega) (by omega) (Value.field.inj h)

/-- **`IxByteStream::read_byte_stream(channel, idx, len)`** builds a stream of exactly `len`
bytes. -/
theorem read_byte_stream_spec : ∀ (n : Nat) {ch idx r : SourceValue F} {h h' : Heap F}
    {cs : List (Call F)}, n < 4294967296 →
    ObsFn W "IxByteStream::read_byte_stream" [ch, idx, .field (n : F)] h r h' cs →
    Heap.Extends h h' ∧ ∃ bytes : List UInt8, bytes.length = n ∧ Stream h' bytes r
  | 0, ch, idx, r, h, h', cs, hn, ev => by
    rcases «IxByteStream::read_byte_stream».obs ev with
      ⟨hv14, he19, hm18, -⟩ | ⟨k38, v67, m70, cs78, m90, hne24, -⟩ |
      ⟨k117, k147, v153, m177, cs187, x_u0, x_u1, m237, m259, hne24, -⟩ |
      ⟨k286, k316, v322, k354, v360, m384, cs394, x_u0, x_u1, m444, m466, v478, m481, cs489, m501,
        hne24, -⟩ |
      ⟨k527, k557, v563, k595, v601, k633, v639, m663, cs673, x_u0, x_u1, m706, cs716, x_u2, x_u3,
        v748, m749, cs759, v763, v764, m820, m842, m864, hne24, -⟩
    · subst he19 hm18
      exact ⟨Heap.Extends.snoc _ _, [], rfl, stream_nil_snoc h⟩
    all_goals exact absurd (by simp) hne24
  | 1, ch, idx, r, h, h', cs, hn, ev => by
    rcases «IxByteStream::read_byte_stream».obs ev with
      ⟨hv14, -⟩ | ⟨k38, v67, m70, cs78, m90, hne24, hv28, ty40, he63, hm62, ev80, hm98, -⟩ |
      ⟨k117, k147, v153, m177, cs187, x_u0, x_u1, m237, m259, hne24, hne103, -⟩ |
      ⟨k286, k316, v322, k354, v360, m384, cs394, x_u0, x_u1, m444, m466, v478, m481, cs489, m501,
        hne24, hne103, -⟩ |
      ⟨k527, k557, v563, k595, v601, k633, v639, m663, cs673, x_u0, x_u1, m706, cs716, x_u2, x_u3,
        v748, m749, cs759, v763, v764, m820, m842, m864, hne24, hne103, -⟩
    · exact absurd (field_eq_lit (k := 0) hn (by omega) (by simp) hv14) (by omega)
    · obtain ⟨b, -, rfl, hm70⟩ := u8_fromField ev80
      subst m70
      subst hm98 hm62 he63
      exact ⟨(Heap.Extends.snoc _ _).trans (Heap.Extends.snoc _ _), [b], rfl,
        stream_cons_snoc (stream_nil_snoc h)⟩
    all_goals exact absurd (by simp) hne103
  | 2, ch, idx, r, h, h', cs, hn, ev => by
    rcases «IxByteStream::read_byte_stream».obs ev with
      ⟨hv14, -⟩ | ⟨k38, v67, m70, cs78, m90, hne24, hv28, -⟩ |
      ⟨k117, k147, v153, m177, cs187, x_u0, x_u1, m237, m259, hne24, hne103, hv107, ty119, op174,
        ty149, ev189, he223, hm222, hm245, hm267, -⟩ |
      ⟨k286, k316, v322, k354, v360, m384, cs394, x_u0, x_u1, m444, m466, v478, m481, cs489, m501,
        hne24, hne103, hne272, -⟩ |
      ⟨k527, k557, v563, k595, v601, k633, v639, m663, cs673, x_u0, x_u1, m706, cs716, x_u2, x_u3,
        v748, m749, cs759, v763, v764, m820, m842, m864, hne24, hne103, hne272, -⟩
    · exact absurd (field_eq_lit (k := 0) hn (by omega) (by simp) hv14) (by omega)
    · exact absurd (field_eq_lit (k := 1) hn (by omega) (by simp) hv28) (by omega)
    · obtain ⟨a, b, -, -, e, hm177⟩ := u8_fromFields ev189
      simp only [Value.tuple.injEq, List.cons.injEq, and_true] at e
      obtain ⟨rfl, rfl⟩ := e
      subst m177
      subst hm267 hm245 hm222 he223
      exact ⟨((Heap.Extends.snoc _ _).trans (Heap.Extends.snoc _ _)).trans (Heap.Extends.snoc _ _),
        [a, b], rfl, stream_cons_snoc (stream_cons_snoc (stream_nil_snoc h))⟩
    all_goals exact absurd (by simp) hne272
  | 3, ch, idx, r, h, h', cs, hn, ev => by
    rcases «IxByteStream::read_byte_stream».obs ev with
      ⟨hv14, -⟩ | ⟨k38, v67, m70, cs78, m90, hne24, hv28, -⟩ |
      ⟨k117, k147, v153, m177, cs187, x_u0, x_u1, m237, m259, hne24, hne103, hv107, -⟩ |
      ⟨k286, k316, v322, k354, v360, m384, cs394, x_u0, x_u1, m444, m466, v478, m481, cs489, m501,
        hne24, hne103, hne272, hv276, ty288, op343, ty318, op381, ty356, ev396, he430, hm429,
        hm452, hm474, ev491, hm509, -⟩ |
      ⟨k527, k557, v563, k595, v601, k633, v639, m663, cs673, x_u0, x_u1, m706, cs716, x_u2, x_u3,
        v748, m749, cs759, v763, v764, m820, m842, m864, hne24, hne103, hne272, hne514, -⟩
    · exact absurd (field_eq_lit (k := 0) hn (by omega) (by simp) hv14) (by omega)
    · exact absurd (field_eq_lit (k := 1) hn (by omega) (by simp) hv28) (by omega)
    · exact absurd (field_eq_lit (k := 2) hn (by omega) (by simp) hv107) (by omega)
    · obtain ⟨a, b, -, -, e, hm384⟩ := u8_fromFields ev396
      simp only [Value.tuple.injEq, List.cons.injEq, and_true] at e
      obtain ⟨rfl, rfl⟩ := e
      subst m384
      obtain ⟨c, -, rfl, hm481⟩ := u8_fromField ev491
      subst m481
      subst hm509 hm474 hm452 hm429 he430
      exact ⟨(((Heap.Extends.snoc _ _).trans (Heap.Extends.snoc _ _)).trans
        (Heap.Extends.snoc _ _)).trans (Heap.Extends.snoc _ _), [a, b, c], rfl,
        stream_cons_snoc (stream_cons_snoc (stream_cons_snoc (stream_nil_snoc h)))⟩
    · exact absurd (by simp) hne514
  | n + 4, ch, idx, r, h, h', cs, hn, ev => by
    rcases «IxByteStream::read_byte_stream».obs ev with
      ⟨hv14, -⟩ | ⟨k38, v67, m70, cs78, m90, hne24, hv28, -⟩ |
      ⟨k117, k147, v153, m177, cs187, x_u0, x_u1, m237, m259, hne24, hne103, hv107, -⟩ |
      ⟨k286, k316, v322, k354, v360, m384, cs394, x_u0, x_u1, m444, m466, v478, m481, cs489, m501,
        hne24, hne103, hne272, hv276, -⟩ |
      ⟨k527, k557, v563, k595, v601, k633, v639, m663, cs673, x_u0, x_u1, m706, cs716, x_u2, x_u3,
        v748, m749, cs759, v763, v764, m820, m842, m864, hne24, hne103, hne272, hne514, ty529,
        op584, ty559, op622, ty597, op660, ty635, ev675, ev718, op785, op800, ev761, he806, hm805,
        hm828, hm850, hm872, -⟩
    · exact absurd (field_eq_lit (k := 0) hn (by omega) (by simp) hv14) (by omega)
    · exact absurd (field_eq_lit (k := 1) hn (by omega) (by simp) hv28) (by omega)
    · exact absurd (field_eq_lit (k := 2) hn (by omega) (by simp) hv107) (by omega)
    · exact absurd (field_eq_lit (k := 3) hn (by omega) (by simp) hv276) (by omega)
    · obtain ⟨a, b, -, -, e1, hm663⟩ := u8_fromFields ev675
      simp only [Value.tuple.injEq, List.cons.injEq, and_true] at e1
      obtain ⟨rfl, rfl⟩ := e1
      subst m663
      obtain ⟨c, d, -, -, e2, hm706⟩ := u8_fromFields ev718
      simp only [Value.tuple.injEq, List.cons.injEq, and_true] at e2
      obtain ⟨rfl, rfl⟩ := e2
      subst m706
      obtain rfl := binop_sub op800
      rw [show ((n + 4 : Nat) : F) - 4 = ((n : Nat) : F) by push_cast; ring] at ev761
      obtain ⟨ext1, rest, hlen, hrest⟩ := read_byte_stream_spec n (by omega) ev761
      subst hm872 hm850 hm828 hm805 he806
      refine ⟨ext1.trans ((((Heap.Extends.snoc _ _).trans (Heap.Extends.snoc _ _)).trans
        (Heap.Extends.snoc _ _)).trans (Heap.Extends.snoc _ _)), a :: b :: c :: d :: rest,
        by simp [hlen], ?_⟩
      exact stream_cons_snoc (stream_cons_snoc (stream_cons_snoc (stream_cons_snoc hrest)))

/-- **`IxByteStream::read_finite_byte_stream(channel, idx, len)`** returns a stream of `len`
bytes, `len < 2^32`. -/
theorem read_finite_byte_stream_spec {ch idx len r : SourceValue F} {h h' : Heap F}
    {cs : List (Call F)}
    (ev : ObsFn W "IxByteStream::read_finite_byte_stream" [ch, idx, len] h r h' cs) :
    Heap.Extends h h' ∧ ∃ bytes : List UInt8, bytes.length < 4294967296 ∧
      len = .field (bytes.length : F) ∧ Stream h' bytes r := by
  rcases «IxByteStream::read_finite_byte_stream».obs ev with
    ⟨m2, cs13, ev15, he39, hm38, -⟩ | ⟨v1, m2, cs13, cs51, ev15, hne44, ev53, -⟩
  · obtain ⟨n, hn, rfl, hr, hm2⟩ := lt_fields_zero_spec ev15
    subst m2
    have hn0 : n = 0 := by
      by_contra hne
      simp only [show 0 < n by omega, ↓reduceIte] at hr
      exact one_ne_zero (Value.field.inj hr).symm
    subst hn0 he39 hm38
    exact ⟨Heap.Extends.snoc _ _, [], by decide, by simp, stream_nil_snoc h⟩
  · obtain ⟨n, hn, rfl, rfl, hm2⟩ := lt_fields_zero_spec ev15
    subst m2
    obtain ⟨ext1, bytes, hlen, hst⟩ := read_byte_stream_spec n hn ev53
    exact ⟨ext1, bytes, by omega, by rw [hlen], hst⟩

/-- **`IxVMCompat::io_get_info`** returns a hint and leaves the heap unchanged. -/
theorem io_get_info_spec {ch key r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (ev : ObsFn W "IxVMCompat::io_get_info" [ch, key] h r h' cs) : h' = h := by
  obtain ⟨k2, v9, m18, cs26, he5, ev28, he37, ty4, -⟩ := «IxVMCompat::io_get_info».obs ev
  obtain ⟨hm18, -⟩ := address_to_fields_spec ev28
  rw [he37, hm18]

end IxVM.Refinement.L1
