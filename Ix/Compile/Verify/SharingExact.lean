import Ix.Compile.Verify.ExprSpineCodec
import Ix.Compile.Verify.TagN
import Ix.Compile.Verify.Catalog
import Ix.Compile.Verify.MutualConstantCodec
import Ix.Sharing.Exact

/-!
# Exact minimum sharing: foundational facts

Proofs about the executable exact-sharing core (`Ix.Sharing.Exact`):

* the integer widths `tag0Size`, `tag4Size`, `shareWidth` are the sizes of
  the production TagN encodings (`f = 0`, `f = 4`; `Ix.Compile.Verify.Codec`)
  and agree with the heuristic's `tag0EncodedSize`/`tag4EncodedSize`;
  `tagNWidth` is the length of the `f = 4` TagN encoding and is monotone with
  the stated rung ends;
* `exprSize` is the length of the production expression encoding for every
  expression in the codec's wire domain (telescope rule included), and the
  complete-Constant length decomposes as `fixedConstantBytes` plus the
  variable parts;
* the §3.2 key comparisons are lawful total orders, and sorting distinct
  keys does not depend on the input order.
-/

namespace Ix.Compile.Verify.SharingExact

open Ix.Sharing.Exact
open Ix.Compile.Verify.Codec
open Ix.Compile.Verify.Codec.Ixon.Expr

/-! ## Minimal little-endian byte counts -/

theorem natByteCount_zero : natByteCount 0 = 0 := by
  rw [natByteCount]
  simp

theorem natByteCount_of_ne_zero {n : Nat} (h : n ≠ 0) :
    natByteCount n = natByteCount (n / 256) + 1 := by
  rw [natByteCount]
  simp [h]

/-- `natByteCount n = k` exactly on `[256^(k-1), 256^k)`. -/
theorem natByteCount_eq_of_range :
    ∀ (k n : Nat), 256 ^ k ≤ n → n < 256 ^ (k + 1) → natByteCount n = k + 1
  | 0, n, hlo, hhi => by
    have hn : n ≠ 0 := by simp at hlo; omega
    rw [natByteCount_of_ne_zero hn]
    have : n / 256 = 0 := by simp at hhi; omega
    rw [this, natByteCount_zero]
  | k + 1, n, hlo, hhi => by
    have hpos : 0 < 256 ^ (k + 1) := Nat.pow_pos_iff.mpr (Or.inl (by decide))
    have hn : n ≠ 0 := by omega
    rw [natByteCount_of_ne_zero hn]
    have hlo' : 256 ^ k ≤ n / 256 := by
      rw [Nat.le_div_iff_mul_le (by decide)]
      simpa [Nat.pow_succ] using hlo
    have hhi' : n / 256 < 256 ^ (k + 1) := by
      rw [Nat.div_lt_iff_lt_mul (by decide)]
      simpa [Nat.pow_succ] using hhi
    rw [natByteCount_eq_of_range k (n / 256) hlo' hhi']

/-- `natByteCount` agrees with the production `u64ByteCount`. -/
theorem natByteCount_toNat (x : UInt64) :
    natByteCount x.toNat = (Ixon.u64ByteCount x).toNat := by
  have hx := x.toNat_lt
  unfold Ixon.u64ByteCount
  split <;> rename_i h0
  · have : x = 0 := by simpa using h0
    subst this
    simp [natByteCount_zero]
  have hne : x.toNat ≠ 0 := by
    intro h
    apply h0
    have : x = 0 := UInt64.toNat_inj.mp (by simpa using h)
    simp [this]
  split <;> rename_i h1
  · simp only [UInt64.lt_iff_toNat_lt, UInt64.reduceToNat] at h1
    simpa using natByteCount_eq_of_range 0 x.toNat (by simp; omega) (by simpa using h1)
  split <;> rename_i h2
  · simp only [UInt64.lt_iff_toNat_lt, UInt64.reduceToNat] at h1 h2
    simpa using natByteCount_eq_of_range 1 x.toNat (by simp; omega) (by simpa using h2)
  split <;> rename_i h3
  · simp only [UInt64.lt_iff_toNat_lt, UInt64.reduceToNat] at h2 h3
    simpa using natByteCount_eq_of_range 2 x.toNat (by simp; omega) (by simpa using h3)
  split <;> rename_i h4
  · simp only [UInt64.lt_iff_toNat_lt, UInt64.reduceToNat] at h3 h4
    simpa using natByteCount_eq_of_range 3 x.toNat (by simp; omega) (by simpa using h4)
  split <;> rename_i h5
  · simp only [UInt64.lt_iff_toNat_lt, UInt64.reduceToNat] at h4 h5
    simpa using natByteCount_eq_of_range 4 x.toNat (by simp; omega) (by simpa using h5)
  split <;> rename_i h6
  · simp only [UInt64.lt_iff_toNat_lt, UInt64.reduceToNat] at h5 h6
    simpa using natByteCount_eq_of_range 5 x.toNat (by simp; omega) (by simpa using h6)
  split <;> rename_i h7
  · simp only [UInt64.lt_iff_toNat_lt, UInt64.reduceToNat] at h6 h7
    simpa using natByteCount_eq_of_range 6 x.toNat (by simp; omega) (by simpa using h7)
  · simp only [UInt64.lt_iff_toNat_lt, UInt64.reduceToNat] at h7
    simpa using natByteCount_eq_of_range 7 x.toNat (by simp; omega) (by simpa using hx)

/-! ## TagN (`f = 0`, `f = 4`) lengths -/

theorem trimmedBytes_size (x : UInt64) (len : Nat) : (trimmedBytes x len).size = len :=
  Codec.trimmedBytes_size x len

/-- `tag4Size` is the length of the production TagN (`f = 4`) bytes. -/
theorem tag4Bytes_size (flag : UInt8) (size : UInt64) :
    (Codec.tag4Bytes flag size).size = tag4Size size.toNat :=
  Codec.tagNBytes_size 4 flag size

/-- `tag0Size` is the length of the production TagN (`f = 0`) bytes. -/
theorem tag0Bytes_size (size : UInt64) :
    (tag0Bytes size).size = tag0Size size.toNat :=
  Codec.tagNBytes_size 0 0 size

/-- `tag4Size` is the size of what `putTagN 4` writes. -/
theorem putTag4_size (flag : UInt8) (size : UInt64) :
    (Ixon.runPut (Ixon.putTagN 4 flag size)).size = tag4Size size.toNat :=
  Codec.runPut_putTagN_size 4 flag size

/-- `tag0Size` is the size of what `putTagN 0` writes. -/
theorem putTag0_size (size : UInt64) :
    (Ixon.runPut (Ixon.putTagN 0 0 size)).size = tag0Size size.toNat :=
  Codec.runPut_putTagN_size 0 0 size

/-- The Share width is the size of the serialized `Share`. -/
theorem shareWidth_eq_putTag4 (idx : UInt64) :
    shareWidth idx.toNat =
      (Ixon.runPut (Ixon.putTagN 4 Ixon.Expr.FLAG_SHARE idx)).size :=
  (putTag4_size Ixon.Expr.FLAG_SHARE idx).symm

/-- `UInt64.byteCount` agrees with the minimal byte count on nonzero values. -/
theorem byteCount_eq_u64ByteCount (x : UInt64) (h : x ≠ 0) :
    x.byteCount = Ixon.u64ByteCount x := by
  unfold UInt64.byteCount Ixon.u64ByteCount
  have h0 : (x == 0) = false := by simpa using h
  simp only [h0, Bool.false_eq_true, if_false]

/-- The heuristic's TagN (`f = 0`) size agrees with `tag0Size`. -/
theorem tag0EncodedSize_eq (x : UInt64) :
    Ix.Sharing.tag0EncodedSize x = tag0Size x.toNat := rfl

/-- The heuristic's TagN (`f = 4`) size agrees with `tag4Size`. -/
theorem tag4EncodedSize_eq (x : UInt64) :
    Ix.Sharing.tag4EncodedSize x = tag4Size x.toNat := rfl

/-! ## TagN widths -/

theorem tagNRung1End_eq : tagNRung1End = 8 := TagN.tagNEnd1_eq_4
theorem tagNRung2End_eq : tagNRung2End = 1032 := TagN.tagNEnd2_eq_4
theorem tagNRung3End_eq : tagNRung3End = 66568 := TagN.tagNEnd3_eq_4
/-- `66568 + 2^24`. -/
theorem tagNRung4End_eq : tagNRung4End = 16843784 := TagN.tagNEnd4_eq_4
/-- `66568 + 2^24 + 2^32`. -/
theorem tagNRung5End_eq : tagNRung5End = 4311811080 := TagN.tagNEnd5_eq_4
/-- `66568 + 2^24 + 2^32 + 2^64`. -/
theorem tagNRung6End_eq : tagNRung6End = 18446744078021362696 := by
  unfold tagNRung6End Ixon.tagNEnd6; rw [TagN.tagNEnd5_eq_4]

/-- `tagNWidth` with the rung ends evaluated. -/
theorem tagNWidth_eq (i : Nat) :
    tagNWidth i =
      if i < 8 then 1 else if i < 1032 then 2 else if i < 66568 then 3
      else if i < 16843784 then 4 else if i < 4311811080 then 5 else 9 := by
  unfold tagNWidth Ixon.tagNByteWidth
  rw [TagN.tagNEnd1_eq_4, TagN.tagNEnd2_eq_4, TagN.tagNEnd3_eq_4, TagN.tagNEnd4_eq_4,
    TagN.tagNEnd5_eq_4]

theorem tagNWidth_pos (i : Nat) : 1 ≤ tagNWidth i := by
  rw [tagNWidth_eq]
  repeat' split
  all_goals omega

/-- TagN widths never decrease with the index. -/
theorem tagNWidth_mono {i j : Nat} (h : i ≤ j) : tagNWidth i ≤ tagNWidth j := by
  rw [tagNWidth_eq, tagNWidth_eq]
  repeat' split
  all_goals omega

theorem tagNWidth_rung1 {i : Nat} (h : i < tagNRung1End) : tagNWidth i = 1 := by
  rw [tagNRung1End_eq] at h
  rw [tagNWidth_eq, if_pos h]

theorem tagNWidth_rung2 {i : Nat} (h1 : tagNRung1End ≤ i) (h2 : i < tagNRung2End) :
    tagNWidth i = 2 := by
  rw [tagNRung1End_eq] at h1
  rw [tagNRung2End_eq] at h2
  rw [tagNWidth_eq, if_neg (by omega), if_pos h2]

theorem tagNWidth_rung3 {i : Nat} (h1 : tagNRung2End ≤ i) (h2 : i < tagNRung3End) :
    tagNWidth i = 3 := by
  rw [tagNRung2End_eq] at h1
  rw [tagNRung3End_eq] at h2
  rw [tagNWidth_eq, if_neg (by omega), if_neg (by omega), if_pos h2]

theorem tagNWidth_rung4 {i : Nat} (h1 : tagNRung3End ≤ i) (h2 : i < tagNRung4End) :
    tagNWidth i = 4 := by
  rw [tagNRung3End_eq] at h1
  rw [tagNRung4End_eq] at h2
  rw [tagNWidth_eq, if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos h2]

theorem tagNWidth_rung5 {i : Nat} (h1 : tagNRung4End ≤ i) (h2 : i < tagNRung5End) :
    tagNWidth i = 5 := by
  rw [tagNRung4End_eq] at h1
  rw [tagNRung5End_eq] at h2
  rw [tagNWidth_eq, if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (by omega), if_pos h2]

theorem tagNWidth_rung6 {i : Nat} (h1 : tagNRung5End ≤ i) : tagNWidth i = 9 := by
  rw [tagNRung5End_eq] at h1
  rw [tagNWidth_eq, if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (by omega), if_neg (by omega)]

/-- The Share width is the `f = 4` instance of the TagN width function. -/
theorem tagNWidth_eq_byteWidth : tagNWidth = Ixon.tagNByteWidth 4 := rfl

/-- `tagNWidth` is the length of the `f = 4` TagN encoding of the index
(the Share code, flag `0xB`), which the decoder reads back exactly. -/
theorem tagNWidth_eq_encoded (i : UInt64) :
    tagNWidth i.toNat = (Ixon.runPut (Ixon.putTagN 4 0xB i)).size ∧
      Ixon.runGetExact (Ixon.getTagN 4) (Ixon.runPut (Ixon.putTagN 4 0xB i)) =
        .ok ⟨0xB, i⟩ :=
  ⟨(Codec.runPut_putTagN_size 4 0xB i).symm,
    Codec.runGetExact_getTagN_putTagN 4 (by decide) 0xB (by decide) i⟩

/-! ## Expression length -/

/-- Length of the production encoding of an expression. -/
def S (e : Ixon.Expr) : Nat := (spineWireEncode e).size

theorem exprListBytes_size (enc : Ixon.Expr → ByteArray) (xs : List Ixon.Expr) :
    (exprListBytes enc xs).size = (xs.map fun e => (enc e).size).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [exprListBytes, ih]

theorem lamBinderListBytes_size (enc : Ixon.Expr → ByteArray)
    (bs : List (Ixon.BinderContract × Ixon.Expr)) :
    (lamBinderListBytes enc bs).size = (bs.map fun b => 1 + (enc b.2).size).sum := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    obtain ⟨u, ty⟩ := b
    simp [lamBinderListBytes, ih]
    all_goals omega

theorem allBinderListBytes_size (enc : Ixon.Expr → ByteArray)
    (bs : List (Ixon.BinderContract × Ixon.ValueContract × Ixon.Expr)) :
    (allBinderListBytes enc bs).size = (bs.map fun b => 1 + (enc b.2.2).size).sum := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    obtain ⟨u, o, ty⟩ := b
    simp [allBinderListBytes, ih]
    all_goals omega

theorem tag0ListBytes_size (xs : List UInt64) :
    (tag0ListBytes xs).size = (xs.map fun u => tag0Size u.toNat).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [tag0ListBytes, ih, tag0Bytes_size]

theorem univIdxsSize_eq (us : Array UInt64) :
    univIdxsSize us = (us.toList.map fun u => tag0Size u.toNat).sum := by
  unfold univIdxsSize
  rw [← Array.foldl_toList]
  generalize us.toList = xs
  suffices h : ∀ acc, xs.foldl (fun acc u => acc + tag0Size u.toNat) acc =
      acc + (xs.map fun u => tag0Size u.toNat).sum by simpa using h 0
  induction xs with
  | nil => simp
  | cons x xs ih => intro acc; simp [ih]; omega

/-- What `sizeInfo` computes for an expression: its full length and the
three telescope continuations. -/
def Spec (i : SizeInfo) (e : Ixon.Expr) : Prop :=
  i.full = S e ∧
  i.appCont = (e.collectAppArgs.1.length,
    S e.collectAppArgs.2 + (e.collectAppArgs.1.map S).sum) ∧
  i.lamCont = (e.collectLamBinders.1.length,
    (e.collectLamBinders.1.map fun b => 1 + S b.2).sum + S e.collectLamBinders.2) ∧
  i.allCont = (e.collectAllBinders.1.length,
    (e.collectAllBinders.1.map fun b => 1 + S b.2.2).sum + S e.collectAllBinders.2)

/-- A node that continues no telescope satisfies the spec once its length
is right. -/
theorem spec_plain (e : Ixon.Expr) (n : Nat) (hn : n = S e)
    (ha : e.collectAppArgs = ([], e)) (hl : e.collectLamBinders = ([], e))
    (hal : e.collectAllBinders = ([], e)) : Spec (.plain n) e := by
  simp [Spec, SizeInfo.plain, ha, hl, hal, hn]

theorem toNat_toUInt64_of_lt {n : Nat} (h : n < UInt64.size) : n.toUInt64.toNat = n := by
  simp [Nat.toUInt64, Nat.mod_eq_of_lt h]

theorem exprListBytes_size_S (xs : List Ixon.Expr) :
    (exprListBytes spineWireEncode xs).size = (xs.map S).sum :=
  exprListBytes_size spineWireEncode xs

theorem lamBinderListBytes_size_S (bs : List (Ixon.BinderContract × Ixon.Expr)) :
    (lamBinderListBytes spineWireEncode bs).size = (bs.map fun b => 1 + S b.2).sum :=
  lamBinderListBytes_size spineWireEncode bs

theorem allBinderListBytes_size_S
    (bs : List (Ixon.BinderContract × Ixon.ValueContract × Ixon.Expr)) :
    (allBinderListBytes spineWireEncode bs).size = (bs.map fun b => 1 + S b.2.2).sum :=
  allBinderListBytes_size spineWireEncode bs

theorem S_def (e : Ixon.Expr) : S e = (spineWireEncode e).size := rfl

theorem map_S_eq (l : List Ixon.Expr) :
    l.map S = l.map fun e => (spineWireEncode e).size := rfl

theorem sum_map_const_one {α : Type} (l : List α) : (l.map fun _ => 1).sum = l.length := by
  induction l with
  | nil => rfl
  | cons x xs ih => simp [ih]; omega

/-- The size facts of a telescope node keep their full length in the
continuations of the other families. -/
theorem sizeInfoWith_app_lamCont (sc : Nat → Nat) (f a : Ixon.Expr) :
    (sizeInfoWith sc (.app f a)).lamCont = (0, (sizeInfoWith sc (.app f a)).full) := rfl
theorem sizeInfoWith_app_allCont (sc : Nat → Nat) (f a : Ixon.Expr) :
    (sizeInfoWith sc (.app f a)).allCont = (0, (sizeInfoWith sc (.app f a)).full) := rfl
theorem sizeInfoWith_lam_appCont (sc : Nat → Nat) (c : Ixon.BinderContract) (t b : Ixon.Expr) :
    (sizeInfoWith sc (.lam c t b)).appCont = (0, (sizeInfoWith sc (.lam c t b)).full) := rfl
theorem sizeInfoWith_lam_allCont (sc : Nat → Nat) (c : Ixon.BinderContract) (t b : Ixon.Expr) :
    (sizeInfoWith sc (.lam c t b)).allCont = (0, (sizeInfoWith sc (.lam c t b)).full) := rfl
theorem sizeInfoWith_all_appCont (sc : Nat → Nat) (c : Ixon.BinderContract)
    (r : Ixon.ValueContract) (t b : Ixon.Expr) :
    (sizeInfoWith sc (.all c r t b)).appCont = (0, (sizeInfoWith sc (.all c r t b)).full) := rfl
theorem sizeInfoWith_all_lamCont (sc : Nat → Nat) (c : Ixon.BinderContract)
    (r : Ixon.ValueContract) (t b : Ixon.Expr) :
    (sizeInfoWith sc (.all c r t b)).lamCont = (0, (sizeInfoWith sc (.all c r t b)).full) := rfl

theorem sizeInfoWith_app_full (sc : Nat → Nat) (f a : Ixon.Expr) :
    (sizeInfoWith sc (.app f a)).full =
      tag4Size ((sizeInfoWith sc f).appCont.1 + 1) +
        ((sizeInfoWith sc f).appCont.2 + (sizeInfoWith sc a).full) := rfl
theorem sizeInfoWith_app_appCont (sc : Nat → Nat) (f a : Ixon.Expr) :
    (sizeInfoWith sc (.app f a)).appCont =
      ((sizeInfoWith sc f).appCont.1 + 1,
        (sizeInfoWith sc f).appCont.2 + (sizeInfoWith sc a).full) := rfl
theorem sizeInfoWith_lam_full (sc : Nat → Nat) (c : Ixon.BinderContract) (t b : Ixon.Expr) :
    (sizeInfoWith sc (.lam c t b)).full =
      tag4Size ((sizeInfoWith sc b).lamCont.1 + 1) +
        (1 + (sizeInfoWith sc t).full + (sizeInfoWith sc b).lamCont.2) := rfl
theorem sizeInfoWith_lam_lamCont (sc : Nat → Nat) (c : Ixon.BinderContract) (t b : Ixon.Expr) :
    (sizeInfoWith sc (.lam c t b)).lamCont =
      ((sizeInfoWith sc b).lamCont.1 + 1,
        1 + (sizeInfoWith sc t).full + (sizeInfoWith sc b).lamCont.2) := rfl
theorem sizeInfoWith_all_full (sc : Nat → Nat) (c : Ixon.BinderContract)
    (r : Ixon.ValueContract) (t b : Ixon.Expr) :
    (sizeInfoWith sc (.all c r t b)).full =
      tag4Size ((sizeInfoWith sc b).allCont.1 + 1) +
        (1 + (sizeInfoWith sc t).full + (sizeInfoWith sc b).allCont.2) := rfl
theorem sizeInfoWith_all_allCont (sc : Nat → Nat) (c : Ixon.BinderContract)
    (r : Ixon.ValueContract) (t b : Ixon.Expr) :
    (sizeInfoWith sc (.all c r t b)).allCont =
      ((sizeInfoWith sc b).allCont.1 + 1,
        1 + (sizeInfoWith sc t).full + (sizeInfoWith sc b).allCont.2) := rfl

theorem sizeInfo_spec (e : Ixon.Expr) (h : e.wireWF) : Spec (sizeInfoWith tag4Size e) e := by
  induction e with
  | sort i =>
    exact spec_plain _ _ (by simp [S, spineWireEncode, tag4Bytes_size]) rfl rfl rfl
  | var i =>
    exact spec_plain _ _ (by simp [S, spineWireEncode, tag4Bytes_size]) rfl rfl rfl
  | str i =>
    exact spec_plain _ _ (by simp [S, spineWireEncode, tag4Bytes_size]) rfl rfl rfl
  | nat i =>
    exact spec_plain _ _ (by simp [S, spineWireEncode, tag4Bytes_size]) rfl rfl rfl
  | share i =>
    exact spec_plain _ _ (by simp [S, spineWireEncode, tag4Bytes_size]) rfl rfl rfl
  | ref r us =>
    have hus : us.size < UInt64.size := h
    exact spec_plain _ _ (by
      simp [S, spineWireEncode, tag4Bytes_size, tag0Bytes_size, tag0ListBytes_size,
        univIdxsSize_eq, toNat_toUInt64_of_lt hus]
      all_goals omega) rfl rfl rfl
  | recur r us =>
    have hus : us.size < UInt64.size := h
    exact spec_plain _ _ (by
      simp [S, spineWireEncode, tag4Bytes_size, tag0Bytes_size, tag0ListBytes_size,
        univIdxsSize_eq, toNat_toUInt64_of_lt hus]
      all_goals omega) rfl rfl rfl
  | prj t f v ih =>
    have hv : (sizeInfoWith tag4Size v).full = (spineWireEncode v).size := (ih h).1
    exact spec_plain _ _ (by
      simp only [sizeInfoWith, hv, S, spineWireEncode, ByteArray.size_append,
        tag4Bytes_size, tag0Bytes_size]) rfl rfl rfl
  | letE c ty v body iht ihv ihb =>
    have h1 : (sizeInfoWith tag4Size ty).full = (spineWireEncode ty).size := (iht h.1).1
    have h2 : (sizeInfoWith tag4Size v).full = (spineWireEncode v).size := (ihv h.2.1).1
    have h3 : (sizeInfoWith tag4Size body).full = (spineWireEncode body).size := (ihb h.2.2).1
    exact spec_plain _ _ (by
      simp only [sizeInfoWith, h1, h2, h3, S, spineWireEncode, ByteArray.size_append,
        tag4Bytes_size, List.size_toByteArray, List.length_singleton]
      omega) rfl rfl rfl
  | app f a ihf iha =>
    obtain ⟨hf, ha, hcount⟩ := h
    obtain ⟨_, hfApp, _, _⟩ := ihf hf
    have haFull : (sizeInfoWith tag4Size a).full = S a := (iha ha).1
    have hlenLt : f.collectAppArgs.1.length + 1 < UInt64.size := by
      rw [collectAppArgs_length]; exact hcount
    have hS : S (.app f a) = tag4Size (f.collectAppArgs.1.length + 1) +
        (S f.collectAppArgs.2 + ((f.collectAppArgs.1.map S).sum + S a)) := by
      rw [S_def, spineWireEncode_app]
      simp only [← S_def, ByteArray.size_append, tag4Bytes_size, exprListBytes_size_S, Ixon.Expr.collectAppArgs, List.length_append,
        List.length_singleton, toNat_toUInt64_of_lt hlenLt, List.map_append,
        List.sum_append, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
      omega
    have hfull : (sizeInfoWith tag4Size (.app f a)).full = S (.app f a) := by
      rw [sizeInfoWith_app_full]
      simp only [hfApp, haFull, hS]
      omega
    refine ⟨hfull, ?_, ?_, ?_⟩
    · rw [sizeInfoWith_app_appCont, hfApp, haFull]
      simp only [Ixon.Expr.collectAppArgs, List.length_append, List.length_singleton,
        List.map_append, List.sum_append, List.map_cons, List.map_nil, List.sum_cons,
        List.sum_nil, Prod.mk.injEq]
      constructor <;> first | trivial | omega
    · rw [sizeInfoWith_app_lamCont, hfull]
      simp [Ixon.Expr.collectLamBinders]
    · rw [sizeInfoWith_app_allCont, hfull]
      simp [Ixon.Expr.collectAllBinders]
  | lam c ty body iht ihb =>
    obtain ⟨ht, hb, hcount⟩ := h
    have htFull : (sizeInfoWith tag4Size ty).full = S ty := (iht ht).1
    obtain ⟨_, _, hbLam, _⟩ := ihb hb
    have hlenLt : body.collectLamBinders.1.length + 1 < UInt64.size := by
      rw [collectLamBinders_length]; exact hcount
    have hS : S (.lam c ty body) = tag4Size (body.collectLamBinders.1.length + 1) +
        (1 + S ty + ((body.collectLamBinders.1.map fun b => 1 + S b.2).sum +
          S body.collectLamBinders.2)) := by
      rw [S_def, spineWireEncode_lam]
      simp only [← S_def, ByteArray.size_append, tag4Bytes_size, lamBinderListBytes_size_S, Ixon.Expr.collectLamBinders, List.length_cons,
        toNat_toUInt64_of_lt hlenLt, List.map_cons, List.sum_cons]
      omega
    have hfull : (sizeInfoWith tag4Size (.lam c ty body)).full = S (.lam c ty body) := by
      rw [sizeInfoWith_lam_full, hbLam, htFull, hS]
    refine ⟨hfull, ?_, ?_, ?_⟩
    · rw [sizeInfoWith_lam_appCont, hfull]
      simp [Ixon.Expr.collectAppArgs]
    · rw [sizeInfoWith_lam_lamCont, hbLam, htFull]
      simp only [Ixon.Expr.collectLamBinders, List.length_cons, List.map_cons,
        List.sum_cons, Prod.mk.injEq]
      constructor <;> first | trivial | omega
    · rw [sizeInfoWith_lam_allCont, hfull]
      simp [Ixon.Expr.collectAllBinders]
  | all c r ty body iht ihb =>
    obtain ⟨ht, hb, hcount⟩ := h
    have htFull : (sizeInfoWith tag4Size ty).full = S ty := (iht ht).1
    obtain ⟨_, _, _, hbAll⟩ := ihb hb
    have hlenLt : body.collectAllBinders.1.length + 1 < UInt64.size := by
      rw [collectAllBinders_length]; exact hcount
    have hS : S (.all c r ty body) = tag4Size (body.collectAllBinders.1.length + 1) +
        (1 + S ty + ((body.collectAllBinders.1.map fun b => 1 + S b.2.2).sum +
          S body.collectAllBinders.2)) := by
      rw [S_def, spineWireEncode_all]
      simp only [← S_def, ByteArray.size_append, tag4Bytes_size, allBinderListBytes_size_S, Ixon.Expr.collectAllBinders, List.length_cons,
        toNat_toUInt64_of_lt hlenLt, List.map_cons, List.sum_cons]
      omega
    have hfull : (sizeInfoWith tag4Size (.all c r ty body)).full = S (.all c r ty body) := by
      rw [sizeInfoWith_all_full, hbAll, htFull, hS]
    refine ⟨hfull, ?_, ?_, ?_⟩
    · rw [sizeInfoWith_all_appCont, hfull]
      simp [Ixon.Expr.collectAppArgs]
    · rw [sizeInfoWith_all_lamCont, hfull]
      simp [Ixon.Expr.collectLamBinders]
    · rw [sizeInfoWith_all_allCont, hbAll, htFull]
      simp only [Ixon.Expr.collectAllBinders, List.length_cons, List.map_cons,
        List.sum_cons, Prod.mk.injEq]
      constructor <;> first | trivial | omega

/-- `exprSize` is the length of the production expression encoding, for
every expression in the codec's wire domain. -/
theorem exprSize_eq_spineWireEncode (e : Ixon.Expr) (h : e.wireWF) :
    exprSize e = (spineWireEncode e).size :=
  (sizeInfo_spec e h).1

/-- `exprSize` is the length of what `putExpr` writes. -/
theorem exprSize_eq_serExpr (e : Ixon.Expr) (h : e.wireWF) :
    exprSize e = (Ixon.runPut (Ixon.putExpr e)).size := by
  rw [exprSize_eq_spineWireEncode e h, ← serExpr_eq_spineWireEncode e h]
  rfl

/-! ## Complete-Constant length -/

section ConstantLength

open Ix.Compile.Verify.Codec.Ixon.Constant
open Ix.Compile.Verify.Codec.Ixon.ConstantTables
open Ix.Compile.Verify.Codec.Ixon.NonrecursiveConstant
open Ix.Compile.Verify.Codec.Ixon.RecursorConstant
open Ix.Compile.Verify.Codec.Ixon.MutualConstant

theorem listBytes_size {α : Type} (enc : α → ByteArray) (xs : List α) :
    (listBytes enc xs).size = (xs.map fun x => (enc x).size).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [listBytes, ih]

theorem sum_map_add {α : Type} (xs : List α) (f g : α → Nat) :
    (xs.map fun x => f x + g x).sum = (xs.map f).sum + (xs.map g).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [ih]; omega

/-- Root-free bytes of a recursor rule, constructor, recursor, inductive. -/
def ruleFixed (rl : Ixon.RecursorRule) : Nat := tag0Size rl.fields.toNat

def ctorFixed (c : Ixon.Constructor) : Nat :=
  1 + tag0Size c.lvls.toNat + tag0Size c.cidx.toNat + tag0Size c.params.toNat +
    tag0Size c.fields.toNat

def recFixed (r : Ixon.Recursor) : Nat :=
  1 + tag0Size r.lvls.toNat + tag0Size r.params.toNat + tag0Size r.indices.toNat +
    tag0Size r.motives.toNat + tag0Size r.minors.toNat +
    tag0Size r.rules.size.toUInt64.toNat + (r.rules.toList.map ruleFixed).sum

def indFixed (i : Ixon.Inductive) : Nat :=
  1 + tag0Size i.lvls.toNat + tag0Size i.params.toNat + tag0Size i.indices.toNat +
    tag0Size i.ctors.size.toUInt64.toNat + (i.ctors.toList.map ctorFixed).sum

def memberFixed : Ixon.MutConst → Nat
  | .defn d => 1 + (1 + tag0Size d.lvls.toNat)
  | .indc i => 1 + indFixed i
  | .recr r => 1 + recFixed r

/-- Bytes of a `ConstantInfo` encoding that are not expression roots. -/
def infoFixed : Ixon.ConstantInfo → Nat
  | .defn d => tag4Size 0 + (1 + tag0Size d.lvls.toNat)
  | .recr r => tag4Size 1 + recFixed r
  | .axio a => tag4Size 2 + (1 + tag0Size a.lvls.toNat)
  | .quot q => tag4Size 3 + (1 + tag0Size q.lvls.toNat)
  | .muts ms => tag4Size ms.size.toUInt64.toNat + (ms.toList.map memberFixed).sum
  | info => (constantInfoBytes info).size

theorem rules_bytes (f : Ixon.Expr → Ixon.Expr) (rules : Array Ixon.RecursorRule) :
    (listBytes recursorRuleBytes (rules.map fun rl => { rl with rhs := f rl.rhs }).toList).size =
      (rules.toList.map ruleFixed).sum + ((rules.toList.map (·.rhs)).map fun r => S (f r)).sum := by
  rw [listBytes_size, Array.toList_map, List.map_map, List.map_map]
  simp only [Function.comp_def, recursorRuleBytes, ByteArray.size_append, tag0Bytes_size]
  rw [sum_map_add]
  rfl

theorem ctors_bytes (f : Ixon.Expr → Ixon.Expr) (ctors : Array Ixon.Constructor) :
    (listBytes constructorBytes (ctors.map fun c => { c with typ := f c.typ }).toList).size =
      (ctors.toList.map ctorFixed).sum + ((ctors.toList.map (·.typ)).map fun r => S (f r)).sum := by
  rw [listBytes_size, Array.toList_map, List.map_map, List.map_map]
  simp only [Function.comp_def, constructorBytes, ByteArray.size_append, tag0Bytes_size,
    List.size_toByteArray, List.length_singleton]
  rw [← sum_map_add]
  congr 1

theorem recursorBytes_map (f : Ixon.Expr → Ixon.Expr) (r : Ixon.Recursor) :
    (recursorBytes
        { r with
          typ := f r.typ,
          rules := r.rules.map fun rl => { rl with rhs := f rl.rhs } }).size =
      recFixed r + (((r.typ :: r.rules.toList.map (·.rhs))).map fun e => S (f e)).sum := by
  simp only [recursorBytes, ByteArray.size_append, tag0Bytes_size, List.size_toByteArray,
    List.length_singleton, Array.size_map, rules_bytes, recFixed, List.map_cons, List.sum_cons]
  simp only [S]
  omega

theorem inductiveBytes_map (f : Ixon.Expr → Ixon.Expr) (i : Ixon.Inductive) :
    (inductiveBytes
        { i with
          typ := f i.typ,
          ctors := i.ctors.map fun c => { c with typ := f c.typ } }).size =
      indFixed i + (((i.typ :: i.ctors.toList.map (·.typ))).map fun e => S (f e)).sum := by
  simp only [inductiveBytes, ByteArray.size_append, tag0Bytes_size, List.size_toByteArray,
    List.length_singleton, Array.size_map, ctors_bytes, indFixed, List.map_cons, List.sum_cons]
  simp only [S]
  omega

theorem memberBytes_map (f : Ixon.Expr → Ixon.Expr) (m : Ixon.MutConst) :
    (mutConstBytes (mapMutConstRoots f m)).size =
      memberFixed m + ((mutConstRoots m).map fun e => S (f e)).sum := by
  cases m with
  | defn d =>
    simp only [mapMutConstRoots, mutConstBytes, definitionBytes, ByteArray.size_append,
      List.size_toByteArray, List.length_singleton, tag0Bytes_size, memberFixed, mutConstRoots,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    simp only [S]
    omega
  | indc i =>
    simp only [mapMutConstRoots, mutConstBytes, ByteArray.size_append, List.size_toByteArray,
      List.length_singleton, inductiveBytes_map, memberFixed, mutConstRoots]
    simp only [List.map_cons, List.map_map, Function.comp_def]
    omega
  | recr r =>
    simp only [mapMutConstRoots, mutConstBytes, ByteArray.size_append, List.size_toByteArray,
      List.length_singleton, recursorBytes_map, memberFixed, mutConstRoots]
    simp only [List.map_cons, List.map_map, Function.comp_def]
    omega

theorem members_bytes (f : Ixon.Expr → Ixon.Expr) (ms : List Ixon.MutConst) :
    (listBytes mutConstBytes (ms.map (mapMutConstRoots f))).size =
      (ms.map memberFixed).sum + ((ms.flatMap mutConstRoots).map fun e => S (f e)).sum := by
  induction ms with
  | nil => rfl
  | cons m ms ih =>
    simp only [List.map_cons, listBytes, ByteArray.size_append, memberBytes_map, ih,
      List.flatMap_cons, List.map_append, List.sum_append, List.sum_cons]
    omega

/-- The info bytes are the root-free bytes plus the roots' encodings, for any
map applied to the roots. -/
theorem infoBytes_mapRoots (f : Ixon.Expr → Ixon.Expr) (info : Ixon.ConstantInfo) :
    (constantInfoBytes (mapRoots f info)).size =
      infoFixed info + ((constantInfoRoots info).toList.map fun e => S (f e)).sum := by
  cases info with
  | defn d =>
    simp only [mapRoots, constantInfoBytes, standaloneInfoBytes, nonrecursiveInfoBytes,
      definitionBytes, Ixon.ConstantInfo.CONST_DEFN, UInt64.reduceToNat, ByteArray.size_append, tag4Bytes_size, List.size_toByteArray,
      List.length_singleton, tag0Bytes_size, infoFixed, constantInfoRoots, mutConstRoots,
      List.toList_toArray, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    simp only [S]
    omega
  | recr r =>
    simp only [mapRoots, constantInfoBytes, standaloneInfoBytes, ByteArray.size_append,
      Ixon.ConstantInfo.CONST_RECR, UInt64.reduceToNat, tag4Bytes_size, recursorBytes_map, infoFixed, constantInfoRoots, mutConstRoots,
      List.toList_toArray]
    omega
  | axio a =>
    simp only [mapRoots, constantInfoBytes, standaloneInfoBytes, nonrecursiveInfoBytes,
      axiomBytes, Ixon.ConstantInfo.CONST_AXIO, UInt64.reduceToNat, ByteArray.size_append, tag4Bytes_size, List.size_toByteArray,
      List.length_singleton, tag0Bytes_size, infoFixed, constantInfoRoots,
      List.toList_toArray, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    simp only [S]
    omega
  | quot q =>
    simp only [mapRoots, constantInfoBytes, standaloneInfoBytes, nonrecursiveInfoBytes,
      quotientBytes, Ixon.ConstantInfo.CONST_QUOT, UInt64.reduceToNat, ByteArray.size_append, tag4Bytes_size, List.size_toByteArray,
      List.length_singleton, tag0Bytes_size, infoFixed, constantInfoRoots,
      List.toList_toArray, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    simp only [S]
    omega
  | cPrj p => simp [mapRoots, infoFixed, constantInfoRoots]
  | rPrj p => simp [mapRoots, infoFixed, constantInfoRoots]
  | iPrj p => simp [mapRoots, infoFixed, constantInfoRoots]
  | dPrj p => simp [mapRoots, infoFixed, constantInfoRoots]
  | muts ms =>
    simp only [mapRoots, constantInfoBytes, ByteArray.size_append, tag4Bytes_size,
      Array.size_map, Array.toList_map, members_bytes, infoFixed, constantInfoRoots,
      List.toList_toArray]
    omega

theorem mapMutConstRoots_id (m : Ixon.MutConst) : mapMutConstRoots (fun e => e) m = m := by
  cases m <;> simp [mapMutConstRoots]

theorem mapRoots_id (info : Ixon.ConstantInfo) : mapRoots (fun e => e) info = info := by
  have hm : (mapMutConstRoots fun e => e) = id := funext mapMutConstRoots_id
  cases info <;> simp [mapRoots, hm]

/-- The info bytes are the root-free bytes plus the roots' encodings. -/
theorem infoBytes_size (info : Ixon.ConstantInfo) :
    (constantInfoBytes info).size = infoFixed info + ((constantInfoRoots info).toList.map S).sum := by
  have h := infoBytes_mapRoots (fun e => e) info
  rw [mapRoots_id] at h
  exact h

theorem mutConstRoots_wireWF (m : Ixon.MutConst) (h : m.wireWF) :
    ∀ e ∈ mutConstRoots m, e.wireWF := by
  cases m with
  | defn d =>
    obtain ⟨ht, hv⟩ := h
    intro e he
    simp only [mutConstRoots, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl <;> assumption
  | indc i =>
    obtain ⟨ht, _, hc⟩ := h
    intro e he
    simp only [mutConstRoots, List.mem_cons, List.mem_map] at he
    rcases he with rfl | ⟨c, hcm, rfl⟩
    · exact ht
    · exact hc c (Array.mem_toList_iff.mp hcm)
  | recr r =>
    obtain ⟨ht, _, hr⟩ := h
    intro e he
    simp only [mutConstRoots, List.mem_cons, List.mem_map] at he
    rcases he with rfl | ⟨rl, hrl, rfl⟩
    · exact ht
    · exact hr rl (Array.mem_toList_iff.mp hrl)

/-- Every root of a wire-well-formed `ConstantInfo` is wire-well-formed. -/
theorem constantInfoRoots_wireWF (info : Ixon.ConstantInfo) (h : info.wireWF) :
    ∀ e ∈ (constantInfoRoots info).toList, e.wireWF := by
  cases info with
  | defn d => exact mutConstRoots_wireWF (.defn d) h
  | recr r => exact mutConstRoots_wireWF (.recr r) h
  | axio a =>
    intro e he
    simp only [constantInfoRoots, List.toList_toArray, List.mem_cons, List.not_mem_nil,
      or_false] at he
    subst he; exact h
  | quot q =>
    intro e he
    simp only [constantInfoRoots, List.toList_toArray, List.mem_cons, List.not_mem_nil,
      or_false] at he
    subst he; exact h
  | cPrj p | rPrj p | iPrj p | dPrj p => intro e he; simp [constantInfoRoots] at he
  | muts ms =>
    obtain ⟨_, hms⟩ := h
    intro e he
    simp only [constantInfoRoots, List.toList_toArray, List.mem_flatMap] at he
    obtain ⟨m, hm, he⟩ := he
    exact mutConstRoots_wireWF m (hms m (Array.mem_toList_iff.mp hm)) e he

theorem mapMutConstRoots_wireWF (f : Ixon.Expr → Ixon.Expr) (hf : ∀ e, (f e).wireWF)
    (m : Ixon.MutConst) (h : m.wireWF) : (mapMutConstRoots f m).wireWF := by
  cases m with
  | defn d => exact ⟨hf _, hf _⟩
  | indc i =>
    obtain ⟨_, hsize, _⟩ := h
    refine ⟨hf _, by simpa using hsize, ?_⟩
    intro c hc
    obtain ⟨c0, _, rfl⟩ := Array.mem_map.mp hc
    exact hf _
  | recr r =>
    obtain ⟨_, hsize, _⟩ := h
    refine ⟨hf _, by simpa using hsize, ?_⟩
    intro rl hrl
    obtain ⟨rl0, _, rfl⟩ := Array.mem_map.mp hrl
    exact hf _

theorem mapRoots_wireWF (f : Ixon.Expr → Ixon.Expr) (hf : ∀ e, (f e).wireWF)
    (info : Ixon.ConstantInfo) (h : info.wireWF) : (mapRoots f info).wireWF := by
  cases info with
  | defn d => exact mapMutConstRoots_wireWF f hf (.defn d) h
  | recr r => exact mapMutConstRoots_wireWF f hf (.recr r) h
  | axio a => exact hf _
  | quot q => exact hf _
  | cPrj p | rPrj p | iPrj p | dPrj p => exact h
  | muts ms =>
    obtain ⟨hsize, hms⟩ := h
    refine ⟨by simpa using hsize, ?_⟩
    intro m hm
    obtain ⟨m0, hm0, rfl⟩ := Array.mem_map.mp hm
    exact mapMutConstRoots_wireWF f hf m0 (hms m0 hm0)

theorem exprsSize_eq (es : Array Ixon.Expr) (h : ∀ e ∈ es, e.wireWF) :
    exprsSize es = (es.toList.map S).sum := by
  unfold exprsSize
  rw [← Array.foldl_toList]
  have h' : ∀ e ∈ es.toList, e.wireWF := fun e he => h e (Array.mem_toList_iff.mp he)
  generalize es.toList = xs at h'
  suffices hs : ∀ acc, xs.foldl (fun acc e => acc + exprSize e) acc = acc + (xs.map S).sum by
    simpa using hs 0
  induction xs with
  | nil => simp
  | cons x xs ih =>
    intro acc
    simp only [List.foldl_cons, List.map_cons, List.sum_cons]
    rw [ih (fun e he => h' e (List.mem_cons_of_mem x he)),
      exprSize_eq_spineWireEncode x (h' x (List.mem_cons_self))]
    simp only [S]
    omega

/-- `putConstant` writes `constantBytes` for every wire-well-formed Constant. -/
theorem serConstant_eq_constantBytes (c : Ixon.Constant) (h : c.wireWF) :
    Ixon.serConstant c = Ix.Compile.Verify.Codec.Ixon.MutualConstant.constantBytes c := by
  have hw := putConstant_writes c ((constantWireWF_iff_catalog c).mpr h) ByteArray.empty
  simp only [Ixon.serConstant, Ixon.runPut, hw, ByteArray.empty_append]

theorem constantBytes_size (c : Ixon.Constant) :
    (Ix.Compile.Verify.Codec.Ixon.MutualConstant.constantBytes c).size =
      (constantInfoBytes c.info).size + tag0Size c.sharing.size.toUInt64.toNat +
        (c.sharing.toList.map S).sum +
          ((tag0Bytes c.refs.size.toUInt64).size + (listBytes Address.hash c.refs.toList).size +
            (tag0Bytes c.univs.size.toUInt64).size +
              (listBytes Ix.Compile.Verify.Codec.Ixon.Univ.wireEncode c.univs.toList).size) := by
  simp only [Ix.Compile.Verify.Codec.Ixon.MutualConstant.constantBytes, ByteArray.size_append,
    tag0Bytes_size, listBytes_size]
  rw [map_S_eq]
  omega

theorem S_var_zero : S (.var 0) = 1 := by
  simp [S, spineWireEncode, tag4Bytes_size, tag4Size, Ixon.tagNByteWidth, TagN.tagNEnd1_eq_4]

/-- The complete-Constant length decomposes into the root-free bytes
(`fixedConstantBytes`), the roots, the table count and the table bodies. -/
theorem serConstant_size_decomposition (c : Ixon.Constant) (h : c.wireWF) :
    (Ixon.serConstant c).size =
      fixedConstantBytes c + exprsSize (constantInfoRoots c.info) + tag0Size c.sharing.size +
        exprsSize c.sharing := by
  obtain ⟨hinfo, hsharingSize, hsharing, hrefsSize, hrefs, hunivsSize, hunivs⟩ := h
  let c' : Ixon.Constant :=
    { c with info := mapRoots (fun _ => Ixon.Expr.var 0) c.info, sharing := #[] }
  have h' : c'.wireWF := by
    refine ⟨mapRoots_wireWF (fun _ => Ixon.Expr.var 0)
      (fun _ => by unfold Ixon.Expr.wireWF; trivial) _ hinfo,
      by simp [c'], ?_, hrefsSize, hrefs,
      hunivsSize, hunivs⟩
    intro e he
    simp [c'] at he
  have hc := serConstant_eq_constantBytes c
    ⟨hinfo, hsharingSize, hsharing, hrefsSize, hrefs, hunivsSize, hunivs⟩
  have hc' := serConstant_eq_constantBytes c' h'
  have hfixed : fixedConstantBytes c = (Ixon.serConstant c').size -
      (constantInfoRoots c.info).size - tag0Size 0 := rfl
  have hroots := exprsSize_eq (constantInfoRoots c.info)
    (fun e he => constantInfoRoots_wireWF c.info hinfo e (Array.mem_toList_iff.mpr he))
  have hshare := exprsSize_eq c.sharing hsharing
  have hmap := infoBytes_mapRoots (fun _ => Ixon.Expr.var 0) c.info
  have hbase := infoBytes_size c.info
  have hlen : ((constantInfoRoots c.info).toList.map fun _ => S (.var 0)).sum =
      (constantInfoRoots c.info).size := by
    rw [show (fun (_ : Ixon.Expr) => S (.var 0)) = fun _ => 1 from funext fun _ => S_var_zero,
      sum_map_const_one, Array.length_toList]
  rw [hlen] at hmap
  rw [hfixed, hroots, hshare, hc, hc', constantBytes_size, constantBytes_size]
  have hz : (Nat.toUInt64 0).toNat = 0 := rfl
  simp only [c', toNat_toUInt64_of_lt hsharingSize, List.map_nil, List.sum_nil,
    Array.size_empty, Array.toList_empty, hmap, hbase, hz]
  omega


end ConstantLength


/-! ## Key orders (§3.2, §3.3) -/

section Orders

instance lexCompare_trans : Std.TransCmp lexCompare :=
  inferInstanceAs (Std.TransCmp (List.compareLex (compare : Nat → Nat → Ordering)))

instance lexCompare_lawfulEq : Std.LawfulEqCmp lexCompare :=
  inferInstanceAs (Std.LawfulEqCmp (List.compareLex (compare : Nat → Nat → Ordering)))

/-- `lexCompare` is `eq` exactly on equal vectors. -/
theorem lexCompare_eq_iff (a b : List Nat) : lexCompare a b = .eq ↔ a = b :=
  ⟨Std.LawfulEqCmp.eq_of_compare, fun h => h ▸ Std.ReflCmp.compare_self⟩

/-- Swapping the arguments of `lexCompare` swaps the outcome. -/
theorem lexCompare_swap (a b : List Nat) : lexCompare a b = (lexCompare b a).swap :=
  Std.OrientedCmp.eq_swap

/-- `lexCompare` is transitive. -/
theorem lexCompare_lt_trans {a b c : List Nat} (h₁ : lexCompare a b = .lt)
    (h₂ : lexCompare b c = .lt) : lexCompare a c = .lt :=
  Std.TransCmp.lt_trans h₁ h₂

/-- Comparing by a projection under a transitive comparison is transitive. -/
theorem transCmp_on {α β : Type} (cmp : β → β → Ordering) [Std.TransCmp cmp] (f : α → β) :
    Std.TransCmp (fun a b => cmp (f a) (f b)) where
  eq_swap := Std.OrientedCmp.eq_swap (cmp := cmp)
  isLE_trans h₁ h₂ := Std.TransCmp.isLE_trans (cmp := cmp) h₁ h₂

instance compareBytes_trans : Std.TransCmp compareBytes :=
  transCmp_on (List.compareLex (compare : UInt8 → UInt8 → Ordering)) (fun b : ByteArray => b.data.toList)

instance compareBytes_lawfulEq : Std.LawfulEqCmp compareBytes where
  compare_self {a} := Std.ReflCmp.compare_self (cmp := List.compareLex (compare : UInt8 → UInt8 → Ordering))
  eq_of_compare {a b} h := by
    have hl : a.data.toList = b.data.toList :=
      Std.LawfulEqCmp.eq_of_compare (cmp := List.compareLex (compare : UInt8 → UInt8 → Ordering)) h
    cases a; cases b
    simp only [ByteArray.mk.injEq]
    exact Array.toList_inj.mp hl

/-! ### Structural keys -/

theorem BinderContract.toBits_inj {a b : Ixon.BinderContract} (h : a.toBits = b.toBits) :
    a = b := by
  have := congrArg Ixon.BinderContract.ofBits? h
  simpa using this

theorem packAllContract_inj {c c' : Ixon.BinderContract} {r r' : Ixon.ValueContract}
    (h : Ixon.packAllContract c r = Ixon.packAllContract c' r') : c = c' ∧ r = r' := by
  have := congrArg Ixon.unpackAllContract? h
  simpa using this

theorem LetContract.eq_of_flags {c c' : Ixon.LetContract} (hf : c.flags = c'.flags)
    (hb : c.binder = c'.binder) : c = c' := by
  have h1 := Ixon.LetContract.ofFlags?_flags c
  have h2 := Ixon.LetContract.ofFlags?_flags c'
  rw [hf, hb, h2] at h1
  exact (Option.some.inj h1).symm

theorem map_toNat_inj : ∀ {xs ys : List UInt64},
    xs.map UInt64.toNat = ys.map UInt64.toNat → xs = ys
  | [], [], _ => rfl
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | x :: xs, y :: ys, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    rw [UInt64.toNat_inj.mp h.1, map_toNat_inj h.2]

/-- Heads with equal §3.2 tag and scalar vector are equal. -/
theorem Head.eq_of_tag_scalars {h₁ h₂ : Head} (ht : h₁.tag = h₂.tag)
    (hs : h₁.scalars = h₂.scalars) : h₁ = h₂ := by
  cases h₁ <;> cases h₂ <;> simp only [Head.tag] at ht <;>
    first
    | exact absurd ht (by decide)
    | simp only [Head.scalars, List.cons.injEq, List.nil_eq, and_true] at hs
  case sort.sort i j => rw [UInt64.toNat_inj.mp hs]
  case var.var i j => rw [UInt64.toNat_inj.mp hs]
  case str.str i j => rw [UInt64.toNat_inj.mp hs]
  case nat.nat i j => rw [UInt64.toNat_inj.mp hs]
  case ref.ref r us r' vs =>
    obtain ⟨hr, _, hu⟩ := hs
    rw [UInt64.toNat_inj.mp hr, Array.toList_inj.mp (map_toNat_inj hu)]
  case recur.recur r us r' vs =>
    obtain ⟨hr, _, hu⟩ := hs
    rw [UInt64.toNat_inj.mp hr, Array.toList_inj.mp (map_toNat_inj hu)]
  case prj.prj t f t' f' =>
    obtain ⟨h1, h2⟩ := hs
    rw [UInt64.toNat_inj.mp h1, UInt64.toNat_inj.mp h2]
  case app.app => rfl
  case lam.lam c c' => rw [BinderContract.toBits_inj (UInt8.toNat_inj.mp hs)]
  case all.all c r c' r' =>
    obtain ⟨h1, h2⟩ := packAllContract_inj (UInt8.toNat_inj.mp hs)
    rw [h1, h2]
  case letE.letE c c' =>
    obtain ⟨h1, h2⟩ := hs
    rw [LetContract.eq_of_flags (UInt64.toNat_inj.mp h1)
      (BinderContract.toBits_inj (UInt8.toNat_inj.mp h2))]

/-- Structural keys determine nodes: `compareKey` is `eq` exactly on equal
nodes (collision-free identity). -/
theorem compareKey_eq_iff (x y : Node) : Node.compareKey x y = .eq ↔ x = y := by
  constructor
  · intro h
    simp only [Node.compareKey, Ordering.then_eq_eq] at h
    obtain ⟨ht, hs, hc⟩ := h
    have ht' : x.head.tag = y.head.tag := Std.LawfulEqOrd.eq_of_compare ht
    have hs' : x.head.scalars = y.head.scalars := (lexCompare_eq_iff _ _).mp hs
    have hc' : x.children.toList = y.children.toList := (lexCompare_eq_iff _ _).mp hc
    cases x; cases y
    simp only [Node.mk.injEq]
    exact ⟨Head.eq_of_tag_scalars ht' hs', Array.toList_inj.mp hc'⟩
  · intro h; subst h
    simp only [Node.compareKey, Ordering.then_eq_eq]
    exact ⟨Std.ReflOrd.compare_self, (lexCompare_eq_iff _ _).mpr rfl,
      (lexCompare_eq_iff _ _).mpr rfl⟩

instance compareKey_trans : Std.TransCmp Node.compareKey :=
  have : Std.TransCmp (fun x y : Node => compare x.head.tag y.head.tag) :=
    transCmp_on (compare : Nat → Nat → Ordering) (fun n : Node => n.head.tag)
  have : Std.TransCmp (fun x y : Node => lexCompare x.head.scalars y.head.scalars) :=
    transCmp_on lexCompare (fun n : Node => n.head.scalars)
  have : Std.TransCmp (fun x y : Node => lexCompare x.children.toList y.children.toList) :=
    transCmp_on lexCompare (fun n : Node => n.children.toList)
  inferInstanceAs (Std.TransCmp (_root_.compareLex
    (fun x y : Node => compare x.head.tag y.head.tag)
    (_root_.compareLex (fun x y : Node => lexCompare x.head.scalars y.head.scalars)
      (fun x y : Node => lexCompare x.children.toList y.children.toList))))

instance compareKey_lawfulEq : Std.LawfulEqCmp Node.compareKey where
  compare_self {a} := (compareKey_eq_iff a a).mpr rfl
  eq_of_compare {a b} h := (compareKey_eq_iff a b).mp h

/-! ### Canonical order of a height bucket -/

/-- The bucket comparison of `canonicalize` (`compareKey x y != .gt`). -/
def keyLe (x y : Node) : Bool := (Node.compareKey x y).isLE

theorem keyLe_eq (x y : Node) : (Node.compareKey x y != .gt) = keyLe x y := by
  unfold keyLe; cases Node.compareKey x y <;> rfl

theorem keyLe_trans (a b c : Node) (h₁ : keyLe a b) (h₂ : keyLe b c) : keyLe a c :=
  Std.TransCmp.isLE_trans h₁ h₂

theorem keyLe_total (a b : Node) : keyLe a b || keyLe b a := by
  unfold keyLe
  rw [Std.OrientedCmp.eq_swap (cmp := Node.compareKey) (a := b) (b := a)]
  cases Node.compareKey a b <;> rfl

theorem keyLe_antisymm (a b : Node) (h₁ : keyLe a b) (h₂ : keyLe b a) : a = b := by
  unfold keyLe at h₁ h₂
  rw [Std.OrientedCmp.eq_swap (cmp := Node.compareKey) (a := b) (b := a)] at h₂
  apply (compareKey_eq_iff a b).mp
  revert h₁ h₂
  cases Node.compareKey a b <;> simp [Ordering.isLE, Ordering.swap]

/-- Sorting by the §3.2 key order gives the same list for any two
arrangements of the same nodes: the order of a height bucket, and hence the
IDs assigned to it, depend only on the bucket's keys. -/
theorem keySort_eq_of_perm {l₁ l₂ : List Node} (hp : l₁.Perm l₂) :
    l₁.mergeSort keyLe = l₂.mergeSort keyLe := by
  apply List.Perm.eq_of_pairwise (le := fun a b => keyLe a b = true)
  · intro a b _ _ h₁ h₂; exact keyLe_antisymm a b h₁ h₂
  · exact List.pairwise_mergeSort keyLe_trans keyLe_total l₁
  · exact List.pairwise_mergeSort keyLe_trans keyLe_total l₂
  · exact (List.mergeSort_perm l₁ keyLe).trans (hp.trans (List.mergeSort_perm l₂ keyLe).symm)

end Orders



/-! ## Expansion correctness of materialization -/

section Materialize

/-- Replace every `Share(i)` by `σ i`: the expansion of an encoding whose
table entry `i` expands to `σ i`. -/
def substShares (σ : Nat → Ixon.Expr) : Ixon.Expr → Ixon.Expr
  | .share i => σ i.toNat
  | .prj t f v => .prj t f (substShares σ v)
  | .app f a => .app (substShares σ f) (substShares σ a)
  | .lam c t b => .lam c (substShares σ t) (substShares σ b)
  | .all c r t b => .all c r (substShares σ t) (substShares σ b)
  | .letE c t v b => .letE c (substShares σ t) (substShares σ v) (substShares σ b)
  | e => e

/-- `E` interprets every term of the DAG as the expression its node
describes. -/
def DagModel (dag : Dag) (E : Nat → Ixon.Expr) : Prop :=
  ∀ u, E u = (dag.node u).toExpr E

/-- Every index of the dictionary names a table entry (`σ`) whose expansion
is the term's interpretation. -/
def IndexModel (index : Array (Option Nat)) (E σ : Nat → Ixon.Expr) : Prop :=
  ∀ u i, index[u]?.getD none = some i → i < UInt64.size ∧ σ i = E u

theorem bind_eq_ok {ε α β : Type} {x : Except ε α} {f : α → Except ε β} {b : β}
    (h : (x >>= f) = .ok b) : ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x with
  | error e => cases h
  | ok a => exact ⟨a, rfl, h⟩

theorem share_subst {index : Array (Option Nat)} {E σ : Nat → Ixon.Expr}
    (hσ : IndexModel index E σ) {u i : Nat} (h : index[u]?.getD none = some i) :
    substShares σ (.share i.toUInt64) = E u := by
  obtain ⟨hi, he⟩ := hσ u i h
  simp only [substShares, toNat_toUInt64_of_lt hi, he]

/-- Rebuilding a spine collected by `spineWalk` around correct pieces
gives the interpretation of the spine's top. -/
theorem spineFold_correct (p : Prep) (E σ : Nat → Ixon.Expr) (hE : DagModel p.dag E)
    (buildSide : Node → Except SharingError Ixon.Expr)
    (hside : ∀ n e, buildSide n = .ok e → substShares σ e = E n.sideChild) :
    ∀ (j t : Nat) (tail res : Ixon.Expr),
      substShares σ tail = E (p.spineWalk j t).2 →
      (p.spineWalk j t).1.foldrM
          (fun n acc => do let side ← buildSide n; rebuildSpineNode n acc side) tail = .ok res →
      substShares σ res = E t := by
  intro j
  induction j with
  | zero =>
    intro t tail res htail h
    simp only [Prep.spineWalk, List.foldrM_nil] at htail h
    cases h
    exact htail
  | succ j ih =>
    intro t tail res htail h
    simp only [Prep.spineWalk] at htail h
    rw [List.foldrM_cons] at h
    obtain ⟨acc, hacc, hstep⟩ := bind_eq_ok h
    have hinner := ih (p.dag.node t).spineNext tail acc htail hacc
    obtain ⟨side, hs, hre⟩ := bind_eq_ok hstep
    have hside' := hside _ side hs
    rw [hE t]
    generalize hn : p.dag.node t = n at hinner hside' hre
    cases hh : n.head with
    | app =>
      simp only [rebuildSpineNode, hh] at hre
      cases hre
      simp only [substShares, hinner, hside', Node.toExpr, hh, Node.spineNext, Node.sideChild]
    | lam bc =>
      simp only [rebuildSpineNode, hh] at hre
      cases hre
      simp only [substShares, hinner, hside', Node.toExpr, hh, Node.spineNext, Node.sideChild]
    | all bc r =>
      simp only [rebuildSpineNode, hh] at hre
      cases hre
      simp only [substShares, hinner, hside', Node.toExpr, hh, Node.spineNext, Node.sideChild]
    | _ => simp [rebuildSpineNode, hh] at hre

/-- Every successful materialization is correct: replacing each `Share(i)`
of the built expression by the expansion `σ i` of table entry `i` gives the
interpretation of the requested term. -/
theorem build_correct (p : Prep) (ev : DictEval) (index width : Array (Option Nat))
    (E σ : Nat → Ixon.Expr) (hE : DagModel p.dag E) (hσ : IndexModel index E σ) :
    ∀ (fuel : Nat) (entry : Bool) (t : Nat) (e : Ixon.Expr),
      p.build ev index width entry fuel t = .ok e → substShares σ e = E t := by
  intro fuel
  induction fuel with
  | zero => intro entry t e h; simp [Prep.build] at h
  | succ fuel ih =>
    intro entry t e h
    have hside : ∀ (n : Node) (e' : Ixon.Expr),
        p.build ev index width false fuel n.sideChild = .ok e' →
        substShares σ e' = E n.sideChild := fun n e' h' => ih false n.sideChild e' h'
    simp only [Prep.build] at h
    split at h
    · split at h
      · split at h
        · -- Share
          split at h
          · rename_i i hi
            cases h
            exact share_subst hσ hi
          · cases h
        · -- inline node
          rw [hE t]
          cases hh : (p.dag.node t).head <;> simp only [hh] at h
          case prj ti f =>
            obtain ⟨v, hv, hpure⟩ := bind_eq_ok h
            cases hpure
            simp only [substShares, Node.toExpr, hh, ih false _ v hv]
          case letE lc =>
            obtain ⟨ty, hty, h2⟩ := bind_eq_ok h
            obtain ⟨v, hv, h3⟩ := bind_eq_ok h2
            obtain ⟨b, hb, hpure⟩ := bind_eq_ok h3
            cases hpure
            simp only [substShares, Node.toExpr, hh, ih false _ ty hty, ih false _ v hv,
              ih false _ b hb]
          all_goals first
            | (cases h; simp only [substShares, Node.toExpr, hh])
            | cases h
        · -- telescope cut
          split at h
          · cases h
          split at h
          · split at h
            · rename_i i hi
              simp only [pure_bind] at h
              exact spineFold_correct p E σ hE _ hside _ _ _ _ (share_subst hσ hi) h
            · cases h
          · obtain ⟨tail, htail, hfold⟩ := bind_eq_ok h
            exact spineFold_correct p E σ hE _ hside _ _ _ _ (ih false _ tail htail) hfold
      · cases h
    · cases h


/-- Every `Share` index of an expression satisfies `P`. -/
def SharesIn (P : Nat → Prop) : Ixon.Expr → Prop
  | .share i => P i.toNat
  | .prj _ _ v => SharesIn P v
  | .app f a => SharesIn P f ∧ SharesIn P a
  | .lam _ t b => SharesIn P t ∧ SharesIn P b
  | .all _ _ t b => SharesIn P t ∧ SharesIn P b
  | .letE _ t v b => SharesIn P t ∧ SharesIn P v ∧ SharesIn P b
  | _ => True

theorem spineFold_shares (P : Nat → Prop) (buildSide : Node → Except SharingError Ixon.Expr)
    (hside : ∀ n e, buildSide n = .ok e → SharesIn P e) :
    ∀ (ns : List Node) (tail res : Ixon.Expr), SharesIn P tail →
      ns.foldrM (fun n acc => do let side ← buildSide n; rebuildSpineNode n acc side) tail =
        .ok res → SharesIn P res := by
  intro ns
  induction ns with
  | nil => intro tail res ht h; simp only [List.foldrM_nil] at h; cases h; exact ht
  | cons n ns ih =>
    intro tail res ht h
    rw [List.foldrM_cons] at h
    obtain ⟨acc, hacc, hstep⟩ := bind_eq_ok h
    have hinner := ih tail acc ht hacc
    obtain ⟨side, hs, hre⟩ := bind_eq_ok hstep
    have hside' := hside n side hs
    cases hh : n.head <;> simp only [rebuildSpineNode, hh] at hre <;> cases hre <;>
      exact ⟨by assumption, by assumption⟩

/-- Every `Share` that a successful materialization emits is the index of
some term in its dictionary (so it satisfies any property all those indices
have). -/
theorem build_shares (p : Prep) (ev : DictEval) (index width : Array (Option Nat))
    (P : Nat → Prop)
    (hP : ∀ (u i : Nat), index[u]?.getD none = some i → i < UInt64.size ∧ P i) :
    ∀ (fuel : Nat) (entry : Bool) (t : Nat) (e : Ixon.Expr),
      p.build ev index width entry fuel t = .ok e → SharesIn P e := by
  intro fuel
  induction fuel with
  | zero => intro entry t e h; simp [Prep.build] at h
  | succ fuel ih =>
    intro entry t e h
    have hside : ∀ (n : Node) (e' : Ixon.Expr),
        p.build ev index width false fuel n.sideChild = .ok e' → SharesIn P e' :=
      fun n e' h' => ih false n.sideChild e' h'
    have hshare : ∀ (u i : Nat), index[u]?.getD none = some i →
        SharesIn P (.share i.toUInt64) := by
      intro u i hi
      obtain ⟨hlt, hp⟩ := hP u i hi
      simp only [SharesIn, toNat_toUInt64_of_lt hlt, hp]
    simp only [Prep.build] at h
    split at h
    · split at h
      · split at h
        · split at h
          · rename_i i hi
            cases h
            exact hshare _ _ hi
          · cases h
        · cases hh : (p.dag.node t).head <;> simp only [hh] at h
          case prj ti f =>
            obtain ⟨v, hv, hpure⟩ := bind_eq_ok h
            cases hpure
            exact ih false _ v hv
          case letE lc =>
            obtain ⟨ty, hty, h2⟩ := bind_eq_ok h
            obtain ⟨v, hv, h3⟩ := bind_eq_ok h2
            obtain ⟨b, hb, hpure⟩ := bind_eq_ok h3
            cases hpure
            exact ⟨ih false _ ty hty, ih false _ v hv, ih false _ b hb⟩
          all_goals first
            | (cases h; simp only [SharesIn, Node.toExpr, hh])
            | cases h
        · split at h
          · cases h
          split at h
          · split at h
            · rename_i i hi
              simp only [pure_bind] at h
              exact spineFold_shares P _ hside _ _ _ (hshare _ _ hi) h
            · cases h
          · obtain ⟨tail, htail, hfold⟩ := bind_eq_ok h
            exact spineFold_shares P _ hside _ _ _ (ih false _ tail htail) hfold
      · cases h
    · cases h

theorem indexOfPairs_bound (size k : Nat) (pairs : List (Nat × Nat))
    (h : ∀ x ∈ pairs, x.2 < k) :
    ∀ (u i : Nat), (indexOfPairs size pairs)[u]?.getD none = some i → i < k := by
  unfold indexOfPairs
  suffices hs : ∀ (acc : Array (Option Nat)),
      (∀ (u i : Nat), acc[u]?.getD none = some i → i < k) →
      ∀ (u i : Nat), (pairs.foldl (fun acc (t, i) => acc.set! t (some i)) acc)[u]?.getD none =
        some i → i < k by
    refine hs _ (fun u i hu => ?_)
    simp only [Array.getElem?_replicate] at hu
    split at hu <;> simp at hu
  induction pairs with
  | nil => intro acc hacc; simpa using hacc
  | cons x xs ih =>
    intro acc hacc
    rw [List.foldl_cons]
    apply ih (fun y hy => h y (List.mem_cons_of_mem x hy))
    intro u i hu
    obtain ⟨t, j⟩ := x
    simp only [Array.set!, Array.getElem?_setIfInBounds] at hu
    split at hu
    · split at hu
      · simp at hu
        subst hu
        exact h (t, j) List.mem_cons_self
      · simp at hu
    · exact hacc u i hu

/-- The dictionary of the first `k` table entries only holds indices below
`k`. -/
theorem indexOfPrefix_bound (size : Nat) (table : Array Nat) (k : Nat) :
    ∀ (u i : Nat), (indexOfPrefix size table k)[u]?.getD none = some i → i < k := by
  unfold indexOfPrefix
  apply indexOfPairs_bound
  intro x hx
  obtain ⟨_, hlt, _⟩ := List.mem_zipIdx hx
  simp only [List.length_take, Nat.zero_add] at hlt
  omega

/-- Backward references: building with the dictionary of the first `k`
entries emits only `Share` indices below `k` (for a table entry `k` that
is "strictly earlier", for roots `k` is the table size). -/
theorem build_prefix_backward (p : Prep) (ev : DictEval) (table : Array Nat) (k : Nat)
    (hk : k ≤ UInt64.size) (width : Array (Option Nat)) :
    ∀ (fuel : Nat) (entry : Bool) (t : Nat) (e : Ixon.Expr),
      p.build ev (indexOfPrefix p.dag.size table k) width entry fuel t = .ok e →
        SharesIn (· < k) e :=
  build_shares p ev _ width (· < k) fun u i hi =>
    have := indexOfPrefix_bound p.dag.size table k u i hi
    ⟨by omega, this⟩

theorem forall₂_imp {α β : Type} {R S : α → β → Prop} (hRS : ∀ a b, R a b → S a b) :
    ∀ {xs : List α} {ys : List β}, List.Forall₂ R xs ys → List.Forall₂ S xs ys
  | _, _, .nil => .nil
  | _, _, .cons h hs => .cons (hRS _ _ h) (forall₂_imp hRS hs)

theorem mapM_ok_forall₂ {α β ε : Type} (f : α → Except ε β) :
    ∀ (xs : List α) (ys : List β), xs.mapM f = .ok ys → List.Forall₂ (fun x y => f x = .ok y) xs ys
  | [], ys, h => by simp only [List.mapM_nil] at h; cases h; exact .nil
  | x :: xs, ys, h => by
    rw [List.mapM_cons] at h
    obtain ⟨y, hy, h2⟩ := bind_eq_ok h
    obtain ⟨ys', hys, h3⟩ := bind_eq_ok h2
    cases h3
    exact .cons hy (mapM_ok_forall₂ f xs ys' hys)

/-- Every expression returned by a successful `materializeWith` expands to
its target term. -/
theorem materializeWith_correct (p : Prep) (index width : Array (Option Nat))
    (targets : Array Nat) (limits : Limits) (out : Array Ixon.Expr) (cost : Array Nat) (work : Nat)
    (h : p.materializeWith index width targets limits = .ok (out, cost, work))
    (E σ : Nat → Ixon.Expr) (hE : DagModel p.dag E) (hσ : IndexModel index E σ) :
    List.Forall₂ (fun t e => substShares σ e = E t) targets.toList out.toList := by
  unfold Prep.materializeWith at h
  obtain ⟨_, _, h⟩ := bind_eq_ok h
  simp only at h
  split at h
  · cases h
  · obtain ⟨out', hout, hret⟩ := bind_eq_ok h
    cases hret
    rw [Array.mapM_eq_mapM_toList] at hout
    cases hm : List.mapM (fun t => p.build (p.evalAll width) index width false (p.dag.size + 1) t)
        targets.toList with
    | error err => rw [hm] at hout; cases hout
    | ok l =>
      rw [hm] at hout
      have hout' : out = l.toArray := by
        cases hout; rfl
      subst hout'
      exact forall₂_imp (fun t e he => build_correct p _ index width E σ hE hσ _ false t e he)
        (mapM_ok_forall₂ _ _ _ hm)


end Materialize


end Ix.Compile.Verify.SharingExact
