/-!
# DR3 / DR4 Pure-Lean Semantic Specifications & Conservativity (`IxCC.Src.ArraySpec`)

Pure-Lean operational specifications and conservativity theorems for Lean 4.34.1's
`Array`, `ByteArray`, and UTF-8 `String` primitives (`docs/data-and-roots-design.md`,
§DR3 Arrays & ByteArrays, §DR4 Strings).

Every primitive's specification is defined purely over `List α` / `List UInt8`
(independent of any runtime heap invariant, so both the x86 contiguous-array
runtime `Rt.Rc.Array` and a certified evaluator share one semantic reference)
and formally proved equal to Lean 4.34.1's reference bodies on `Array.toList`,
`ByteArray.data`, and `String.toByteArray`.
-/

namespace IxCC.Src

/-! ## Operation inventories -/

/-- DR3 `Array` primitives pinned by the unfolding table. -/
inductive ArrayOp where
  | emptyWithCapacity
  | size
  | getInternal
  | set
  | setIfInBounds
  | push
  | pop
  | extract
  | copySlice
  | swap
  deriving DecidableEq, Repr, Inhabited, Hashable

namespace ArrayOp

def all : List ArrayOp :=
  [.emptyWithCapacity, .size, .getInternal, .set, .setIfInBounds,
   .push, .pop, .extract, .copySlice, .swap]

/-- Number of runtime-relevant value arguments (excluding erased type/proof args). -/
def runtimeArity : ArrayOp → Nat
  | .emptyWithCapacity => 1
  | .size => 1
  | .getInternal => 2
  | .set => 3
  | .setIfInBounds => 3
  | .push => 2
  | .pop => 1
  | .extract => 3
  | .copySlice => 5
  | .swap => 3

def leanName : ArrayOp → String
  | .emptyWithCapacity => "Array.emptyWithCapacity"
  | .size => "Array.size"
  | .getInternal => "Array.getInternal"
  | .set => "Array.set"
  | .setIfInBounds => "Array.setIfInBounds"
  | .push => "Array.push"
  | .pop => "Array.pop"
  | .extract => "Array.extract"
  | .copySlice => "Array.copySlice"
  | .swap => "Array.swap"

end ArrayOp

/-- DR3 `ByteArray` primitives pinned by the unfolding table. -/
inductive ByteArrayOp where
  | emptyWithCapacity
  | size
  | get
  | set
  | push
  | extract
  | copySlice
  deriving DecidableEq, Repr, Inhabited, Hashable

namespace ByteArrayOp

def all : List ByteArrayOp :=
  [.emptyWithCapacity, .size, .get, .set, .push, .extract, .copySlice]

def runtimeArity : ByteArrayOp → Nat
  | .emptyWithCapacity => 1
  | .size => 1
  | .get => 2
  | .set => 3
  | .push => 2
  | .extract => 3
  | .copySlice => 5

def leanName : ByteArrayOp → String
  | .emptyWithCapacity => "ByteArray.emptyWithCapacity"
  | .size => "ByteArray.size"
  | .get => "ByteArray.get"
  | .set => "ByteArray.set"
  | .push => "ByteArray.push"
  | .extract => "ByteArray.extract"
  | .copySlice => "ByteArray.copySlice"

end ByteArrayOp

/-- DR4 `String` representation bridges over UTF-8 `ByteArray`. -/
inductive StringOp where
  | ofByteArray
  | toByteArray
  | utf8ByteSize
  | getUTF8Byte
  | push
  | append
  deriving DecidableEq, Repr, Inhabited, Hashable

namespace StringOp

def all : List StringOp :=
  [.ofByteArray, .toByteArray, .utf8ByteSize, .getUTF8Byte, .push, .append]

def leanName : StringOp → String
  | .ofByteArray => "String.ofByteArray"
  | .toByteArray => "String.toByteArray"
  | .utf8ByteSize => "String.utf8ByteSize"
  | .getUTF8Byte => "String.getUTF8Byte"
  | .push => "String.push"
  | .append => "String.append"

end StringOp

/-! ## Pure list-level specifications -/

namespace ArraySpec

/-- Pure list-level `extract`: elements in `[start, min stop xs.length)`. -/
def extractList {α : Type u} (xs : List α) (start stop : Nat) : List α :=
  (xs.drop start).take (min stop xs.length - start)

/-- Pure list-level `copySlice`: overwrites/extends `dest` starting at `destOff`
with `min len (src.length - srcOff)` elements taken from `src` at `srcOff`. -/
def copySliceList {α : Type u} (src : List α) (srcOff : Nat) (dest : List α)
    (destOff len : Nat) : List α :=
  extractList dest 0 destOff ++
    extractList src srcOff (srcOff + len) ++
    extractList dest (destOff + min len (src.length - srcOff)) dest.length

/-- Pure list-level `swap` on in-bounds indices. -/
def swapList {α : Type u} (xs : List α) (i j : Nat) (hi : i < xs.length) (hj : j < xs.length) : List α :=
  let vi := xs[i]'hi
  let vj := xs[j]'hj
  (xs.set i vj).set j vi

/-! ### Conservativity theorems against Lean 4.34.1 `Array` reference bodies -/

theorem emptyWithCapacity_eq {α : Type u} (c : Nat) :
    (Array.emptyWithCapacity (α := α) c).toList = [] := rfl

theorem mkEmpty_eq {α : Type u} (c : Nat) :
    (Array.mkEmpty (α := α) c).toList = [] := rfl

theorem size_eq {α : Type u} (a : Array α) :
    a.size = a.toList.length := rfl

theorem getInternal_eq {α : Type u} (a : Array α) (i : Nat) (h : i < a.size) :
    a.getInternal i h = a.toList[i]'h := by
  rfl

theorem set_eq {α : Type u} (a : Array α) (i : Nat) (v : α) (h : i < a.size) :
    (a.set i v h).toList = a.toList.set i v := by
  simp [Array.toList_set]

theorem setIfInBounds_eq {α : Type u} (a : Array α) (i : Nat) (v : α) :
    (a.setIfInBounds i v).toList = a.toList.set i v := by
  simp [Array.toList_setIfInBounds]

theorem push_eq {α : Type u} (a : Array α) (v : α) :
    (a.push v).toList = a.toList ++ [v] := by
  simp [Array.toList_push]

theorem pop_eq {α : Type u} (a : Array α) :
    a.pop.toList = a.toList.dropLast := by
  rfl

theorem extract_eq {α : Type u} (a : Array α) (start stop : Nat) :
    (a.extract start stop).toList = extractList a.toList start stop := by
  unfold extractList
  rw [Array.toList_extract, List.extract_eq_take_drop]
  by_cases h : stop ≤ a.size
  · have hm : min stop a.toList.length = stop := by rw [← size_eq]; exact Nat.min_eq_left h
    rw [hm]
  · have hm : min stop a.toList.length = a.toList.length := by
      rw [← size_eq]; exact Nat.min_eq_right (Nat.le_of_not_le h)
    rw [hm]
    have hge1 : (a.toList.drop start).length ≤ stop - start := by
      simp only [List.length_drop]; rw [← size_eq]; omega
    have hge2 : (a.toList.drop start).length ≤ a.toList.length - start := by
      simp only [List.length_drop]; exact Nat.le_refl _
    rw [List.take_of_length_le hge1, List.take_of_length_le hge2]

theorem copySlice_model_eq {α : Type u} (src : Array α) (srcOff : Nat)
    (dest : Array α) (destOff len : Nat) :
    (dest.extract 0 destOff ++ src.extract srcOff (srcOff + len) ++
      dest.extract (destOff + min len (src.size - srcOff)) dest.size).toList =
      copySliceList src.toList srcOff dest.toList destOff len := by
  simp only [Array.toList_append, extract_eq, copySliceList, size_eq]

theorem swap_eq {α : Type u} (a : Array α) (i j : Nat) (hi : i < a.size) (hj : j < a.size) :
    (a.swap i j hi hj).toList = swapList a.toList i j hi hj := by
  simp only [Array.swap, swapList, Array.toList_set]
  rfl

/-! ### Structural & indexing laws (consumed by runtime refinement proofs) -/

theorem extractList_length {α : Type u} (xs : List α) (start stop : Nat) :
    (extractList xs start stop).length = min stop xs.length - start := by
  unfold extractList
  simp only [List.length_take, List.length_drop]
  omega

theorem extractList_getElem {α : Type u} (xs : List α) (start stop k : Nat)
    (hk : k < (extractList xs start stop).length) :
    (extractList xs start stop)[k]'hk = xs[start + k]'(by
      rw [extractList_length] at hk; omega) := by
  simp only [extractList, List.getElem_take, List.getElem_drop]

theorem copySliceList_length {α : Type u} (src : List α) (srcOff : Nat)
    (dest : List α) (destOff len : Nat) :
    (copySliceList src srcOff dest destOff len).length =
      max dest.length (min destOff dest.length + min len (src.length - srcOff)) := by
  unfold copySliceList
  simp only [List.length_append, extractList_length]
  omega

theorem copySliceList_getElem {α : Type u} (src : List α) (srcOff : Nat)
    (dest : List α) (destOff len k : Nat)
    (hk : k < (copySliceList src srcOff dest destOff len).length) :
    let d0 := min destOff dest.length
    let n := min len (src.length - srcOff)
    (copySliceList src srcOff dest destOff len)[k]'hk =
      if h1 : k < d0 then dest[k]'(by omega)
      else if h2 : k < d0 + n then src[srcOff + (k - d0)]'(by omega)
      else dest[k]'(by
        rw [copySliceList_length] at hk
        omega) := by
  dsimp only
  have hl1 : (extractList dest 0 destOff).length = min destOff dest.length := by
    rw [extractList_length]; omega
  have hl2 : (extractList src srcOff (srcOff + len)).length = min len (src.length - srcOff) := by
    rw [extractList_length]; omega
  simp only [copySliceList]
  split
  · next h1 =>
      rw [List.getElem_append_left (by simp only [List.length_append, hl1, hl2]; omega)]
      rw [List.getElem_append_left (by omega)]
      rw [extractList_getElem]
      simp
  · next h1 =>
      split
      · next h2 =>
          rw [List.getElem_append_left (by simp only [List.length_append, hl1, hl2]; omega)]
          rw [List.getElem_append_right (by omega)]
          rw [extractList_getElem]
          simp [hl1]
      · next h2 =>
          rw [List.getElem_append_right (by simp only [List.length_append, hl1, hl2]; omega)]
          rw [extractList_getElem]
          congr 1
          simp only [List.length_append, hl1, hl2]
          by_cases hd : destOff ≤ dest.length
          · have : min destOff dest.length = destOff := Nat.min_eq_left hd
            omega
          · have hlen := copySliceList_length src srcOff dest destOff len
            rw [hlen] at hk
            have : min destOff dest.length = dest.length := Nat.min_eq_right (Nat.le_of_not_le hd)
            omega

theorem copySliceList_zero_len {α : Type u} (src : List α) (srcOff : Nat)
    (dest : List α) (destOff : Nat) :
    copySliceList src srcOff dest destOff 0 = dest := by
  apply List.ext_getElem
  · rw [copySliceList_length]; simp; omega
  · intro k hk1 hk2
    have h := copySliceList_getElem src srcOff dest destOff 0 k hk1
    simp only [Nat.zero_min, Nat.add_zero] at h
    rw [h]
    by_cases hlt : k < min destOff dest.length
    · rw [dite_eq_left hlt]
    · rw [dite_eq_right hlt, dite_eq_right hlt]

theorem setList_oob {α : Type u} (xs : List α) (i : Nat) (v : α) (h : xs.length ≤ i) :
    xs.set i v = xs := by
  apply List.ext_getElem
  · simp
  · intro k hk1 hk2
    rw [List.getElem_set_ne (by omega)]

end ArraySpec

/-! ## Pure-Lean `ByteArray` specifications & conservativity -/

namespace ByteArraySpec

/-- Underlying byte list of a `ByteArray`. -/
def toBytes (b : ByteArray) : List UInt8 := b.data.toList

theorem emptyWithCapacity_eq (c : Nat) :
    toBytes (ByteArray.emptyWithCapacity c) = [] := rfl

theorem empty_eq : toBytes ByteArray.empty = [] := rfl

theorem size_eq (b : ByteArray) :
    b.size = (toBytes b).length := rfl

theorem get_eq (b : ByteArray) (i : Nat) (h : i < b.size) :
    b.get i h = (toBytes b)[i]'h := by
  rfl

theorem set_eq (b : ByteArray) (i : Nat) (v : UInt8) (h : i < b.size) :
    toBytes (b.set i v h) = (toBytes b).set i v := by
  simp [toBytes, ByteArray.set]

theorem push_eq (b : ByteArray) (v : UInt8) :
    toBytes (b.push v) = toBytes b ++ [v] := by
  simp [toBytes, ByteArray.push]

theorem copySlice_eq (src : ByteArray) (srcOff : Nat) (dest : ByteArray)
    (destOff len : Nat) (exact : Bool) :
    toBytes (src.copySlice srcOff dest destOff len exact) =
      ArraySpec.copySliceList (toBytes src) srcOff (toBytes dest) destOff len := by
  unfold toBytes ByteArray.copySlice
  exact ArraySpec.copySlice_model_eq src.data srcOff dest.data destOff len

theorem extract_eq (b : ByteArray) (start stop : Nat) :
    toBytes (b.extract start stop) = ArraySpec.extractList (toBytes b) start stop := by
  unfold ByteArray.extract
  rw [copySlice_eq, empty_eq]
  apply List.ext_getElem
  · rw [ArraySpec.copySliceList_length, ArraySpec.extractList_length]
    simp only [List.length_nil, Nat.min_zero, Nat.zero_add, Nat.zero_max]
    omega
  · intro k hk1 hk2
    have h := ArraySpec.copySliceList_getElem (toBytes b) start [] 0 (stop - start) k hk1
    simp only [List.length_nil, Nat.min_zero, Nat.not_lt_zero, dite_false, Nat.zero_add,
      Nat.sub_zero] at h
    have hlt : k < min (stop - start) ((toBytes b).length - start) := by
      rw [ArraySpec.extractList_length] at hk2; omega
    rw [h, dite_eq_left hlt, ArraySpec.extractList_getElem]

theorem append_eq (a b : ByteArray) :
    toBytes (a ++ b) = toBytes a ++ toBytes b := by
  change toBytes (ByteArray.append a b) = toBytes a ++ toBytes b
  rw [ByteArray.append_eq_fastAppend]
  unfold ByteArray.fastAppend
  rw [copySlice_eq]
  apply List.ext_getElem
  · rw [ArraySpec.copySliceList_length, List.length_append, size_eq, size_eq]
    simp only [Nat.min_self, Nat.sub_zero]
    omega
  · intro k hk1 hk2
    have h := ArraySpec.copySliceList_getElem (toBytes b) 0 (toBytes a) a.size b.size k hk1
    simp only [size_eq, Nat.min_self, Nat.sub_zero, Nat.zero_add] at h ⊢
    rw [h]
    by_cases hka : k < (toBytes a).length
    · rw [dite_eq_left hka, List.getElem_append_left hka]
    · rw [dite_eq_right hka]
      have hkb : k < (toBytes a).length + (toBytes b).length := by
        simpa [List.length_append] using hk2
      rw [dite_eq_left hkb, List.getElem_append_right (Nat.le_of_not_lt hka)]

end ByteArraySpec

/-! ## DR4 `String` over UTF-8 `ByteArray` specifications & conservativity -/

namespace StringSpec

/-- Underlying UTF-8 byte sequence of a `String`. -/
def toBytes (s : String) : List UInt8 := ByteArraySpec.toBytes s.toByteArray

theorem toByteArray_ofByteArray (b : ByteArray) (h : ByteArray.IsValidUTF8 b) :
    (String.ofByteArray b h).toByteArray = b := rfl

theorem utf8ByteSize_eq (s : String) :
    s.utf8ByteSize = s.toByteArray.size := rfl

theorem toUTF8_eq (s : String) :
    s.toUTF8 = s.toByteArray := rfl

theorem toBytes_eq_toUTF8 (s : String) :
    toBytes s = ByteArraySpec.toBytes s.toUTF8 := rfl

theorem ofByteArray_toByteArray (s : String) :
    String.ofByteArray s.toByteArray s.isValidUTF8 = s := by
  cases s; rfl

theorem fromUTF8_toByteArray (s : String) :
    String.fromUTF8 s.toByteArray s.isValidUTF8 = s := by
  cases s; rfl

theorem fromUTF8?_toByteArray (s : String) :
    String.fromUTF8? s.toByteArray = some s := by
  simp [String.fromUTF8?, s.isValidUTF8, fromUTF8_toByteArray]

theorem append_toBytes (a b : String) :
    toBytes (a ++ b) = toBytes a ++ toBytes b := by
  unfold toBytes
  have h : (a ++ b).toByteArray = a.toByteArray ++ b.toByteArray := String.toByteArray_append
  rw [h, ByteArraySpec.append_eq]

/-- UTF-8 byte equality characterizes `String` equality: two strings have the
same runtime `ByteArray` representation iff they are equal. -/
theorem eq_iff_toBytes_eq (a b : String) :
    a = b ↔ toBytes a = toBytes b := by
  constructor
  · intro h; subst h; rfl
  · intro h
    have hba : a.toByteArray = b.toByteArray := by
      apply ByteArray.ext
      exact Array.toList_inj.mp h
    cases a; cases b
    simp only [String.ofByteArray.injEq] at hba ⊢
    exact hba

end StringSpec

end IxCC.Src
