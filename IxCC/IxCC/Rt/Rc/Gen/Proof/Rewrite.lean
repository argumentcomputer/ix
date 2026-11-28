import IxCC.Rt.Rc.Gen.Proof.WriteCell
import IxCC.Rt.Rc.Gen.Proof.ObjectFrame
import IxCC.Rt.Rc.Gen.Proof.ProtectedFrame
import IxCC.Rt.Rc.Proof.CountPreserve

/-! # Rewriting a cell in place

The memory facts of `writeCell` (`Gen.Proof.WriteCell`): permissions unchanged, every byte
outside `[a, a + 8·(1 + fields))` unchanged (`writeCell_bytes_out`, `writeCell_objectFrame`,
`writeCell_protected`), and the new cell is a `LiveCell` with one reference when every field has a
word and the class is the old one (`LiveCell.rewrite`). Nothing emits this rewrite yet; it is
what an in-place reuse stores. -/

set_option autoImplicit false
namespace IxCC.Rt.Rc.Gen
open Lir
open IxCC.Rt.Proof
open IxCC.Rt (headerLow maxTag maxFields)
open IxCC.Rt.Rc.Procs (AddressMap valueWord ObjectFrame cell_offset4 pack32 truncate32_small)

/-! ## Stores -/

theorem write_readable (mem : X86.Memory) (w : X86.Width) (a v : Word) :
    (mem.write w a v).readable = mem.readable := by
  simp [X86.Memory.write]

theorem write_writable (mem : X86.Memory) (w : X86.Width) (a v : Word) :
    (mem.write w a v).writable = mem.writable := by
  simp [X86.Memory.write]

theorem writeFields_cons (mem : X86.Memory) (addresses : AddressMap) (a : Word) (c : Fir.CtorInfo)
    (value : Own.RVal) (j : Nat) (entries : List (Own.RVal × Nat)) :
    writeFields mem addresses a c ((value, j) :: entries) =
      writeFields (mem.write .w64 (a + UInt64.ofNat (8 + 8 * j))
        ((fieldWord addresses c j value).getD 0)) addresses a c entries := rfl

theorem writeFields_perm (addresses : AddressMap) (a : Word) (c : Fir.CtorInfo) :
    ∀ (entries : List (Own.RVal × Nat)) (mem : X86.Memory),
      (writeFields mem addresses a c entries).readable = mem.readable ∧
        (writeFields mem addresses a c entries).writable = mem.writable
  | [], _ => ⟨rfl, rfl⟩
  | (value, j) :: entries, mem => by
    rw [writeFields_cons]
    have ih := writeFields_perm addresses a c entries
      (mem.write .w64 (a + UInt64.ofNat (8 + 8 * j)) ((fieldWord addresses c j value).getD 0))
    exact ⟨ih.1.trans (write_readable ..), ih.2.trans (write_writable ..)⟩

/-- The stores leave every byte outside their words. -/
theorem writeFields_bytes (addresses : AddressMap) (a : Word) (c : Fir.CtorInfo) (y : Word) :
    ∀ (entries : List (Own.RVal × Nat)) (mem : X86.Memory),
      (∀ e ∈ entries, a.toNat + 16 + 8 * e.2 ≤ 2^64 ∧
        (y.toNat < a.toNat + 8 + 8 * e.2 ∨ a.toNat + 16 + 8 * e.2 ≤ y.toNat)) →
      (writeFields mem addresses a c entries).bytes y = mem.bytes y
  | [], _, _ => rfl
  | (value, j) :: entries, mem, h => by
    have h0 := h (value, j) (by simp)
    simp only at h0
    rw [writeFields_cons, writeFields_bytes addresses a c y entries _ (fun e he => h e (by simp [he]))]
    have hat : (a + UInt64.ofNat (8 + 8 * j)).toNat = a.toNat + 8 + 8 * j := by
      rw [addr_toNat (by omega)]; omega
    simp only [X86.Memory.write, X86.Width.bytes]
    exact writeLittle_bytes_out (by omega) (by rw [hat]; omega)
      (by rw [hat]; omega)

/-- The stores keep a word outside their words. -/
theorem writeFields_wordAt (addresses : AddressMap) (a : Word) (c : Fir.CtorInfo) {t w : Word} :
    ∀ (entries : List (Own.RVal × Nat)) (mem : X86.Memory),
      (∀ e ∈ entries, a.toNat + 16 + 8 * e.2 ≤ 2^64 ∧
        (t.toNat + 8 ≤ a.toNat + 8 + 8 * e.2 ∨ a.toNat + 16 + 8 * e.2 ≤ t.toNat)) →
      t.toNat + 8 ≤ 2^64 → WordAt mem t w → WordAt (writeFields mem addresses a c entries) t w
  | [], _, _, _, hw => hw
  | (value, j) :: entries, mem, h, ht, hw => by
    have h0 := h (value, j) (by simp)
    simp only at h0
    have hat : (a + UInt64.ofNat (8 + 8 * j)).toNat = a.toNat + 8 + 8 * j := by
      rw [addr_toNat (by omega)]; omega
    rw [writeFields_cons]
    exact writeFields_wordAt addresses a c entries _ (fun e he => h e (by simp [he])) ht
      (hw.write_disjoint (by simp only [X86.Width.bytes]; rw [hat]; omega) ht
        (by simp only [X86.Width.bytes]; rw [hat]; omega))

theorem mem_zipIdx_bounds {α : Type} :
    ∀ (l : List α) (n : Nat) (e : α × Nat), e ∈ l.zipIdx n → n ≤ e.2 ∧ e.2 < n + l.length
  | [], _, _, h => by simp at h
  | x :: xs, n, e, h => by
    rw [List.zipIdx_cons, List.mem_cons] at h
    rcases h with rfl | h
    · simp
    · have := mem_zipIdx_bounds xs (n + 1) e h
      simp only [List.length_cons]
      omega

/-- Field `j` holds its word after the stores of a list's fields from index `n`. -/
theorem writeFields_field (addresses : AddressMap) (a : Word) (c : Fir.CtorInfo) :
    ∀ (l : List Own.RVal) (n : Nat) (mem : X86.Memory) (j : Nat) (value : Own.RVal),
      a.toNat + 8 * (n + l.length + 1) ≤ 2^64 → n ≤ j → l[j - n]? = some value →
      (∀ i < 8, mem.readable (a + UInt64.ofNat (8 + 8 * j) + UInt64.ofNat i) = true) →
      WordAt (writeFields mem addresses a c (l.zipIdx n)) (a + UInt64.ofNat (8 + 8 * j))
        ((fieldWord addresses c j value).getD 0)
  | [], _, _, _, _, _, _, hv, _ => by simp at hv
  | x :: xs, n, mem, j, value, hfit, hn, hv, hr => by
    rw [List.zipIdx_cons, writeFields_cons]
    simp only [List.length_cons] at hfit
    have hjl : j < n + xs.length + 1 := by
      rcases Nat.lt_or_ge (j - n) (xs.length + 1) with h | h
      · omega
      · have : (x :: xs)[j - n]? = none := List.getElem?_eq_none (by simp; omega)
        rw [this] at hv; cases hv
    have hat : (a + UInt64.ofNat (8 + 8 * j)).toNat = a.toNat + 8 + 8 * j := by
      rw [addr_toNat (by omega)]; omega
    by_cases hj : j = n
    · subst hj
      simp only [Nat.sub_self, List.getElem?_cons_zero, Option.some.injEq] at hv
      subst hv
      apply writeFields_wordAt addresses a c (xs.zipIdx (j + 1)) _ ?_ (by rw [hat]; omega)
        (wordAt_write64 hr)
      intro e he
      have hb := mem_zipIdx_bounds xs (j + 1) e he
      rw [hat]
      constructor <;> omega
    · have hv' : xs[j - (n + 1)]? = some value := by
        have he : j - n = (j - (n + 1)) + 1 := by omega
        rw [he, List.getElem?_cons_succ] at hv
        exact hv
      exact writeFields_field addresses a c xs (n + 1) _ j value (by omega) (by omega) hv'
        (fun i hi => by rw [write_readable]; exact hr i hi)

/-! ## The rewritten cell's memory -/

section Cell
variable {mem : X86.Memory} {addresses : AddressMap} {a : Word} {b : Own.Body} {cls : Nat}

theorem writeCell_readable : (writeCell mem addresses a b cls).readable = mem.readable :=
  (writeFields_perm addresses a b.ctor _ _).1.trans (write_readable ..)

theorem writeCell_writable : (writeCell mem addresses a b cls).writable = mem.writable :=
  (writeFields_perm addresses a b.ctor _ _).2.trans (write_writable ..)

/-- Every byte outside the rewritten words is unchanged. -/
theorem writeCell_bytes_out (hfit : a.toNat + 8 * (1 + b.fields.length) ≤ 2^64) {y : Word}
    (hy : y.toNat < a.toNat ∨ a.toNat + 8 * (1 + b.fields.length) ≤ y.toNat) :
    (writeCell mem addresses a b cls).bytes y = mem.bytes y := by
  unfold writeCell
  rw [writeFields_bytes addresses a b.ctor y _ _ (fun e he => by
    have := mem_zipIdx_bounds b.fields 0 e he
    constructor <;> omega)]
  simp only [X86.Memory.write, X86.Width.bytes]
  exact writeLittle_bytes_out (by omega) (by omega) (by omega)

theorem writeCell_objectFrame (hfit : a.toNat + 8 * (1 + b.fields.length) ≤ 2^64) {x : Word} {n : Nat}
    (hx : x.toNat + n ≤ 2^64) (hsep : x.toNat + n ≤ a.toNat ∨ a.toNat + 8 * (1 + b.fields.length) ≤ x.toNat) :
    ObjectFrame mem (writeCell mem addresses a b cls) x n where
  readable := writeCell_readable
  writable := writeCell_writable
  bytes_eq j hj := by
    apply writeCell_bytes_out hfit
    rw [addr_toNat (by omega)]
    omega

theorem writeCell_wordAt (hfit : a.toNat + 8 * (1 + b.fields.length) ≤ 2^64) {t w : Word}
    (ht : t.toNat + 8 ≤ 2^64) (hsep : t.toNat + 8 ≤ a.toNat ∨ a.toNat + 8 * (1 + b.fields.length) ≤ t.toNat)
    (hw : WordAt mem t w) : WordAt (writeCell mem addresses a b cls) t w := by
  have frame := writeCell_objectFrame (mem := mem) (addresses := addresses) (cls := cls) hfit ht hsep
  simpa using frame.word (offset := 0) (by omega) (by simpa using hw)

/-- The rewrite stays inside `[base, bump)`, so it is a protected store. -/
theorem writeCell_protected (hfit : a.toNat + 8 * (1 + b.fields.length) ≤ 2^64)
    {context base bump : Word} (hlo : base.toNat ≤ a.toNat)
    (hhi : a.toNat + 8 * (1 + b.fields.length) ≤ bump.toNat) :
    ProtectedFrame mem (writeCell mem addresses a b cls) context base bump where
  readable := writeCell_readable
  writable := writeCell_writable
  bytes_eq y hy _ := writeCell_bytes_out hfit (by omega)

theorem writeCell_header (hfit : a.toNat + 8 * (1 + b.fields.length) ≤ 2^64)
    (hr : ∀ i < 8, mem.readable (a + UInt64.ofNat i) = true) :
    WordAt (writeCell mem addresses a b cls) a (dynamicHeader b.ctor.nobj cls b.ctor.tag 1) := by
  unfold writeCell
  apply writeFields_wordAt addresses a b.ctor _ _ (fun e he => by
    have := mem_zipIdx_bounds b.fields 0 e he
    constructor <;> omega) (by omega) (wordAt_write64 hr)

theorem writeCell_field (hfit : a.toNat + 8 * (1 + b.fields.length) ≤ 2^64) {j : Nat} {value : Own.RVal}
    (hv : b.fields[j]? = some value)
    (hr : ∀ i < 8, mem.readable (a + UInt64.ofNat (8 + 8 * j) + UInt64.ofNat i) = true) :
    WordAt (writeCell mem addresses a b cls) (a + UInt64.ofNat (8 + 8 * j))
      ((fieldWord addresses b.ctor j value).getD 0) := by
  unfold writeCell
  exact writeFields_field addresses a b.ctor b.fields 0 _ j value (by omega) (Nat.zero_le _)
    (by simpa using hv) (fun i hi => by rw [write_readable]; exact hr i hi)

end Cell

/-! ## The header's two halves -/

theorem wordAt_read32_low {mem : X86.Memory} {address word : Word}
    (represented : WordAt mem address word) :
    mem.read .w32 address = X86.Width.w32.truncate word := by
  change mem.readLittle address 4 = _
  simp (discharger := omega) only [X86.Memory.readLittle, represented.bytes]
  simpa using pack32 word

theorem wordAt_read32_high_zero {mem : X86.Memory} {address word : Word}
    (represented : WordAt mem address word) (small : word.toNat < 2^32) :
    mem.read .w32 (address + 4) = 0 := by
  have bytes : ∀ j < 4, mem.bytes ((address+4)+UInt64.ofNat j) = 0 := by
    intro j hj
    rw [cell_offset4, represented.bytes (4+j) (by omega)]
    apply UInt8.toNat_inj.mp
    rw [byte_of_shift _ _ (by omega)]
    change word.toNat / 2^(8*(4+j)) % 256 = 0
    have options : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
    rcases options with rfl | rfl | rfl | rfl <;> omega
  simp only [X86.Memory.read, X86.Width.bytes, X86.Memory.readLittle]
  simp (discharger := omega) only [bytes]
  rfl

/-- A one-reference dynamic header reads back as its low half and a zero count word. -/
theorem dynamicHeader_reads {mem : X86.Memory} {address : Word} {scan cls tag : Nat}
    (hs : scan < 256) (hc : cls < 256) (ht : tag < 65536)
    (represented : WordAt mem address (dynamicHeader scan cls tag 1)) :
    mem.read .w32 address = UInt64.ofNat (headerLow scan cls tag) ∧
      mem.read .w32 (address + 4) = 0 := by
  have headerEq : dynamicHeader scan cls tag 1 = UInt64.ofNat (headerLow scan cls tag) := by
    simp [dynamicHeader, header]
  rw [headerEq] at represented
  have bound : headerLow scan cls tag < 2^32 := by
    simp only [headerLow]
    omega
  have wordBound : (UInt64.ofNat (headerLow scan cls tag)).toNat < 2^32 := by
    rw [UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]
    exact bound
  exact ⟨(wordAt_read32_low represented).trans (truncate32_small wordBound),
    wordAt_read32_high_zero represented wordBound⟩

/-! ## Cells under a changed address map -/

theorem valueWord_remap {addresses addresses' : AddressMap} {value : Own.RVal}
    (hmap : ∀ k, value = .loc k → addresses' k = addresses k) :
    valueWord addresses' value = valueWord addresses value := by
  cases value with
  | loc k => simp [valueWord, hmap k rfl]
  | lit l => cases l <;> rfl
  | ctor0 _ | erased => rfl

theorem fieldWord_remap {addresses addresses' : AddressMap} {c : Fir.CtorInfo} {j : Nat}
    {value : Own.RVal} (hmap : ∀ k, value = .loc k → addresses' k = addresses k) :
    fieldWord addresses' c j value = fieldWord addresses c j value := by
  simp only [fieldWord, valueWord_remap hmap]

/-- A live cell stays live under an address map that agrees on the locations its fields name. -/
theorem LiveCell.remap {addresses addresses' : AddressMap} {mem : X86.Memory} {address : Word}
    {refs : Nat} {body : Own.Body} (h : LiveCell addresses mem address refs body)
    (hmap : ∀ k, Own.RVal.loc k ∈ body.fields → addresses' k = addresses k) :
    LiveCell addresses' mem address refs body := by
  refine { h with fields := ?_ }
  intro j value hj
  obtain ⟨word, hv, hw⟩ := h.fields j value hj
  refine ⟨word, ?_, hw⟩
  rw [fieldWord_remap (fun k e => hmap k (by subst e; exact List.mem_of_getElem? hj))]
  exact hv

/-- The rewritten cell is a live cell with one reference: same storage (the old cell's class, so
the same bytes), a valid layout, and a word for every field (`hwords`; a scanned field without a
value word is stored as `0`, which the release would follow as a cell). -/
theorem LiveCell.rewrite {addresses addresses' : AddressMap} {mem : X86.Memory} {a : Word}
    {refs : Nat} {b b' : Own.Body} (old : LiveCell addresses mem a refs b)
    (hlayout : (layoutOf b'.ctor).ok = true)
    (harity : b'.fields.length = b'.ctor.nobj + b'.ctor.nscalar)
    (hshared : b'.ctor.fieldKinds = List.replicate b'.ctor.nobj .shared)
    (hclass : classOf b'.ctor = classOf b.ctor)
    (hwords : ∀ j value, b'.fields[j]? = some value → (fieldWord addresses b'.ctor j value).isSome)
    (hmap : ∀ k, Own.RVal.loc k ∈ b'.fields → addresses' k = addresses k) :
    LiveCell addresses' (writeCell mem addresses a b' (classOf b.ctor)) a 1 b' := by
  have hbytes : cellBytesOf b'.ctor = cellBytesOf b.ctor := by unfold cellBytesOf; rw [hclass]
  have hlen := (cellBytesOf_le hlayout).2.1
  have hfit := old.fit
  have hw : a.toNat + 8 * (1 + b'.fields.length) ≤ 2^64 := by omega
  have hlt := classOf_lt hlayout
  have hdr := writeCell_header (addresses := addresses) (cls := classOf b.ctor) hw
    (fun i hi => old.readable i (by have := old.bytes; omega))
  have reads := dynamicHeader_reads hlt.2.1 (by rw [← hclass]; exact hlt.1) hlt.2.2 hdr
  refine {
    positive := by decide
    bounded := by decide
    layout := hlayout
    arity := harity
    shared := hshared
    nonzero := old.nonzero
    aligned := old.aligned
    fit := by rw [hbytes]; exact hfit
    readable := fun j hj => by rw [writeCell_readable]; exact old.readable j (by omega)
    writable := fun j hj => by rw [writeCell_writable]; exact old.writable j (by omega)
    header := ?_
    count := reads.2
    fields := ?_ }
  · rw [hclass]; exact reads.1
  · intro j value hj
    have hjl := (List.getElem?_eq_some_iff.mp hj).1
    obtain ⟨word, hword⟩ := Option.isSome_iff_exists.mp (hwords j value hj)
    refine ⟨word, ?_, ?_⟩
    · rw [fieldWord_remap (fun k e => hmap k (by subst e; exact List.mem_of_getElem? hj))]
      exact hword
    · have := writeCell_field (addresses := addresses) (cls := classOf b.ctor) hw hj (fun i hi => by
        have he : a + UInt64.ofNat (8 + 8 * j) + UInt64.ofNat i = a + UInt64.ofNat (8 + 8 * j + i) := by
          rw [UInt64.ofNat_add (8 + 8 * j) i]; simp [UInt64.add_assoc]
        rw [he]
        exact old.readable _ (by omega))
      simpa [hword] using this

end IxCC.Rt.Rc.Gen
