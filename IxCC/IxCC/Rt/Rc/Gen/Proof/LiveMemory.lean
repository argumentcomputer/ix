import IxCC.Rt.Rc.Proof.LiveMemory
import IxCC.Rt.Rc.Gen.Procs

/-! The heap/memory interface for cells of any layout: today's `Procs.LiveCell`, `HeapLive` and
`ArenaPartition` with the class of a cell from its layout (`classOf`), its storage `8·classWords`
of its class, the scanned fields encoded as values and the scalar positions as raw words, and the
classes of the partition bounded by a parameter `cmax` (at most 71). Every cell and partition of
today's invariant is one of these (`Procs.LiveCell.toGen`, `Procs.ArenaPartition.toGen`). -/
namespace IxCC.Rt.Rc.Gen
open Lir
open IxCC.Rt.Proof
open IxCC.Rt.Rc.Procs (AddressMap valueWord SlotKind Slot cell_offset4)

/-- The layout of a constructor's cells. -/
def layoutOf (c : Fir.CtorInfo) : CellLayout := ⟨c.nobj, c.nscalar, c.tag⟩

/-- The class of a constructor's cells (`0` if its layout has none). -/
def classOf (c : Fir.CtorInfo) : Nat := ((layoutOf c).cls?).getD 0

/-- The bytes of a constructor's cells: its class's words. -/
def cellBytesOf (c : Fir.CtorInfo) : Nat := 8 * classWords (classOf c)

/-- The physical word of a scalar position: the raw word of a literal below 2⁶⁴. -/
def scalarWord : Own.RVal → Option Word
  | .lit (.nat n) => if n < 2 ^ 64 then some (UInt64.ofNat n) else none
  | _ => none

/-- The word of field `j` of a cell of constructor `c`: a value word for a scanned field, a raw
word for a scalar position. -/
def fieldWord (addresses : AddressMap) (c : Fir.CtorInfo) (j : Nat) (value : Own.RVal) :
    Option Word :=
  if j < c.nobj then valueWord addresses value else scalarWord value

/-- A live dynamic cell of any layout. -/
structure LiveCell (addresses : AddressMap) (mem : X86.Memory)
    (address : Word) (refs : Nat) (body : Own.Body) : Prop where
  positive : 0 < refs
  bounded : refs ≤ maxCount
  layout : (layoutOf body.ctor).ok = true
  arity : body.fields.length = body.ctor.nobj + body.ctor.nscalar
  shared : body.ctor.fieldKinds = List.replicate body.ctor.nobj .shared
  nonzero : address ≠ 0
  aligned : address.toNat % 8 = 0
  fit : address.toNat + cellBytesOf body.ctor < 2^63
  readable : ∀ j < cellBytesOf body.ctor, mem.readable (address + UInt64.ofNat j) = true
  writable : ∀ j < cellBytesOf body.ctor, mem.writable (address + UInt64.ofNat j) = true
  header : mem.read .w32 address =
    UInt64.ofNat (headerLow body.ctor.nobj (classOf body.ctor) body.ctor.tag)
  count : mem.read .w32 (address + 4) = UInt64.ofNat (refs-1)
  fields : ∀ j value, body.fields[j]? = some value →
    ∃ word, fieldWord addresses body.ctor j value = some word ∧
      WordAt mem (address + UInt64.ofNat (8+8*j)) word

structure HeapLive (heap : Own.Heap) (addresses : AddressMap) (mem : X86.Memory) : Prop where
  cell : ∀ location refs mode body, heap.cell? location = some (.live refs mode body) →
    mode = .dyn ∧ ∃ address, addresses location = some address ∧ LiveCell addresses mem address refs body
  fields_live : ∀ location refs body child,
    heap.cell? location = some (.live refs .dyn body) → .loc child ∈ body.fields →
    ∃ childRefs childBody, heap.cell? child = some (.live childRefs .dyn childBody)
  disjoint : ∀ l₁ l₂ r₁ r₂ b₁ b₂ a₁ a₂,
    heap.cell? l₁ = some (.live r₁ .dyn b₁) → heap.cell? l₂ = some (.live r₂ .dyn b₂) →
    addresses l₁ = some a₁ → addresses l₂ = some a₂ → l₁ ≠ l₂ →
    a₁.toNat + cellBytesOf b₁.ctor ≤ a₂.toNat ∨
      a₂.toNat + cellBytesOf b₂.ctor ≤ a₁.toNat

/-- The physical partition: slots of classes `1 … 71`, each of `8·classWords` bytes, every
slot's class at most `cmax`. -/
structure ArenaPartition (cmax : Nat) (heap : Own.Heap) (addresses : AddressMap)
    (objectBase bump limit : Word) (slots : List Slot) : Prop where
  bounds : objectBase.toNat ≤ bump.toNat ∧ bump.toNat ≤ limit.toNat ∧ limit.toNat < 2^63
  valid : ∀ slot ∈ slots, 1 ≤ slot.cls ∧ slot.cls ≤ maxClass ∧
    slot.address.toNat % 8 = 0 ∧ objectBase.toNat ≤ slot.address.toNat ∧
    slot.address.toNat + 8*classWords slot.cls ≤ bump.toNat ∧
    1 ≤ classWords slot.cls ∧ classWords slot.cls ≤ 67108864
  bounded : ∀ slot ∈ slots, slot.cls ≤ cmax
  disjoint : ∀ (i j : Nat) (si sj : Slot), slots[i]? = some si → slots[j]? = some sj → i ≠ j →
    si.address.toNat + 8*classWords si.cls ≤ sj.address.toNat ∨
      sj.address.toNat + 8*classWords sj.cls ≤ si.address.toNat
  accounted : ∀ n, objectBase.toNat ≤ n → n < bump.toNat →
    ∃ slot ∈ slots, slot.address.toNat ≤ n ∧ n < slot.address.toNat + 8*classWords slot.cls
  live : ∀ slot ∈ slots, ∀ location, slot.kind = .live location →
    ∃ refs body, heap.cell? location = some (.live refs .dyn body) ∧
      addresses location = some slot.address ∧ slot.cls = classOf body.ctor
  placed : ∀ location refs body, heap.cell? location = some (.live refs .dyn body) →
    ∃ slot ∈ slots, slot.kind = .live location
  pending : ∀ slot ∈ slots, ∀ location suffix predecessor,
    slot.kind = .pending location suffix predecessor → heap.cell? location = some .dead

theorem le_classWords {c : Nat} (h : c ≤ maxClass) : c ≤ classWords c := by
  have all : ∀ c < maxClass + 1, c ≤ classWords c := by decide
  exact all c (by unfold maxClass at h ⊢; omega)

/-! ## Layout facts of a constructor with a valid layout -/

theorem layoutOf_cls {c : Fir.CtorInfo} (h : (layoutOf c).ok = true) :
    (layoutOf c).cls? = some (classOf c) := by
  obtain ⟨cls, hc⟩ := CellLayout.ok_cls h
  simp [classOf, hc]

/-- The class of a valid layout: at least 2, at most 71, and its words hold the cell. -/
theorem classOf_spec {c : Fir.CtorInfo} (h : (layoutOf c).ok = true) :
    2 ≤ classOf c ∧ classOf c ≤ maxClass ∧ 1 + c.nobj + c.nscalar ≤ classWords (classOf c) := by
  have := CellLayout.cls_spec h (layoutOf_cls h)
  simpa [CellLayout.words, layoutOf] using this

theorem layoutOf_bounds {c : Fir.CtorInfo} (h : (layoutOf c).ok = true) :
    0 < c.nobj + c.nscalar ∧ c.nobj ≤ maxFields ∧ c.tag ≤ maxTag := by
  simpa [layoutOf] using CellLayout.ok_bounds h

theorem cellBytesOf_le {c : Fir.CtorInfo} (h : (layoutOf c).ok = true) :
    16 ≤ cellBytesOf c ∧ 8 * (1 + c.nobj + c.nscalar) ≤ cellBytesOf c ∧
      cellBytesOf c ≤ 8 * maxCellWords := by
  obtain ⟨h2, hm, hw⟩ := classOf_spec h
  have hb := layoutOf_bounds h
  have := classWords_le_max hm
  unfold cellBytesOf
  omega

/-- The class byte and the scan byte of a valid layout fit in a byte. -/
theorem classOf_lt {c : Fir.CtorInfo} (h : (layoutOf c).ok = true) :
    classOf c < 256 ∧ c.nobj < 256 ∧ c.tag < 65536 := by
  obtain ⟨_, hm, _⟩ := classOf_spec h
  have hb := layoutOf_bounds h
  unfold maxClass at hm; unfold maxFields at hb; unfold maxTag at hb
  omega

/-! ## Facts of a live cell -/

namespace LiveCell
variable {addresses : AddressMap} {mem : X86.Memory} {address : Word} {refs : Nat} {body : Own.Body}

theorem bytes (h : LiveCell addresses mem address refs body) :
    16 ≤ cellBytesOf body.ctor ∧ 8 * (1 + body.fields.length) ≤ cellBytesOf body.ctor := by
  have := cellBytesOf_le h.layout
  have ha := h.arity
  omega

theorem tag_le (h : LiveCell addresses mem address refs body) : body.ctor.tag ≤ maxTag :=
  (layoutOf_bounds h.layout).2.2

theorem nobj_le (h : LiveCell addresses mem address refs body) : body.ctor.nobj ≤ maxFields :=
  (layoutOf_bounds h.layout).2.1

theorem count_readable (h : LiveCell addresses mem address refs body) :
    ∀ j < 4, mem.readable ((address+4)+UInt64.ofNat j) = true := by
  intro j hj
  rw [cell_offset4]
  apply h.readable
  have := h.bytes
  omega

theorem count_writable (h : LiveCell addresses mem address refs body) :
    ∀ j < 4, mem.writable ((address+4)+UInt64.ofNat j) = true := by
  intro j hj
  rw [cell_offset4]
  apply h.writable
  have := h.bytes
  omega

theorem count_load (h : LiveCell addresses mem address refs body) :
    loadWord mem .w32 .zero (address+4) = some (UInt64.ofNat (refs-1)) := by
  unfold loadWord
  rw [read?_ok (w := .w32) h.count_readable, h.count]

theorem count_encoding (h : LiveCell addresses mem address refs body) :
    (UInt64.ofNat (refs-1)).toNat = refs-1 := by
  rw [UInt64.toNat_ofNat']
  apply Nat.mod_eq_of_lt
  have hb := h.bounded
  unfold maxCount at hb
  omega

/-- A scanned field holds its value's word. -/
theorem scanned (h : LiveCell addresses mem address refs body) {j : Nat} {value : Own.RVal}
    (hj : body.fields[j]? = some value) (hs : j < body.ctor.nobj) :
    ∃ word, valueWord addresses value = some word ∧
      WordAt mem (address + UInt64.ofNat (8+8*j)) word := by
  obtain ⟨word, hw, hat⟩ := h.fields j value hj
  simp only [fieldWord, hs, ite_true] at hw
  exact ⟨word, hw, hat⟩

end LiveCell

theorem scalarWord_lit {value : Own.RVal} {word : Word} (h : scalarWord value = some word) :
    ∃ n, value = .lit (.nat n) := by
  cases value with
  | lit l => cases l with
    | nat n => exact ⟨n, rfl⟩
    | str _ => simp [scalarWord] at h
  | _ => simp [scalarWord] at h

/-- The scalar positions of a live cell hold `Nat` literals. -/
theorem LiveCell.scalar_values {addresses : AddressMap} {mem : X86.Memory} {address : Word}
    {refs : Nat} {body : Own.Body} (h : LiveCell addresses mem address refs body) :
    ∀ j value, body.fields[j]? = some value → body.ctor.nobj ≤ j → ∃ n, value = .lit (.nat n) := by
  intro j value hj hs
  obtain ⟨word, hw, _⟩ := h.fields j value hj
  simp only [fieldWord, show ¬ j < body.ctor.nobj by omega, if_false] at hw
  exact scalarWord_lit hw

/-! ## Today's cells and partitions are cells and partitions of any layout -/

/-- Every cell of today's invariant is a cell of the general one, in the same class. -/
theorem _root_.IxCC.Rt.Rc.Procs.LiveCell.toGen {addresses : AddressMap} {mem : X86.Memory}
    {address : Word} {refs : Nat} {body : Own.Body}
    (h : Procs.LiveCell addresses mem address refs body) :
    LiveCell addresses mem address refs body ∧ classOf body.ctor = smallClass body.fields.length ∧
      cellBytesOf body.ctor = cellBytes body.fields.length := by
  have hlay : layoutOf body.ctor = CellLayout.ofFields body.fields.length body.ctor.tag := by
    simp [layoutOf, CellLayout.ofFields, h.nobj, h.nscalar]
  have hok : (layoutOf body.ctor).ok = true := by
    rw [hlay]; exact CellLayout.ofFields_ok h.fields_positive h.fields_small h.tag
  have hcls : classOf body.ctor = smallClass body.fields.length := by
    simp [classOf, hlay, CellLayout.ofFields_cls h.fields_small]
  have hbytes : cellBytesOf body.ctor = cellBytes body.fields.length := by
    rw [cellBytesOf, hcls, classWords_small (by have := h.fields_small; unfold smallClass; omega)]
    simp [smallClass, cellBytes]; omega
  refine ⟨{
    positive := h.positive, bounded := h.bounded, layout := hok
    arity := by rw [h.nobj, h.nscalar]; rfl
    shared := by rw [h.shared, h.nobj]
    nonzero := h.nonzero, aligned := h.aligned
    fit := by rw [hbytes]; exact h.fit
    readable := by rw [hbytes]; exact h.readable
    writable := by rw [hbytes]; exact h.writable
    header := by rw [hcls, h.header, h.nobj]
    count := h.count
    fields := ?_ }, hcls, hbytes⟩
  intro j value hj
  have hlt := (List.getElem?_eq_some_iff.mp hj).1
  have hs : j < body.ctor.nobj := by rw [h.nobj]; exact hlt
  obtain ⟨word, hw, hat⟩ := h.fields j value hj
  exact ⟨word, by simp only [fieldWord, hs, ite_true]; exact hw, hat⟩

theorem _root_.IxCC.Rt.Rc.Procs.HeapLive.toGen {heap : Own.Heap} {addresses : AddressMap}
    {mem : X86.Memory} (h : Procs.HeapLive heap addresses mem) : HeapLive heap addresses mem where
  cell location refs mode body hc := by
    obtain ⟨hm, address, ha, hl⟩ := h.cell location refs mode body hc
    exact ⟨hm, address, ha, hl.toGen.1⟩
  fields_live := h.fields_live
  disjoint l₁ l₂ r₁ r₂ b₁ b₂ a₁ a₂ h₁ h₂ ha₁ ha₂ hne := by
    obtain ⟨_, _, _, hl₁⟩ := h.cell l₁ r₁ .dyn b₁ h₁
    obtain ⟨_, _, _, hl₂⟩ := h.cell l₂ r₂ .dyn b₂ h₂
    rw [hl₁.toGen.2.2, hl₂.toGen.2.2]
    exact h.disjoint l₁ l₂ r₁ r₂ b₁ b₂ a₁ a₂ h₁ h₂ ha₁ ha₂ hne

end IxCC.Rt.Rc.Gen
