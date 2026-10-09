import Compilatrix.Own.Heap
import Compilatrix.Rt.Rc.Layout
import Compilatrix.Rt.Proof.Mem

/-! First fully-scanned heap/memory interface. Its facts describe actual bytes,
permissions, constructor fields and abstract locations. Operation branch/load
premises are consequences, not fields named after a successful simulation.
This interface does not yet prove allocator or unique-release preservation. -/
namespace Compilatrix.Rt.Rc.Procs
open Lir
open Compilatrix.Rt.Proof

abbrev AddressMap := Nat → Option Word

def valueWord (addresses : AddressMap) : Own.RVal → Option Word
  | .loc location => addresses location
  | .lit (.nat n) => natWord n
  | .lit (.str _) => none
  | .ctor0 ctor => if ctor.arity == 0 && ctor.tag ≤ maxTag then some (ctor0Word ctor.tag) else none
  | .erased => some 1

/-- Counts and lower header are represented by their actual little-endian
32-bit memory reads. Read permissions are required separately for every byte.
This avoids assuming the result of the permission-checking Lir load. -/
structure LiveCell (addresses : AddressMap) (mem : X86.Memory)
    (address : Word) (refs : Nat) (body : Own.Body) : Prop where
  positive : 0 < refs
  bounded : refs ≤ maxCount
  fields_positive : 0 < body.fields.length
  fields_small : body.fields.length < 32
  tag : body.ctor.tag ≤ maxTag
  nobj : body.ctor.nobj = body.fields.length
  nscalar : body.ctor.nscalar = 0
  shared : body.ctor.fieldKinds = List.replicate body.fields.length .shared
  nonzero : address ≠ 0
  aligned : address.toNat % 8 = 0
  fit : address.toNat + cellBytes body.fields.length < 2^63
  readable : ∀ j < cellBytes body.fields.length,
    mem.readable (address + UInt64.ofNat j) = true
  writable : ∀ j < cellBytes body.fields.length,
    mem.writable (address + UInt64.ofNat j) = true
  header : mem.read .w32 address = UInt64.ofNat
    (headerLow body.fields.length (smallClass body.fields.length) body.ctor.tag)
  count : mem.read .w32 (address + 4) = UInt64.ofNat (refs-1)
  fields : ∀ j value, body.fields[j]? = some value →
    ∃ word, valueWord addresses value = some word ∧
      WordAt mem (address + UInt64.ofNat (8+8*j)) word

/-- The mapping is required on live abstract cells only. A dead location has
no retained placement obligation: its physical cell can represent a later
fresh abstract location after recycle. Static cells are outside this initial
source fragment; the separate inc-static theorem remains preserved. -/
structure HeapLive (heap : Own.Heap) (addresses : AddressMap) (mem : X86.Memory) : Prop where
  cell : ∀ location refs mode body, heap.cell? location = some (.live refs mode body) →
    mode = .dyn ∧ ∃ address, addresses location = some address ∧ LiveCell addresses mem address refs body
  fields_live : ∀ location refs body child,
    heap.cell? location = some (.live refs .dyn body) → .loc child ∈ body.fields →
    ∃ childRefs childBody, heap.cell? child = some (.live childRefs .dyn childBody)
  disjoint : ∀ l₁ l₂ r₁ r₂ b₁ b₂ a₁ a₂,
    heap.cell? l₁ = some (.live r₁ .dyn b₁) → heap.cell? l₂ = some (.live r₂ .dyn b₂) →
    addresses l₁ = some a₁ → addresses l₂ = some a₂ → l₁ ≠ l₂ →
    a₁.toNat + cellBytes b₁.fields.length ≤ a₂.toNat ∨
      a₂.toNat + cellBytes b₂.fields.length ≤ a₁.toNat

/-- Explicit physical partition, used by the forthcoming release/allocator
invariant. Pending and reserved storage is never treated as a live source
value. Free-list links overwrite the header only after pending scan finishes. -/
inductive SlotKind where
  | live (location : Nat)
  | pending (deadLocation : Nat) (unvisited : List Own.RVal) (predecessor : Word)
  | free
  | reserved
  deriving Repr
structure Slot where
  address : Word
  cls : Nat
  kind : SlotKind
  deriving Repr
structure ArenaPartition (heap : Own.Heap) (addresses : AddressMap)
    (objectBase bump limit : Word) (slots : List Slot) : Prop where
  bounds : objectBase.toNat ≤ bump.toNat ∧ bump.toNat ≤ limit.toNat ∧ limit.toNat < 2^63
  valid : ∀ slot ∈ slots, 1 ≤ slot.cls ∧ slot.cls ≤ 32 ∧
    slot.address.toNat % 8 = 0 ∧ objectBase.toNat ≤ slot.address.toNat ∧
    slot.address.toNat + 8*slot.cls ≤ bump.toNat
  disjoint : ∀ (i j : Nat) (si sj : Slot), slots[i]? = some si → slots[j]? = some sj → i ≠ j →
    si.address.toNat + 8*si.cls ≤ sj.address.toNat ∨
      sj.address.toNat + 8*sj.cls ≤ si.address.toNat
  accounted : ∀ n, objectBase.toNat ≤ n → n < bump.toNat →
    ∃ slot ∈ slots, slot.address.toNat ≤ n ∧ n < slot.address.toNat + 8*slot.cls
  live : ∀ slot ∈ slots, ∀ location, slot.kind = .live location →
    ∃ refs body, heap.cell? location = some (.live refs .dyn body) ∧
      addresses location = some slot.address ∧ slot.cls = smallClass body.fields.length
  placed : ∀ location refs body, heap.cell? location = some (.live refs .dyn body) →
    ∃ slot ∈ slots, slot.kind = .live location
  pending : ∀ slot ∈ slots, ∀ location suffix predecessor,
    slot.kind = .pending location suffix predecessor → heap.cell? location = some .dead

theorem cell_offset4 (address : Word) (j : Nat) :
    (address+4) + UInt64.ofNat j = address + UInt64.ofNat (4+j) := by
  rw [UInt64.ofNat_add]
  simp [UInt64.add_assoc]

theorem LiveCell.count_readable {addresses : AddressMap} {mem : X86.Memory}
    {address : Word} {refs : Nat} {body : Own.Body}
    (h : LiveCell addresses mem address refs body) :
    ∀ j < 4, mem.readable ((address+4)+UInt64.ofNat j) = true := by
  intro j hj
  rw [cell_offset4]
  apply h.readable
  simp [cellBytes]
  omega

theorem LiveCell.count_writable {addresses : AddressMap} {mem : X86.Memory}
    {address : Word} {refs : Nat} {body : Own.Body}
    (h : LiveCell addresses mem address refs body) :
    ∀ j < 4, mem.writable ((address+4)+UInt64.ofNat j) = true := by
  intro j hj
  rw [cell_offset4]
  apply h.writable
  simp [cellBytes]
  omega

theorem LiveCell.count_load {addresses : AddressMap} {mem : X86.Memory}
    {address : Word} {refs : Nat} {body : Own.Body}
    (h : LiveCell addresses mem address refs body) :
    loadWord mem .w32 .zero (address+4) = some (UInt64.ofNat (refs-1)) := by
  unfold loadWord
  rw [read?_ok (w := .w32) h.count_readable, h.count]

theorem LiveCell.count_encoding {addresses : AddressMap} {mem : X86.Memory}
    {address : Word} {refs : Nat} {body : Own.Body}
    (h : LiveCell addresses mem address refs body) :
    (UInt64.ofNat (refs-1)).toNat = refs-1 := by
  rw [UInt64.toNat_ofNat']
  apply Nat.mod_eq_of_lt
  have hb := h.bounded
  unfold maxCount at hb
  omega




end Compilatrix.Rt.Rc.Procs
