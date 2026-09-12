import Compilatrix.X86.HeapObject
import Compilatrix.X86.PhysicalScalarValues
import Compilatrix.IxIR2.ReservationOwnership

namespace Compilatrix.X86.PhysicalHeap
open WordRegion HeapArena
open IxIR2.Eval (RVal Credit Store)

/-- The dead module-export closure has no native cell. All later physical
locations are represented by their offset from this fixed offset. -/
inductive ValueAt (layout : HeapArena.Layout) (offset used : Nat) : Kind → RVal → Word → Prop where
  | scalar (word : Word) : ValueAt layout offset used .scalar (.lit (.nat word.toNat)) word
  | node (location : Nat) (above : offset ≤ location) (below : location < offset + used) :
      ValueAt layout offset used .node (.loc location) (layout.pointer (location - offset))
  | erased : ValueAt layout offset used .erased .erased 0

theorem ValueAt.grow {layout offset smaller larger kind value word}
    (represented : ValueAt layout offset smaller kind value word) (bound : smaller ≤ larger) :
    ValueAt layout offset larger kind value word := by
  cases represented with
  | scalar => exact .scalar _
  | node location above below => exact .node location above (by omega)
  | erased => exact .erased

theorem ValueAt.scalar_value {layout offset used value word} (represented : ValueAt layout offset used .scalar value word) :
    value = PhysicalScalar.rval word := by cases represented; rfl

theorem ValueAt.node_value {layout offset used value word} (represented : ValueAt layout offset used .node value word) :
    ∃ location, value = .loc location ∧ offset ≤ location ∧ location < offset + used ∧ word = layout.pointer (location - offset) := by
  cases represented with
  | node location above below => exact ⟨location, rfl, above, below, rfl⟩

structure CreditData (layout : HeapArena.Layout) (offset used : Nat) (id : IxIR2.LayoutId) (credit : Credit) (word : Word) where
  location : Nat
  above : offset ≤ location
  below : location < offset + used
  layoutAt : credit.layout = id
  presence : credit.presence = .present (some location)
  pointer : word = layout.pointer (location - offset)

abbrev CreditAt (layout : HeapArena.Layout) (offset used : Nat) (id : IxIR2.LayoutId) (credit : Credit) (word : Word) :=
  Nonempty (CreditData layout offset used id credit word)

theorem CreditAt.grow {layout offset smaller larger id credit word}
    (represented : CreditAt layout offset smaller id credit word) (bound : smaller ≤ larger) :
    CreditAt layout offset larger id credit word := by
  rcases represented with ⟨represented⟩
  exact ⟨{ represented with below := by have := represented.below; omega }⟩

def reservations (credits : Array (Option Credit)) : List Nat :=
  (credits.toList.filterMap id).filterMap IxIR2.Eval.Credit.reservation?

def suspendedReservations (stack : List IxIR2.Eval.Continuation) : List Nat :=
  stack.flatMap IxIR2.Eval.Continuation.reservations

def counters (store : Store) (field : Nat) : Nat :=
  match field with
  | 2 => store.heap.allocs
  | 3 => store.heap.frees
  | 4 => store.heap.reuses
  | 5 => store.heap.rcops
  | 6 => store.resetAttempts
  | 7 => store.hotResets
  | 8 => store.reusedPayloadUnits
  | _ => 0

structure NodeData (schemas : Schemas) (constructors : Array IxIR2.CtorId) (words : Words) (index : Nat) (box : IxIR1.NodeBox) where
  constructorIndex : Nat
  cid : IxIR2.CtorId
  fields : Array Word
  schema : IxIR2.CtorSchema
  schemaAt : schemas box.world cid = some schema
  arity : fields.size = schema.fields.size
  registered : constructors[constructorIndex]? = some cid
  constructorBound : constructorIndex < maxConstructors
  small : fields.size ≤ 2
  unique : box.rc = 1
  node : box.node = .ctorN cid (fields.map PhysicalScalar.rval)
  tag : words (cellSlot index 0) = UInt64.ofNat (constructorIndex + 2)
  first : words (cellSlot index 1) = fields[0]?.getD 0
  second : words (cellSlot index 2) = fields[1]?.getD 0
  padding : words (cellSlot index 3) = 0

abbrev NodeAt (schemas : Schemas) (constructors : Array IxIR2.CtorId) (words : Words) (index : Nat) (box : IxIR1.NodeBox) :=
  Nonempty (NodeData schemas constructors words index box)

/-- The live-cell relation records full leaf contents and unit reference
counts. A dead cell may remain reserved only while a physical credit names
it. This implication supplies complete native reclamation at a scalar halt. -/
structure HeapAt (schemas : Schemas) (constructors : Array IxIR2.CtorId) (offset : Nat) (store : Store)
    (reserved : List Nat) (words : Words) : Prop where
  extent : offset ≤ store.heap.nodes.size
  bounded : store.heap.nodes.size - offset ≤ capacity
  offsetDead : ∀ location < offset, store.get? location = none
  cursor : words 0 = UInt64.ofNat (32 * (store.heap.nodes.size - offset))
  statistics : ∀ field, 2 ≤ field → field ≤ 8 → words field = UInt64.ofNat (counters store field)
  reservations : words 9 = UInt64.ofNat reserved.length
  live : ∀ location box, store.get? location = some box →
    offset ≤ location ∧ NodeAt schemas constructors words (location - offset) box
  dead : ∀ location, offset ≤ location → location < store.heap.nodes.size → store.get? location = none →
    words (cellSlot (location - offset) 0) = 0 ∨
      (words (cellSlot (location - offset) 0) = 1 ∧ location ∈ reserved)

theorem HeapAt.reclaimed {schemas constructors offset store words} (represented : HeapAt schemas constructors offset store [] words)
    (empty : ∀ location, store.get? location = none) :
    words 9 = 0 ∧ ∀ index < store.heap.nodes.size - offset, words (cellSlot index 0) = 0 := by
  refine ⟨by simpa using represented.reservations, fun index bound => ?_⟩
  have dead := represented.dead (offset + index) (by omega) (by omega) (empty _)
  simpa only [Nat.add_sub_cancel_left, List.not_mem_nil, and_false, or_false] using dead

end Compilatrix.X86.PhysicalHeap
