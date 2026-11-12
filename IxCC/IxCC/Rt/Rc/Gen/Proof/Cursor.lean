import IxCC.Rt.Rc.Gen.Proof.Resume
import IxCC.Rt.Rc.Proof.Cursor

/-! The suspended-parent cursor of the general release. `visited` counts the scanned fields
transferred, the one being released included; the count word holds `scan − visited`; only the
unvisited scanned fields remain to be read. -/
namespace IxCC.Rt.Rc.Gen
open IxCC.Rt.Rc.Procs
open Lir
open IxCC.Rt.Proof

structure PendingCursor (addresses : AddressMap) (before mem : X86.Memory)
    (address predecessor : Word) (original : Own.Body) (visited : Nat) : Prop where
  visited_positive : 0 < visited
  visited_le : visited ≤ original.ctor.nobj
  layout : (layoutOf original.ctor).ok = true
  arity : original.fields.length = original.ctor.nobj + original.ctor.nscalar
  scalars : ∀ j value, original.fields[j]? = some value → original.ctor.nobj ≤ j →
    ∃ n, value = .lit (.nat n)
  remaining : mem.read .w32 (address+4) = UInt64.ofNat (original.ctor.nobj-visited)
  link : WordAt mem (address+8) predecessor
  header_low : ∀ j < 4,
    mem.bytes (address+UInt64.ofNat j) = before.bytes (address+UInt64.ofNat j)
  readable : mem.readable = before.readable
  writable : mem.writable = before.writable
  suffix : ∀ j value, original.fields[j]? = some value → visited ≤ j → j < original.ctor.nobj →
    ∃ word, valueWord addresses value = some word ∧
      WordAt mem (address + UInt64.ofNat (8+8*j)) word

theorem PendingParent.cursor {addresses before mem address predecessor original}
    (h : PendingParent addresses before mem address predecessor original) :
    PendingCursor addresses before mem address predecessor original 1 where
  visited_positive := by omega
  visited_le := h.nonempty
  layout := h.layout
  arity := h.arity
  scalars := h.scalars
  remaining := h.remaining
  link := h.link
  header_low := h.header_low
  readable := h.readable
  writable := h.writable
  suffix j value hj hv hs := h.suffix j value hj (by omega) hs

theorem cursor_field_address (address : Word) {scan visited : Nat}
    (hs : scan < 256) (hv : visited ≤ scan) :
    nextFieldAddress address (UInt64.ofNat scan) (UInt64.ofNat (scan-visited)) =
      address + UInt64.ofNat (8+8*visited) := by
  unfold nextFieldAddress
  rw [small_word_sub (by omega) (by omega)]
  have hn : scan - (scan-visited) = visited := by omega
  rw [hn]
  rw [show (8 : Word) = UInt64.ofNat 8 from rfl, ← UInt64.ofNat_mul,
    UInt64.add_assoc, ← UInt64.ofNat_add]
  congr 2
  omega

theorem PendingCursor.next_child {addresses before mem address predecessor original visited}
    (h : PendingCursor addresses before mem address predecessor original visited)
    (hv : visited < original.ctor.nobj)
    {child : Own.RVal} (hc : original.fields[visited]? = some child) :
    ∃ word, valueWord addresses child = some word ∧
      loadWord mem .w64 .zero
        (nextFieldAddress address (UInt64.ofNat original.ctor.nobj)
          (UInt64.ofNat (original.ctor.nobj-visited))) = some word := by
  obtain ⟨word, hv', hw⟩ := h.suffix visited child hc (by omega) hv
  refine ⟨word, hv', ?_⟩
  have hs := (classOf_lt h.layout).2.1
  rw [cursor_field_address address (by omega) h.visited_le]
  simp only [loadWord, hw.read64]

end IxCC.Rt.Rc.Gen
