import IxCC.Rt.Rc.Proof.Resume

/-! Suspended-parent cursor. `visited` counts transferred children, including
the currently executing child. Only the unvisited suffix remains in this
parent's pending tokens; the overwritten field0 is never read as a child. -/
namespace IxCC.Rt.Rc.Procs
open Lir
open IxCC.Rt.Proof

structure PendingCursor (addresses : AddressMap) (before mem : X86.Memory)
    (address predecessor : Word) (original : Own.Body) (visited : Nat) : Prop where
  visited_positive : 0 < visited
  visited_le : visited ≤ original.fields.length
  small : original.fields.length < 32
  remaining : mem.bytes address = (UInt64.ofNat (original.fields.length-visited)).toUInt8
  link : WordAt mem (address+8) predecessor
  header_tail : ∀ j, 0 < j → j < 8 →
    mem.bytes (address+UInt64.ofNat j) = before.bytes (address+UInt64.ofNat j)
  readable : mem.readable = before.readable
  writable : mem.writable = before.writable
  suffix : ∀ j value, original.fields[j]? = some value → visited ≤ j →
    ∃ word, valueWord addresses value = some word ∧
      WordAt mem (address + UInt64.ofNat (8+8*j)) word

theorem PendingParent.cursor {addresses before mem address predecessor original}
    (h : PendingParent addresses before mem address predecessor original) :
    PendingCursor addresses before mem address predecessor original 1 where
  visited_positive := by omega
  visited_le := h.nonempty
  small := h.small
  remaining := h.remaining
  link := h.link
  header_tail := h.header_tail
  readable := h.readable
  writable := h.writable
  suffix j value hj hv := h.suffix j value hj (by omega)

theorem small_word_sub {a b : Nat} (ha : a < 2^64) (hb : b ≤ a) :
    UInt64.ofNat a - UInt64.ofNat b = UInt64.ofNat (a-b) := by
  apply UInt64.toNat_inj.mp
  have ha' := toNat_ofNat_lt ha
  have hb' := toNat_ofNat_lt (n := b) (by omega)
  rw [sub_toNat_of_le (by rw [ha', hb']; exact hb), ha', hb',
    toNat_ofNat_lt (by omega)]

theorem cursor_field_address (address : Word) {fields visited : Nat}
    (hf : fields < 32) (hv : visited ≤ fields) :
    nextFieldAddress address (UInt64.ofNat (fields+1)) (UInt64.ofNat (fields-visited)) =
      address + UInt64.ofNat (8+8*visited) := by
  unfold nextFieldAddress
  have hs : UInt64.ofNat (fields+1) - 1 = UInt64.ofNat fields := by
    simpa using small_word_sub (a := fields+1) (b := 1) (by omega) (by omega)
  rw [hs, small_word_sub (by omega) (by omega)]
  have hn : fields - (fields-visited) = visited := by omega
  rw [hn]
  rw [show (8 : Word) = UInt64.ofNat 8 from rfl, ← UInt64.ofNat_mul,
    UInt64.add_assoc, ← UInt64.ofNat_add]
  congr 2
  omega

theorem PendingCursor.next_child {addresses before mem address predecessor original visited}
    (h : PendingCursor addresses before mem address predecessor original visited)
    {child : Own.RVal} (hc : original.fields[visited]? = some child) :
    ∃ word, valueWord addresses child = some word ∧
      loadWord mem .w64 .zero
        (nextFieldAddress address (UInt64.ofNat (original.fields.length+1))
          (UInt64.ofNat (original.fields.length-visited))) = some word := by
  obtain ⟨word, hv, hw⟩ := h.suffix visited child hc (by omega)
  refine ⟨word, hv, ?_⟩
  rw [cursor_field_address address h.small h.visited_le]
  simp only [loadWord, hw.read64]




end IxCC.Rt.Rc.Procs
