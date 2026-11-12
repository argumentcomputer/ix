import IxCC.Rt.Rc.Gen.Proof.Cursor

/-! The countdown store of block 8 preserves the continuation link, the header's low half and the
unvisited scanned fields; any byte-preserving change of other memory preserves a cursor. -/
namespace IxCC.Rt.Rc.Gen
open IxCC.Rt.Rc.Procs
open Lir
open IxCC.Rt.Proof

theorem PendingCursor.bytes {addresses before mem address predecessor original visited}
    (h : PendingCursor addresses before mem address predecessor original visited) :
    16 ≤ cellBytesOf original.ctor ∧ 8 * (1 + original.ctor.nobj) ≤ cellBytesOf original.ctor := by
  have := cellBytesOf_le h.layout
  omega

theorem PendingCursor.advance {addresses before mem address predecessor original visited}
    (h : PendingCursor addresses before mem address predecessor original visited)
    (hv : visited < original.ctor.nobj)
    (hfit : address.toNat + cellBytesOf original.ctor < 2^63) :
    PendingCursor addresses before
      (resumeParent mem address (UInt64.ofNat (original.ctor.nobj-visited)))
      address predecessor original (visited+1) := by
  have hb := h.bytes
  have hscan := (classOf_lt h.layout).2.1
  have hs : UInt64.ofNat (original.ctor.nobj-visited)-1 =
      UInt64.ofNat (original.ctor.nobj-(visited+1)) := by
    have he : original.ctor.nobj-visited-1 = original.ctor.nobj-(visited+1) := by omega
    have hh := small_word_sub (a := original.ctor.nobj-visited) (b := 1) (by omega) (by omega)
    simpa [he] using hh
  have hfit8 : address.toNat + 8 ≤ 2^64 := by omega
  have ha8 : (address+8).toNat = address.toNat+8 :=
    addr_toNat (a := address) (i := 8) (by omega)
  refine {
    visited_positive := by omega
    visited_le := by omega
    layout := h.layout
    arity := h.arity
    scalars := h.scalars
    remaining := ?_
    link := ?_
    header_low := ?_
    readable := ?_
    writable := ?_
    suffix := ?_ }
  · unfold resumeParent storeCount
    rw [read32_write32, hs]
    apply truncate32_small
    rw [UInt64.toNat_ofNat']
    omega
  · exact storeCount_word h.link hfit8 (by rw [ha8]; omega) (by right; rw [ha8]; omega)
  · intro j hj
    have haj : (address+UInt64.ofNat j).toNat = address.toNat+j := addr_toNat (by omega)
    unfold resumeParent
    rw [(storeCount_frame _ address _ hfit8).outside _ (by left; rw [haj]; omega)]
    exact h.header_low j hj
  · simpa [resumeParent, storeCount, X86.Memory.write] using h.readable
  · simpa [resumeParent, storeCount, X86.Memory.write] using h.writable
  · intro j value hj hvisited hs'
    obtain ⟨word, hvw, hw⟩ := h.suffix j value hj (by omega) hs'
    have haj : (address+UInt64.ofNat (8+8*j)).toNat = address.toNat+(8+8*j) :=
      addr_toNat (by omega)
    exact ⟨word, hvw, storeCount_word hw hfit8 (by rw [haj]; omega) (by right; rw [haj]; omega)⟩

/-- Other pending frames are preserved by a change that keeps their bytes. -/
theorem PendingCursor.frame {addresses before mem mem' address predecessor original visited}
    (h : PendingCursor addresses before mem address predecessor original visited)
    (hr : mem'.readable = mem.readable) (hw : mem'.writable = mem.writable)
    (hb : ∀ j < cellBytesOf original.ctor,
      mem'.bytes (address+UInt64.ofNat j) = mem.bytes (address+UInt64.ofNat j)) :
    PendingCursor addresses before mem' address predecessor original visited := by
  have hbytes := h.bytes
  refine { h with
    remaining := ?_, link := ?_, header_low := ?_
    readable := hr.trans h.readable
    writable := hw.trans h.writable
    suffix := ?_ }
  · rw [← h.remaining]
    change mem'.readLittle (address+4) 4 = mem.readLittle (address+4) 4
    apply X86.Memory.readLittle_congr
    intro j hj
    rw [cell_offset4]
    exact hb (4+j) (by omega)
  · refine ⟨?_, ?_⟩
    · intro j hj
      rw [field0_address, hb (8+j) (by omega)]
      simpa [field0_address] using h.link.bytes j hj
    · intro j hj
      rw [hr]
      exact h.link.readable j hj
  · intro j hj
    rw [hb j (by omega)]
    exact h.header_low j hj
  · intro j value hj hvisited hs
    obtain ⟨word, hv, hword⟩ := h.suffix j value hj hvisited hs
    refine ⟨word, hv, ?_, ?_⟩
    · intro k hk
      have he : (address+UInt64.ofNat (8+8*j))+UInt64.ofNat k =
          address+UInt64.ofNat (8+8*j+k) := by
        rw [UInt64.ofNat_add]; simp [UInt64.add_assoc]
      rw [he, hb (8+8*j+k) (by omega)]
      simpa only [he] using hword.bytes k hk
    · intro k hk
      rw [hr]
      exact hword.readable k hk

end IxCC.Rt.Rc.Gen
