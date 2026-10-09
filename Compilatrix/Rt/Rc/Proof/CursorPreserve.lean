import Compilatrix.Rt.Rc.Proof.Cursor

/-! Actual scan-byte update preserves the continuation link, all metadata,
and the still-unvisited fields. No successful machine execution is assumed. -/
namespace Compilatrix.Rt.Rc.Procs
open Lir
open Compilatrix.Rt.Proof

theorem PendingCursor.advance {addresses before mem address predecessor original visited}
    (h : PendingCursor addresses before mem address predecessor original visited)
    (hv : visited < original.fields.length)
    (hfit : address.toNat + cellBytes original.fields.length < 2^63) :
    PendingCursor addresses before
      (resumeParent mem address (UInt64.ofNat (original.fields.length-visited)))
      address predecessor original (visited+1) := by
  have hf := hfit
  simp only [cellBytes] at hf
  have hs : UInt64.ofNat (original.fields.length-visited)-1 =
      UInt64.ofNat (original.fields.length-(visited+1)) := by
    have he : original.fields.length-visited-1 = original.fields.length-(visited+1) := by omega
    have hh := small_word_sub (a := original.fields.length-visited) (b := 1)
      (by have := h.small; omega) (by omega)
    simpa [he] using hh
  have ha8 : (address+8).toNat = address.toNat+8 :=
    addr_toNat (a := address) (i := 8) (by omega)
  refine {
    visited_positive := by omega
    visited_le := by omega
    small := h.small
    remaining := ?_
    link := ?_
    header_tail := ?_
    readable := ?_
    writable := ?_
    suffix := ?_ }
  · simp [resumeParent, hs, X86.Memory.write, X86.Width.bytes,
      X86.Memory.writeLittle, X86.Memory.writeByte]
  · apply h.link.write_disjoint
    · simp only [X86.Width.bytes]; omega
    · rw [ha8]; omega
    · right; simp only [X86.Width.bytes]; rw [ha8]; omega
  · intro j hj hbound
    have haj : (address+UInt64.ofNat j).toNat = address.toNat+j := addr_toNat (by omega)
    unfold resumeParent X86.Memory.write
    simp only [X86.Width.bytes]
    rw [writeLittle_bytes_out (a := address) (by decide : 1 ≤ 8) (by omega)
      (by right; rw [haj]; omega)]
    exact h.header_tail j hj hbound
  · simpa [resumeParent, X86.Memory.write] using h.readable
  · simpa [resumeParent, X86.Memory.write] using h.writable
  · intro j value hj hvisited
    obtain ⟨word, hvw, hw⟩ := h.suffix j value hj (by omega)
    have hjbound := (List.getElem?_eq_some_iff.mp hj).1
    have haj : (address+UInt64.ofNat (8+8*j)).toNat = address.toNat+(8+8*j) :=
      addr_toNat (by omega)
    refine ⟨word, hvw, ?_⟩
    apply hw.write_disjoint
    · simp only [X86.Width.bytes]; omega
    · rw [haj]; omega
    · right; simp only [X86.Width.bytes]; rw [haj]; omega

/-- Other pending frames are preserved by a disjoint scan-byte update. The
frame relation refers to real bytes, not a presumed semantic simulation. -/
theorem PendingCursor.frame {addresses before mem mem' address predecessor original visited}
    (h : PendingCursor addresses before mem address predecessor original visited)
    (hr : mem'.readable = mem.readable) (hw : mem'.writable = mem.writable)
    (hb : ∀ j < cellBytes original.fields.length,
      mem'.bytes (address+UInt64.ofNat j) = mem.bytes (address+UInt64.ofNat j)) :
    PendingCursor addresses before mem' address predecessor original visited := by
  refine { h with
    remaining := ?_, link := ?_, header_tail := ?_
    readable := hr.trans h.readable
    writable := hw.trans h.writable
    suffix := ?_ }
  · have hz := hb 0 (by simp [cellBytes]; omega)
    have hz' : mem'.bytes address = mem.bytes address := by simpa using hz
    exact hz'.trans h.remaining
  · refine ⟨?_, ?_⟩
    · intro j hj
      rw [field0_address, hb (8+j) (by have := h.visited_positive; have := h.visited_le; simp only [cellBytes]; omega)]
      simpa [field0_address] using h.link.bytes j hj
    · intro j hj
      rw [hr]
      exact h.link.readable j hj
  · intro j hj hbound
    rw [hb j (by simp only [cellBytes]; omega)]
    exact h.header_tail j hj hbound
  · intro j value hj hvisited
    obtain ⟨word, hv, hword⟩ := h.suffix j value hj hvisited
    have hjbound := (List.getElem?_eq_some_iff.mp hj).1
    refine ⟨word, hv, ?_, ?_⟩
    · intro k hk
      have he : (address+UInt64.ofNat (8+8*j))+UInt64.ofNat k =
          address+UInt64.ofNat (8+8*j+k) := by
        rw [UInt64.ofNat_add]; simp [UInt64.add_assoc]
      rw [he, hb (8+8*j+k) (by simp only [cellBytes]; omega)]
      simpa only [he] using hword.bytes k hk
    · intro k hk
      rw [hr]
      exact hword.readable k hk



end Compilatrix.Rt.Rc.Procs
