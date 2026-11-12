import IxCC.Rt.Rc.Gen.Proof.DetachCursorPlacement
import IxCC.Rt.Rc.Gen.Proof.DetachFree
import IxCC.Rt.Rc.Gen.Proof.LiveHeader

namespace IxCC.Rt.Rc.Gen
open IxCC.Rt.Rc.Procs
open IxCC.Rt.Proof
open Lir
open IxCC.Own IxCC.Own.Rc

def detachFrame (location : Nat) (address : Word) (body : Body) (mem : X86.Memory) : CursorFrame :=
  { location, address, original := body, before := mem, visited := 1 }

/-- Complete unique-parent memory transition. The parent ceases to be a live
abstract cell before its first payload becomes a continuation link. Its first
child and every remaining field become pending tokens, with no duplicated
edge in the surviving heap. -/
theorem ReleaseInvariant.detach_complete
    {heap addresses mem external location frames context base bump limit slots lists}
    (h : ReleaseInvariant cmax heap addresses mem external (some (.loc location)) frames
      context base bump limit slots lists)
    {body address} (hcell : heap.cell? location = some (.live 1 .dyn body))
    (haddress : addresses location = some address) (hn : 0 < body.ctor.nobj) {child suffix}
    (hfields : body.fields = child :: suffix) :
    ∃ parent ∈ slots,
      ReleaseInvariant cmax (setCell heap location .dead) addresses
        (detachParent mem address (cursorHead frames) body.ctor.nobj)
        external (some child) (detachFrame location address body mem :: frames)
        context base bump limit
        (advanceSlots parent.address location suffix (cursorHead frames) slots) lists := by
  obtain ⟨_, a, ha, cell⟩ := h.live.cell location 1 .dyn body hcell
  have hae : a = address := by rw [haddress] at ha; exact (Option.some.inj ha).symm
  subst a
  obtain ⟨parent, hp, hk⟩ := h.partition.placed location 1 body hcell
  obtain ⟨r, b, hc, had, hcls⟩ := h.partition.live parent hp location hk
  rw [hcell] at hc
  have heq : r = 1 ∧ b = body := by simpa using hc.symm
  obtain ⟨hr, hb⟩ := heq
  subst r
  subst b
  have hpa : parent.address = address := by
    rw [haddress] at had
    exact (Option.some.inj had).symm
  have hclass : 2 ≤ classWords parent.cls := by
    rw [hcls]; have := cell.bytes; unfold cellBytesOf at this; omega
  have hb : Balance heap external (.loc location :: cursorTokens frames) := by simpa using h.balance
  have hedges := (unique_has_no_survivor hcell hb).2.2
  let top := detachFrame location address body mem
  let after := detachParent mem address (cursorHead frames) body.ctor.nobj
  have ht_suffix : top.suffix = suffix := by simp [top, detachFrame, CursorFrame.suffix, hfields]
  have htop : parent.address = top.address := hpa
  have htopcls : parent.cls = classOf top.original.ctor := hcls
  have htopkind : parent.kind = .live top.location := hk
  have hpend := cell.detach_pending hn (cursorHead frames)
  have htail : CursorChain addresses (setCell heap location .dead) after frames := by
    apply (h.cursors.free_cell hcell).frame
    intro frame hm
    simpa only [after, hpa] using h.detach_cursor_frame hp hk hclass (cursorHead frames) body.ctor.nobj hm
  refine ⟨parent, hp, {
    balance := ?_
    live := h.live.detach hcell haddress hedges _
    partition := h.partition.detach_pending hp hk hcell suffix _
    cursors := ?_
    cursor_distinct := ?_
    cursor_nonzero := ?_
    cursor_layout := ?_
    cursor_access := ?_
    cursor_class := ?_
    cursor_scan := ?_
    cursors_placed := ?_
    pending_exact := ?_
    free_exact := h.detach_free_exact hp hk suffix _
    free_distinct := h.free_distinct
    free_placed := ?_
    free_chains := ?_
    free_heads := ?_
    head_writable := ?_
    head_fit := h.head_fit
    context_fit := h.context_fit
    head_disjoint := ?_ }⟩
  · have hb' := balance_free hcell hb
    simpa [cursorTokens, top, detachFrame, CursorFrame.suffix, flattenPending, hfields] using hb'
  · have hl : location < heap.size := (Array.getElem?_eq_some_iff.mp hcell).1
    exact ⟨by simp [detachFrame, setCell_cell heap location _ hl], hpend.cursor, cell.fit, htail⟩
  · apply List.nodup_cons.mpr
    exact ⟨by simpa only [top, detachFrame, ← hpa] using h.live_not_cursor hp hk, h.cursor_distinct⟩
  · intro frame hm
    rcases List.mem_cons.mp hm with rfl | hm
    · exact cell.nonzero
    · exact h.cursor_nonzero frame hm
  · intro frame hm
    rcases List.mem_cons.mp hm with rfl | hm
    · exact cell.layout
    · exact h.cursor_layout frame hm
  · intro frame hm j hj
    rcases List.mem_cons.mp hm with rfl | hm
    · simpa [detachParent, storeCount, X86.Memory.write, detachFrame] using
        And.intro (cell.readable j hj) (cell.writable j hj)
    · simpa [detachParent, storeCount, X86.Memory.write] using h.cursor_access frame hm j hj
  · intro frame hm
    rcases List.mem_cons.mp hm with rfl | hm
    · exact (hpend.header_low 1 (by decide)).trans cell.class_byte
    · have hf := h.detach_cursor_frame hp hk hclass (cursorHead frames) body.ctor.nobj hm
      have hb' := hf.bytes_eq 1 (by have := h.cursor_bytes hm; omega)
      have he : after.bytes (frame.address+1) = mem.bytes (frame.address+1) := by
        simpa [after, hpa] using hb'
      exact he.trans (h.cursor_class frame hm)
  · intro frame hm
    rcases List.mem_cons.mp hm with rfl | hm
    · have h0 := hpend.header_low 0 (by decide)
      have hz : address + UInt64.ofNat 0 = address := by simp
      rw [hz] at h0
      exact h0.trans cell.scan_byte
    · have hf := h.detach_cursor_frame hp hk hclass (cursorHead frames) body.ctor.nobj hm
      have hb' := hf.bytes_eq 0 (by have := h.cursor_bytes hm; omega)
      have he : after.bytes frame.address = mem.bytes frame.address := by
        simpa [after, hpa] using hb'
      exact he.trans (h.cursor_scan frame hm)
  · have placed := h.detach_cursors_placed hp htopkind htop htopcls
    rw [ht_suffix] at placed
    simpa only [top, detachFrame] using placed
  · have pending := h.detach_pending_exact hp htopkind htop htopcls
    rw [ht_suffix] at pending
    simpa only [top, detachFrame] using pending
  · intro cls a hm
    exact h.detach_free_placed hp hk suffix _ hm
  · intro cls
    simpa only [hpa] using h.detach_free_chains hp hk hclass (cursorHead frames) body.ctor.nobj cls
  · intro cls hl hu
    simpa only [hpa] using h.detach_free_heads hp hclass (cursorHead frames) body.ctor.nobj hl hu
  · intro cls hl hu j hj
    simpa [detachParent, storeCount, X86.Memory.write] using h.head_writable cls hl hu j hj
  · intro cls hl hu slot hm
    obtain ⟨old, hold, rfl⟩ := List.mem_map.mp hm
    have hs := h.head_disjoint cls hl hu old hold
    by_cases he : old.address = parent.address <;> simpa [he] using hs


end IxCC.Rt.Rc.Gen
