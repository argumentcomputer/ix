import IxCC.Rt.Rc.Proof.RecycleClasses

namespace IxCC.Rt.Rc.Procs
open Lir

theorem ReleaseInvariant.recycle_free_placed
    {heap addresses mem external current frames context base bump limit slots lists}
    (h : ReleaseInvariant heap addresses mem external current frames context base bump limit slots lists)
    {parent : Slot} (hp : parent ∈ slots) {location suffix predecessor}
    (hk : parent.kind = .pending location suffix predecessor)
    {cls : Nat} {address : Word} (hm : address ∈ pushFree lists parent.cls parent.address cls) :
    ∃ slot ∈ recycleSlots parent.address slots,
      slot.address = address ∧ slot.cls = cls ∧ slot.kind = .free := by
  by_cases he : cls = parent.cls ∧ address = parent.address
  · rcases he with ⟨rfl, rfl⟩
    refine ⟨{parent with kind := .free}, ?_, rfl, rfl, rfl⟩
    apply List.mem_map.mpr
    exact ⟨parent, hp, by simp⟩
  · have hold : address ∈ lists cls := by
      by_cases hc : cls = parent.cls
      · have ha : address ≠ parent.address := by intro ha; exact he ⟨hc, ha⟩
        simpa [pushFree, hc, ha] using hm
      · simpa [pushFree, hc] using hm
    obtain ⟨slot, hs, ha, hc, hf⟩ := h.free_placed cls address hold
    have hne : slot.address ≠ parent.address := by
      intro had
      have heq := h.partition.address_unique hs hp had
      subst slot
      rw [hk] at hf
      cases hf
    refine ⟨slot, ?_, ha, hc, hf⟩
    exact List.mem_map.mpr ⟨slot, hs, by simp [hne]⟩

/-- Surviving suspended frames retain physical slot placement after the top
parent is recycled. Distinct cursor addresses derive the needed exclusion. -/
theorem ReleaseInvariant.recycle_cursors_placed
    {heap addresses mem external current top tail context base bump limit slots lists}
    (h : ReleaseInvariant heap addresses mem external current (top :: tail)
      context base bump limit slots lists)
    {parent : Slot} (hp : parent ∈ slots) (ha : parent.address = top.address)
    (earlier : List CursorFrame) (frame : CursorFrame) (later : List CursorFrame)
    (he : tail = earlier ++ frame :: later) :
    ∃ slot ∈ recycleSlots parent.address slots,
      slot.address = frame.address ∧ slot.cls = smallClass frame.original.fields.length ∧
      slot.kind = .pending frame.location frame.suffix (cursorHead later) := by
  obtain ⟨slot, hs, had, hc, hk⟩ := h.cursors_placed (top :: earlier) frame later (by simp [he])
  have hn : top.address ∉ tail.map CursorFrame.address := by
    have hd := h.cursor_distinct
    simp only [List.map_cons, List.nodup_cons] at hd
    exact hd.1
  have hne : slot.address ≠ parent.address := by
    intro eq
    have haddr : frame.address = top.address := had.symm.trans (eq.trans ha)
    apply hn
    apply List.mem_map.mpr
    exact ⟨frame, by simp [he], haddr⟩
  exact ⟨slot, List.mem_map.mpr ⟨slot, hs, by simp [hne]⟩, had, hc, hk⟩




theorem ReleaseInvariant.recycle_pending_exact
    {heap addresses mem external current top tail context base bump limit slots lists}
    (h : ReleaseInvariant heap addresses mem external current (top :: tail)
      context base bump limit slots lists) :
    ∀ slot ∈ recycleSlots top.address slots, ∀ location suffix predecessor,
      slot.kind = .pending location suffix predecessor ↔
        ∃ earlier frame later, tail = earlier ++ frame :: later ∧
          frame.location = location ∧ frame.address = slot.address ∧
          slot.cls = smallClass frame.original.fields.length ∧
          frame.suffix = suffix ∧ predecessor = cursorHead later := by
  intro slot hm location suffix predecessor
  obtain ⟨old, hold, rfl⟩ := List.mem_map.mp hm
  have hn : top.address ∉ tail.map CursorFrame.address := by
    have hd := h.cursor_distinct
    simp only [List.map_cons, List.nodup_cons] at hd
    exact hd.1
  by_cases he : old.address = top.address
  · simp only [he, ite_true]
    constructor
    · intro impossible; cases impossible
    · rintro ⟨earlier, frame, later, htail, hloc, haddr, hcls, hsuf, hpred⟩
      exfalso
      apply hn
      exact List.mem_map.mpr ⟨frame, by simp [htail], by simpa only [he] using haddr⟩
  · simp only [he, ite_false]
    constructor
    · intro hk
      obtain ⟨earlier, frame, later, hframes, hloc, haddr, hcls, hsuf, hpred⟩ :=
        (h.pending_exact old hold location suffix predecessor).mp hk
      cases earlier with
      | nil =>
        have ht : top = frame := (List.cons.inj hframes).1
        exact False.elim (he (haddr.symm.trans (congrArg CursorFrame.address ht).symm))
      | cons first earlier =>
        have ht : tail = earlier ++ frame :: later := (List.cons.inj hframes).2
        exact ⟨earlier, frame, later, ht, hloc, haddr, hcls, hsuf, hpred⟩
    · rintro ⟨earlier, frame, later, htail, hloc, haddr, hcls, hsuf, hpred⟩
      apply (h.pending_exact old hold location suffix predecessor).mpr
      exact ⟨top :: earlier, frame, later, by simp [htail], hloc, haddr, hcls, hsuf, hpred⟩



theorem ReleaseInvariant.recycle_chains
    {heap addresses mem external current frames context base bump limit slots lists}
    (h : ReleaseInvariant heap addresses mem external current frames context base bump limit slots lists)
    {parent : Slot} (hp : parent ∈ slots) {location suffix predecessor}
    (hk : parent.kind = .pending location suffix predecessor)
    (hr : ∀ j < 8, mem.readable (parent.address+UInt64.ofNat j) = true) (cls : Nat) :
    FreeChain (recycleParent mem context (UInt64.ofNat parent.cls) parent.address
      ((lists parent.cls).headD 0)) (pushFree lists parent.cls parent.address cls) := by
  by_cases he : cls = parent.cls
  · subst cls
    simpa only [pushFree, ite_true] using (h.recycle_chain hp hk hr).1
  · simp only [pushFree, if_neg he]
    have vp := h.partition.valid parent hp
    have hb := h.partition.bounds
    apply (h.free_chains cls).recycle_frame (by omega) (h.head_fit parent.cls vp.1 vp.2.1)
    · intro a ha
      exact (h.pending_free_separation hp hk ha).1
    · intro a ha
      have hpsep := (h.pending_free_separation hp hk ha).2
      obtain ⟨free, hm, had, hc, hf⟩ := h.free_placed cls a ha
      have vs := h.partition.valid free hm
      have hs := h.head_disjoint parent.cls vp.1 vp.2.1 free hm
      rw [had] at hs
      refine ⟨hpsep, ?_⟩
      rcases hs with hs | hs
      · exact Or.inr hs
      · left; omega


end IxCC.Rt.Rc.Procs
