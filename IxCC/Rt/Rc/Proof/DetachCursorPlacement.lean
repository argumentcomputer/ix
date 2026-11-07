import IxCC.Rt.Rc.Proof.DetachPlacement

namespace IxCC.Rt.Rc.Procs
open Lir

theorem ReleaseInvariant.live_not_cursor
    {heap addresses mem external current frames context base bump limit slots lists}
    (h : ReleaseInvariant heap addresses mem external current frames context base bump limit slots lists)
    {parent : Slot} (hp : parent ∈ slots) {location} (hk : parent.kind = .live location) :
    parent.address ∉ frames.map CursorFrame.address := by
  intro hm
  obtain ⟨frame, hf, ha⟩ := List.mem_map.mp hm
  obtain ⟨earlier, later, he⟩ := List.mem_iff_append.mp hf
  obtain ⟨slot, hs, had, hc, hkind⟩ := h.cursors_placed earlier frame later he
  have eq := h.partition.address_unique hs hp (had.trans ha)
  subst slot
  rw [hk] at hkind
  cases hkind

theorem ReleaseInvariant.detach_cursors_placed
    {heap addresses mem external current frames context base bump limit slots lists}
    (h : ReleaseInvariant heap addresses mem external current frames context base bump limit slots lists)
    {parent : Slot} (hp : parent ∈ slots) {top : CursorFrame}
    (hk : parent.kind = .live top.location) (ha : parent.address = top.address)
    (hc : parent.cls = smallClass top.original.fields.length)
    (earlier : List CursorFrame) (frame : CursorFrame) (later : List CursorFrame)
    (he : top :: frames = earlier ++ frame :: later) :
    ∃ slot ∈ advanceSlots parent.address top.location top.suffix (cursorHead frames) slots,
      slot.address = frame.address ∧ slot.cls = smallClass frame.original.fields.length ∧
      slot.kind = .pending frame.location frame.suffix (cursorHead later) := by
  cases earlier with
  | nil =>
    have hf : top = frame := (List.cons.inj he).1
    have ht : frames = later := (List.cons.inj he).2
    subst frame
    subst later
    exact ⟨{parent with kind := .pending top.location top.suffix (cursorHead frames)},
      List.mem_map.mpr ⟨parent, hp, by simp⟩, ha, hc, rfl⟩
  | cons first earlier =>
    have ht : frames = earlier ++ frame :: later := (List.cons.inj he).2
    obtain ⟨slot, hs, had, hcls, hkind⟩ := h.cursors_placed earlier frame later ht
    have hne : slot.address ≠ parent.address := by
      intro haddr
      exact h.live_not_cursor hp hk (List.mem_map.mpr ⟨frame, by simp [ht], had.symm.trans haddr⟩)
    exact ⟨slot, List.mem_map.mpr ⟨slot, hs, by simp [hne]⟩, had, hcls, hkind⟩

theorem ReleaseInvariant.detach_pending_exact
    {heap addresses mem external current frames context base bump limit slots lists}
    (h : ReleaseInvariant heap addresses mem external current frames context base bump limit slots lists)
    {parent : Slot} (hp : parent ∈ slots) {top : CursorFrame}
    (hk : parent.kind = .live top.location) (ha : parent.address = top.address)
    (hc : parent.cls = smallClass top.original.fields.length) :
    ∀ slot ∈ advanceSlots parent.address top.location top.suffix (cursorHead frames) slots,
      ∀ location suffix predecessor,
      slot.kind = .pending location suffix predecessor ↔
        ∃ earlier frame later, top :: frames = earlier ++ frame :: later ∧
          frame.location = location ∧ frame.address = slot.address ∧
          slot.cls = smallClass frame.original.fields.length ∧
          frame.suffix = suffix ∧ predecessor = cursorHead later := by
  intro slot hm location suffix predecessor
  obtain ⟨old, hold, rfl⟩ := List.mem_map.mp hm
  by_cases he : old.address = parent.address
  · have ho := h.partition.address_unique hold hp he
    subst old
    simp only [ite_true]
    constructor
    · intro hkind
      have eq : top.location = location ∧ top.suffix = suffix ∧ cursorHead frames = predecessor := by
        simpa using hkind
      exact ⟨[], top, frames, rfl, eq.1, ha.symm, hc, eq.2.1, eq.2.2.symm⟩
    · rintro ⟨earlier, frame, later, hframes, hloc, had, hcls, hsuf, hpred⟩
      cases earlier with
      | nil =>
        have hf : top = frame := (List.cons.inj hframes).1
        have ht : frames = later := (List.cons.inj hframes).2
        subst frame
        subst later
        rw [← hloc, ← hsuf, hpred]
      | cons first earlier =>
        have ht : frames = earlier ++ frame :: later := (List.cons.inj hframes).2
        exact False.elim (h.live_not_cursor hp hk (List.mem_map.mpr ⟨frame, by simp [ht], had⟩))
  · simp only [he, ite_false]
    constructor
    · intro hkind
      obtain ⟨earlier, frame, later, hframes, hloc, had, hcls, hsuf, hpred⟩ :=
        (h.pending_exact old hold location suffix predecessor).mp hkind
      exact ⟨top :: earlier, frame, later, by simp [hframes], hloc, had, hcls, hsuf, hpred⟩
    · rintro ⟨earlier, frame, later, hframes, hloc, had, hcls, hsuf, hpred⟩
      cases earlier with
      | nil =>
        have hf : top = frame := (List.cons.inj hframes).1
        exact False.elim (he (had.symm.trans ((congrArg CursorFrame.address hf).symm.trans ha.symm)))
      | cons first earlier =>
        have ht : frames = earlier ++ frame :: later := (List.cons.inj hframes).2
        exact (h.pending_exact old hold location suffix predecessor).mpr
          ⟨earlier, frame, later, ht, hloc, had, hcls, hsuf, hpred⟩




end IxCC.Rt.Rc.Procs
