import IxCC.Rt.Rc.Proof.PartitionAdvance
import IxCC.Rt.Rc.Proof.ResumeStep

namespace IxCC.Rt.Rc.Procs
open Lir

theorem ReleaseInvariant.advance_pending_exact
    {heap addresses mem external current top tail context base bump limit slots lists}
    (h : ReleaseInvariant heap addresses mem external current (top :: tail)
      context base bump limit slots lists)
    {parent : Slot} (hp : parent ∈ slots) (ha : parent.address = top.address)
    (hc : parent.cls = smallClass top.original.fields.length) :
    ∀ slot ∈ advanceSlots parent.address top.location (advanceFrame top).suffix (cursorHead tail) slots,
      ∀ location suffix predecessor,
      slot.kind = .pending location suffix predecessor ↔
        ∃ earlier frame later, advanceFrame top :: tail = earlier ++ frame :: later ∧
          frame.location = location ∧ frame.address = slot.address ∧
          slot.cls = smallClass frame.original.fields.length ∧
          frame.suffix = suffix ∧ predecessor = cursorHead later := by
  intro slot hm location suffix predecessor
  obtain ⟨old, hold, rfl⟩ := List.mem_map.mp hm
  have hn : top.address ∉ tail.map CursorFrame.address := by
    have hd := h.cursor_distinct
    simp only [List.map_cons, List.nodup_cons] at hd
    exact hd.1
  by_cases he : old.address = parent.address
  · have ho := h.partition.address_unique hold hp he
    subst old
    simp only [ite_true]
    constructor
    · intro hk
      have eq : top.location = location ∧ (advanceFrame top).suffix = suffix ∧
          cursorHead tail = predecessor := by simpa using hk
      exact ⟨[], advanceFrame top, tail, rfl, eq.1, ha.symm, hc, eq.2.1, eq.2.2.symm⟩
    · rintro ⟨earlier, frame, later, hframes, hloc, had, hcls, hsuf, hpred⟩
      cases earlier with
      | nil =>
        have hf : advanceFrame top = frame := (List.cons.inj hframes).1
        have ht : tail = later := (List.cons.inj hframes).2
        subst frame
        subst later
        rw [← hloc, ← hsuf, hpred]
        rfl
      | cons first earlier =>
        have ht : tail = earlier ++ frame :: later := (List.cons.inj hframes).2
        exfalso
        apply hn
        exact List.mem_map.mpr ⟨frame, by simp [ht], had.trans ha⟩
  · simp only [he, ite_false]
    constructor
    · intro hk
      obtain ⟨earlier, frame, later, hframes, hloc, had, hcls, hsuf, hpred⟩ :=
        (h.pending_exact old hold location suffix predecessor).mp hk
      cases earlier with
      | nil =>
        have hf : top = frame := (List.cons.inj hframes).1
        exfalso
        exact he (had.symm.trans ((congrArg CursorFrame.address hf).symm.trans ha.symm))
      | cons first earlier =>
        have ht : tail = earlier ++ frame :: later := (List.cons.inj hframes).2
        exact ⟨advanceFrame top :: earlier, frame, later, by simp [ht], hloc, had, hcls, hsuf, hpred⟩
    · rintro ⟨earlier, frame, later, hframes, hloc, had, hcls, hsuf, hpred⟩
      cases earlier with
      | nil =>
        have hf : advanceFrame top = frame := (List.cons.inj hframes).1
        exfalso
        apply he
        exact had.symm.trans ((congrArg CursorFrame.address hf).symm.trans ha.symm)
      | cons first earlier =>
        have ht : tail = earlier ++ frame :: later := (List.cons.inj hframes).2
        apply (h.pending_exact old hold location suffix predecessor).mpr
        exact ⟨top :: earlier, frame, later, by simp [ht], hloc, had, hcls, hsuf, hpred⟩

theorem ReleaseInvariant.advance_cursors_placed
    {heap addresses mem external current top tail context base bump limit slots lists}
    (h : ReleaseInvariant heap addresses mem external current (top :: tail)
      context base bump limit slots lists)
    {parent : Slot} (hp : parent ∈ slots) (ha : parent.address = top.address)
    (hc : parent.cls = smallClass top.original.fields.length)
    (earlier : List CursorFrame) (frame : CursorFrame) (later : List CursorFrame)
    (he : advanceFrame top :: tail = earlier ++ frame :: later) :
    ∃ slot ∈ advanceSlots parent.address top.location (advanceFrame top).suffix (cursorHead tail) slots,
      slot.address = frame.address ∧ slot.cls = smallClass frame.original.fields.length ∧
      slot.kind = .pending frame.location frame.suffix (cursorHead later) := by
  cases earlier with
  | nil =>
    have hf : advanceFrame top = frame := (List.cons.inj he).1
    have ht : tail = later := (List.cons.inj he).2
    subst frame
    subst later
    refine ⟨{parent with kind := .pending top.location (advanceFrame top).suffix (cursorHead tail)},
      List.mem_map.mpr ⟨parent, hp, by simp⟩, ha, hc, rfl⟩
  | cons first earlier =>
    have ht : tail = earlier ++ frame :: later := (List.cons.inj he).2
    obtain ⟨slot, hs, had, hcls, hk⟩ := h.cursors_placed (top :: earlier) frame later (by simp [ht])
    have hn : top.address ∉ tail.map CursorFrame.address := by
      have hd := h.cursor_distinct
      simp only [List.map_cons, List.nodup_cons] at hd
      exact hd.1
    have hne : slot.address ≠ parent.address := by
      intro haddr
      apply hn
      exact List.mem_map.mpr ⟨frame, by simp [ht], had.symm.trans (haddr.trans ha)⟩
    exact ⟨slot, List.mem_map.mpr ⟨slot, hs, by simp [hne]⟩, had, hcls, hk⟩



end IxCC.Rt.Rc.Procs
