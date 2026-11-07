import IxCC.Xv.XlSemantics

/-!
# Xl locations

Reading and writing Xl locations (`Xl.read`, `Xl.write`): a write of a
usable location succeeds, sets that location, leaves every other one alone
and keeps the frame's control fields. Registers are an array of sixteen
entries, which every register file the semantics builds keeps
(`Regs.size_set`).
-/

namespace IxCC.Xv.Xl

open IxCC.Lir (Word)

theorem Regs.size_set (rs : Regs) (r : X86.GPR) (v : Option Word) : (rs.set r v).size = rs.size := by
  simp [Regs.set]

theorem Regs.get_set (rs : Regs) (hs : rs.size = 16) (r r' : X86.GPR) (v : Option Word) :
    (rs.set r v).get r' = if r' = r then v else rs.get r' := by
  unfold Regs.get Regs.set
  rw [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]
  have hlt : gprIndex r < rs.size := by
    rw [hs]; cases r <;> decide
  by_cases h : r' = r
  · subst h; simp [hlt]
  · have : gprIndex r ≠ gprIndex r' := fun e => h (by
      cases r <;> cases r' <;> simp_all [gprIndex])
    simp [this, h]

theorem Regs.empty_size : Regs.empty.size = 16 := rfl

theorem Regs.get_empty (r : X86.GPR) : Regs.empty.get r = none := by
  cases r <;> rfl

/-- A location a write may name: an allocatable register, a slot, an
incoming cell the frame has, or an outgoing cell. -/
def WriteOk (fr : Frame) : Loc → Prop
  | .reg r => reserved r = false
  | .slot _ => True
  | .inArg i => i < fr.inArgs.size
  | .outArg _ => True

/-- The frame fields no location write changes. -/
structure Frame.SameCtl (fr fr' : Frame) : Prop where
  fn : fr'.fn = fr.fn
  label : fr'.label = fr.label
  pos : fr'.pos = fr.pos
  saved : fr'.saved = fr.saved
  clobber : fr'.clobber = fr.clobber
  results : fr'.results = fr.results
  inArgs : fr'.inArgs.size = fr.inArgs.size

theorem Frame.SameCtl.refl (fr : Frame) : Frame.SameCtl fr fr := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem Frame.SameCtl.trans {fr fr' fr'' : Frame} (h : Frame.SameCtl fr fr') (h' : Frame.SameCtl fr' fr'') :
    Frame.SameCtl fr fr'' :=
  ⟨h'.fn.trans h.fn, h'.label.trans h.label, h'.pos.trans h.pos, h'.saved.trans h.saved,
    h'.clobber.trans h.clobber, h'.results.trans h.results, h'.inArgs.trans h.inArgs⟩

theorem write_ok {regs : Regs} {fr : Frame} {l : Loc} (h : WriteOk fr l) (v : Word) :
    ∃ regs' fr', write regs fr l v = some (regs', fr') := by
  cases l with
  | reg r => simp only [WriteOk] at h; simp [write, h]
  | slot i => simp [write]
  | inArg i => simp only [WriteOk] at h; simp [write, h]
  | outArg i => simp [write]

theorem write_spec {regs regs' : Regs} {fr fr' : Frame} {l : Loc} {v : Word} (hs : regs.size = 16)
    (h : write regs fr l v = some (regs', fr')) :
    read regs' fr' l = some v ∧ (∀ l', l' ≠ l → read regs' fr' l' = read regs fr l') ∧
      Frame.SameCtl fr fr' ∧ regs'.size = 16 := by
  cases l with
  | reg r =>
    simp only [write] at h
    split at h
    · simp at h
    · rename_i hr
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨by simp [read, hr, Regs.get_set _ hs], ?_, Frame.SameCtl.refl _, by rw [Regs.size_set, hs]⟩
      intro l' hl'
      cases l' with
      | reg r' =>
        have : r' ≠ r := fun e => hl' (e ▸ rfl)
        simp [read, Regs.get_set _ hs, this]
      | _ => rfl
  | slot i =>
    simp only [write, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨by simp [read], ?_, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, hs⟩
    intro l' hl'
    cases l' with
    | slot j =>
      have : i ≠ j := fun e => hl' (e ▸ rfl)
      simp [read, Std.HashMap.getElem?_insert, this]
    | _ => rfl
  | inArg i =>
    simp only [write] at h
    split at h
    · rename_i hi
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨by simp [read, Array.set!_eq_setIfInBounds, hi], ?_,
        ⟨rfl, rfl, rfl, rfl, rfl, rfl, by simp⟩, hs⟩
      intro l' hl'
      cases l' with
      | inArg j =>
        have : i ≠ j := fun e => hl' (e ▸ rfl)
        simp [read, Array.set!_eq_setIfInBounds, this]
      | _ => rfl
    · simp at h
  | outArg i =>
    simp only [write, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨by simp [read], ?_, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, hs⟩
    intro l' hl'
    cases l' with
    | outArg j =>
      have : i ≠ j := fun e => hl' (e ▸ rfl)
      simp [read, Std.HashMap.getElem?_insert, this]
    | _ => rfl

/-- A read of an allocatable register is the register file's. -/
theorem read_reg {regs : Regs} {fr : Frame} {r : X86.GPR} (h : reserved r = false) :
    read regs fr (.reg r) = regs.get r := by
  simp [read, h]

end IxCC.Xv.Xl
