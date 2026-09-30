import Compilatrix.Xv.Semantics
import Compilatrix.Xv.Validate.Proof.Map

/-!
# Register assignments

Both Xv and Xl run a row on registers: Xv places each operand position in a
fresh scratch register (`Xv.Placer`), Xl in its location's register or, for
a stack cell, a borrowed scratch register. A *register assignment* of bound
operands over a payload `α` is a `Bound (α × GPR)`: each operand keeps its
payload and gains the register it runs in. This module describes the Xv
placer as such an assignment (`Placer.bounds_spec`): the machine arguments
are the assignment's, the registers it hands out are distinct scratch
registers, and it loads each use's value into its register and reads each
definition back from its register.
-/

namespace Compilatrix.Xv

open Compilatrix.Lir (VReg)
open X86 (GPR)

variable {α : Type}

/-! ## Assignments -/

/-- The registers a placement hands out for a bound operand: every register
other than an implicit operand's fixed one. -/
def Bound.taken : Bound (α × GPR) → List GPR
  | .input _ a => a.regs.map (·.2)
  | .output _ x => [x.2]
  | .tied _ a _ => [a.2]
  | .memory _ m => m.regs.map (·.2)
  | .fixedUse .. | .fixedDef .. | .fixedTied .. => []

/-- Implicit operands sit in their fixed register, and a tied definition in
its use's register. -/
def Bound.Assigned : Bound (α × GPR) → Prop
  | .tied _ a x => a.2 = x.2
  | .fixedUse i a => a.2 = i.reg
  | .fixedDef i x => x.2 = i.reg
  | .fixedTied i a x => a.2 = i.reg ∧ x.2 = i.reg
  | _ => True

@[simp] theorem Bound.isSlot_map {β : Type} (f : α → β) (b : Bound α) : (b.map f).isSlot = b.isSlot := by
  cases b <;> rfl

@[simp] theorem Bound.uses_map {β : Type} (f : α → β) (b : Bound α) : (b.map f).uses = b.uses.map f := by
  cases b with
  | input s a => simp [Bound.map, Bound.uses]
  | memory s m => simp [Bound.map, Bound.uses]
  | _ => simp [Bound.map, Bound.uses]

@[simp] theorem Bound.defs_map {β : Type} (f : α → β) (b : Bound α) : (b.map f).defs = b.defs.map f := by
  cases b <;> simp [Bound.map, Bound.defs]

theorem slotArgs_cons {ρ : Type} (place addr : ρ → Option GPR) (b : Bound ρ) (bs : List (Bound ρ)) :
    slotArgs place addr (b :: bs) =
      if b.isSlot then (b.machine place addr).bind fun a => (a :: ·) <$> slotArgs place addr bs
      else slotArgs place addr bs := by
  unfold slotArgs
  by_cases h : b.isSlot <;> simp [h, List.mapM_cons, Option.bind_eq_bind]
  cases b.machine place addr <;> simp
  cases List.mapM (Bound.machine place addr) (List.filter Bound.isSlot bs) <;> rfl

/-! ## The Xv placer -/

theorem Placer.take_spec {p p' : Placer} {r : GPR} (h : p.take = some (r, p')) :
    p.free = r :: p'.free ∧ p'.loads = p.loads ∧ p'.reads = p.reads := by
  unfold Placer.take at h
  split at h
  · rename_i r' rs hf
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨hf, rfl, rfl⟩
  · simp at h

theorem Placer.use_spec {p p' : Placer} {x : VReg} {r : GPR} (h : p.use x = some (r, p')) :
    p.free = r :: p'.free ∧ p'.loads = (r, x) :: p.loads ∧ p'.reads = p.reads := by
  unfold Placer.use at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨⟨r', p₁⟩, ht, he⟩ := h
  simp only [pure, Option.some.injEq, Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  obtain ⟨hf, hl, hr⟩ := take_spec ht
  exact ⟨hf, by simp [hl], by simp [hr]⟩

theorem Placer.amode_spec {p p' : Placer} {am : Amode α} {f : α → VReg} {m : X86.MemAddr}
    (h : p.amode (am.map f) = some (m, p')) :
    ∃ amR : Amode (α × GPR), amR.map Prod.fst = am ∧ (amR.map Prod.snd).toMem some = some m ∧
      p.free = amR.regs.map (·.2) ++ p'.free ∧
      p'.loads = (amR.regs.map fun q => (q.2, f q.1)).reverse ++ p.loads ∧ p'.reads = p.reads := by
  rcases am with ⟨base, index, disp⟩
  rcases base with _ | (b | _) <;> rcases index with _ | ⟨x, s⟩
  · simp [Placer.amode, Amode.map] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨{ disp := disp }, rfl, rfl, by simp [Amode.regs], by simp [Amode.regs], rfl⟩
  · cases hu : p.use (f x) with
    | none => simp [Placer.amode, Amode.map, hu] at h
    | some q =>
      obtain ⟨r, p₁⟩ := q
      obtain ⟨hf, hl, hr⟩ := use_spec hu
      cases hi : indexReg r with
      | none => simp [Placer.amode, Amode.map, hu, hi] at h
      | some i =>
        simp [Placer.amode, Amode.map, hu, hi] at h
        obtain ⟨rfl, rfl⟩ := h
        refine ⟨{ index := some ((x, r), s), disp := disp }, rfl, ?_, ?_, ?_, hr⟩
        · simp [Amode.toMem, Amode.map, hi]
        · simp [Amode.regs, hf]
        · simp [Amode.regs, hl]
  · cases hu : p.use (f b) with
    | none => simp [Placer.amode, Amode.map, Base.map, hu] at h
    | some q =>
      obtain ⟨r, p₁⟩ := q
      obtain ⟨hf, hl, hr⟩ := use_spec hu
      simp [Placer.amode, Amode.map, Base.map, hu] at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨{ base := some (.r (b, r)), disp := disp }, rfl, ?_, ?_, ?_, hr⟩
      · simp [Amode.toMem, Amode.map, Base.map]
      · simp [Amode.regs, hf]
      · simp [Amode.regs, hl]
  · cases hu : p.use (f b) with
    | none => simp [Placer.amode, Amode.map, Base.map, hu] at h
    | some q =>
      obtain ⟨r, p₁⟩ := q
      obtain ⟨hf, hl, hr⟩ := use_spec hu
      cases hu' : p₁.use (f x) with
      | none => simp [Placer.amode, Amode.map, Base.map, hu, hu'] at h
      | some q' =>
        obtain ⟨r', p₂⟩ := q'
        obtain ⟨hf', hl', hr'⟩ := use_spec hu'
        cases hi : indexReg r' with
        | none => simp [Placer.amode, Amode.map, Base.map, hu, hu', hi] at h
        | some i =>
          simp [Placer.amode, Amode.map, Base.map, hu, hu', hi] at h
          obtain ⟨rfl, rfl⟩ := h
          refine ⟨{ base := some (.r (b, r)), index := some ((x, r'), s), disp := disp }, rfl, ?_,
            ?_, ?_, by rw [hr', hr]⟩
          · simp [Amode.toMem, Amode.map, Base.map, hi]
          · simp [Amode.regs, hf, hf']
          · simp [Amode.regs, hl, hl']
  · simp [Placer.amode, Amode.map, Base.map] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨{ base := some .ctx, disp := disp }, rfl, rfl, by simp [Amode.regs], by simp [Amode.regs],
      rfl⟩
  · cases hu : p.use (f x) with
    | none => simp [Placer.amode, Amode.map, Base.map, hu] at h
    | some q =>
      obtain ⟨r, p₁⟩ := q
      obtain ⟨hf, hl, hr⟩ := use_spec hu
      cases hi : indexReg r with
      | none => simp [Placer.amode, Amode.map, Base.map, hu, hi] at h
      | some i =>
        simp [Placer.amode, Amode.map, Base.map, hu, hi] at h
        obtain ⟨rfl, rfl⟩ := h
        refine ⟨{ base := some .ctx, index := some ((x, r), s), disp := disp }, rfl, ?_, ?_, ?_, hr⟩
        · simp [Amode.toMem, Amode.map, Base.map, hi]
        · simp [Amode.regs, hf]
        · simp [Amode.regs, hl]

theorem Placer.bound_spec {p p' : Placer} {b : Bound α} {f : α → VReg} {arg : Option X86.Arg}
    (h : p.bound (b.map f) = some (arg, p')) :
    ∃ bR : Bound (α × GPR), bR.map Prod.fst = b ∧ bR.Assigned ∧
      (bR.map Prod.snd).machine some some = arg ∧ (bR.isSlot = true → arg.isSome = true) ∧
      p.free = bR.taken ++ p'.free ∧
      p'.loads = (bR.uses.map fun q => (q.2, f q.1)).reverse ++ p.loads ∧
      p'.reads = (bR.defs.map fun q => (f q.1, q.2)).reverse ++ p.reads := by
  cases b with
  | input s a =>
    cases a with
    | r a =>
      cases hu : p.use (f a) with
      | none => simp [Bound.map, XArg.map, Placer.bound, hu] at h
      | some q =>
        obtain ⟨r, p₁⟩ := q
        obtain ⟨hf, hl, hr⟩ := use_spec hu
        simp [Bound.map, XArg.map, Placer.bound, hu] at h
        obtain ⟨rfl, rfl⟩ := h
        refine ⟨.input s (.r (a, r)), rfl, trivial, rfl, fun _ => rfl, ?_, ?_, hr⟩
        · simp [Bound.taken, XArg.regs, hf]
        · simp [Bound.uses, XArg.regs, hl]
    | m am =>
      cases ha : p.amode (am.map f) with
      | none => simp [Bound.map, XArg.map, Placer.bound, ha] at h
      | some q =>
        obtain ⟨m, p₁⟩ := q
        obtain ⟨amR, hmap, hmem, hf, hl, hr⟩ := amode_spec ha
        simp [Bound.map, XArg.map, Placer.bound, ha] at h
        obtain ⟨rfl, rfl⟩ := h
        refine ⟨.input s (.m amR), by simp [Bound.map, XArg.map, hmap], trivial, ?_, fun _ => rfl,
          ?_, ?_, hr⟩
        · simp [Bound.map, XArg.map, Bound.machine, hmem]
        · simp [Bound.taken, XArg.regs, hf]
        · simp [Bound.uses, XArg.regs, hl]
    | i w =>
      simp [Bound.map, XArg.map, Placer.bound, pure] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨.input s (.i w), rfl, trivial, rfl, fun _ => rfl, by simp [Bound.taken, XArg.regs],
        by simp [Bound.uses, XArg.regs], by simp [Bound.defs]⟩
  | output s x =>
    cases ht : p.take with
    | none => simp [Bound.map, Placer.bound, ht] at h
    | some q =>
      obtain ⟨r, p₁⟩ := q
      obtain ⟨hf, hl, hr⟩ := take_spec ht
      simp [Bound.map, Placer.bound, ht] at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨.output s (x, r), rfl, trivial, rfl, fun _ => rfl, ?_, ?_, ?_⟩
      · simp [Bound.taken, hf]
      · simp [Bound.uses, hl]
      · simp [Bound.defs, hr]
  | tied s a x =>
    cases hu : p.use (f a) with
    | none => simp [Bound.map, Placer.bound, hu] at h
    | some q =>
      obtain ⟨r, p₁⟩ := q
      obtain ⟨hf, hl, hr⟩ := use_spec hu
      simp [Bound.map, Placer.bound, hu] at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨.tied s (a, r) (x, r), rfl, rfl, rfl, fun _ => rfl, ?_, ?_, ?_⟩
      · simp [Bound.taken, hf]
      · simp [Bound.uses, hl]
      · simp [Bound.defs, hr]
  | memory s am =>
    cases ha : p.amode (am.map f) with
    | none => simp [Bound.map, Placer.bound, ha] at h
    | some q =>
      obtain ⟨m, p₁⟩ := q
      obtain ⟨amR, hmap, hmem, hf, hl, hr⟩ := amode_spec ha
      simp [Bound.map, Placer.bound, ha] at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨.memory s amR, by simp [Bound.map, hmap], trivial, ?_, fun _ => rfl, ?_, ?_, hr⟩
      · simp [Bound.map, Bound.machine, hmem]
      · simp [Bound.taken, hf]
      · simp [Bound.uses, hl]
  | fixedUse i a =>
    simp [Bound.map, Placer.bound, pure] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨.fixedUse i (a, i.reg), rfl, rfl, rfl, fun h => by simp [Bound.isSlot] at h,
      by simp [Bound.taken], by simp [Bound.uses], by simp [Bound.defs]⟩
  | fixedDef i x =>
    simp [Bound.map, Placer.bound, pure] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨.fixedDef i (x, i.reg), rfl, rfl, rfl, fun h => by simp [Bound.isSlot] at h,
      by simp [Bound.taken], by simp [Bound.uses], by simp [Bound.defs]⟩
  | fixedTied i a x =>
    simp [Bound.map, Placer.bound, pure] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨.fixedTied i (a, i.reg) (x, i.reg), rfl, ⟨rfl, rfl⟩, rfl,
      fun h => by simp [Bound.isSlot] at h, by simp [Bound.taken], by simp [Bound.uses],
      by simp [Bound.defs]⟩

/-- The Xv placer is a register assignment: its machine arguments are the
assignment's, it hands out its free registers in order, loads each use and
reads back each definition. -/
theorem Placer.bounds_spec {f : α → VReg} :
    ∀ {bs : List (Bound α)} {p p' : Placer} {margs : List X86.Arg},
      p.bounds (bs.map (Bound.map f)) = some (margs, p') →
      ∃ bR : List (Bound (α × GPR)), bR.map (Bound.map Prod.fst) = bs ∧ (∀ b ∈ bR, b.Assigned) ∧
        slotArgs some some (bR.map (Bound.map Prod.snd)) = some margs ∧
        p.free = bR.flatMap Bound.taken ++ p'.free ∧
        p'.loads = ((bR.flatMap Bound.uses).map fun q => (q.2, f q.1)).reverse ++ p.loads ∧
        p'.reads = ((bR.flatMap Bound.defs).map fun q => (f q.1, q.2)).reverse ++ p.reads
  | [], p, p', margs, h => by
      simp [Placer.bounds] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨[], rfl, by simp, by simp [slotArgs], by simp, by simp, by simp⟩
  | b :: bs, p, p', margs, h => by
      simp only [List.map_cons, Placer.bounds, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨⟨arg, p₁⟩, hb, ⟨args, p₂⟩, hbs, he⟩ := h
      simp only [pure, Option.some.injEq, Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      obtain ⟨bR, hmap, hass, hmach, hslot, hf, hl, hr⟩ := bound_spec hb
      obtain ⟨bRs, hmaps, hasss, hargs, hfs, hls, hrs⟩ := bounds_spec hbs
      refine ⟨bR :: bRs, by simp [hmap, hmaps], ?_, ?_, ?_, ?_, ?_⟩
      · intro b' hb'
        rcases List.mem_cons.1 hb' with rfl | hb'
        · exact hass
        · exact hasss b' hb'
      · rw [List.map_cons, slotArgs_cons, Bound.isSlot_map]
        by_cases hs : bR.isSlot = true
        · have := hslot hs
          cases harg : arg with
          | none => simp [harg] at this
          | some a =>
            rw [harg] at hmach
            simp [hs, hmach, hargs]
        · have : arg = none := by
            rw [← hmach]
            cases bR <;> simp_all [Bound.isSlot, Bound.map, Bound.machine]
          simp [hs, hargs, this]
      · rw [hf, hfs]; simp
      · rw [hls, hl]; simp
      · rw [hrs, hr]; simp

end Compilatrix.Xv

