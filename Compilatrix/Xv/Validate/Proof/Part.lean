import Compilatrix.Xv.Validate.Proof.XvRow

/-!
# One row, two assignments

`part_corr`: a row whose operands are assigned twice (Xv's placement, and
Xl's locations as re-assigned by `g`), run on two cores where each use's
register holds the operand's value, with no stack traffic and each run
writing each register at most once, succeeds on the second core whenever it
succeeds on the first, with the same flags and memory, each definition's
registers ending equal, and every register the row does not write left
alone. The registers a row writes are its definitions' (`rowWrites_eq`).
-/

namespace Compilatrix.Xv

open Compilatrix.Lir (VReg Word)
open X86 (GPR)
open Compilatrix.Xv.Validate (SlotsCorr WrittenCorr Wide slotWrites implicitWrites rowWrites
  op_exec_corr)

variable {α : Type}

/-- A part as binding builds it: slot bounds in slot order, then implicit
bounds in order, each in its role. -/
structure PartShape (ap : APart α) : Prop where
  split : ∃ bs₁ bs₂, ap.2 = bs₁ ++ bs₂ ∧ bs₁.map Bound.slot? = (X86.desc ap.1).slots.map some ∧
    bs₂.map Bound.implicit? = (X86.desc ap.1).implicit.map some
  role : ∀ b ∈ ap.2, b.RoleOk

/-- Re-assign a part by `g` on the payload. -/
def APart.reassign (g : α → GPR) (ap : APart α) : APart α := (ap.1, ap.2.map (Bound.reassign g))

theorem PartShape.reassign {ap : APart α} (h : PartShape ap) (g : α → GPR) :
    PartShape (ap.reassign g) := by
  obtain ⟨⟨bs₁, bs₂, he, hs₁, hs₂⟩, hr⟩ := h
  refine ⟨⟨bs₁.map (Bound.reassign g), bs₂.map (Bound.reassign g), by simp [APart.reassign, he], ?_, ?_⟩,
    ?_⟩
  · have : (bs₁.map (Bound.reassign g)).map Bound.slot? = bs₁.map Bound.slot? := by
      simp [List.map_map, Function.comp_def, Bound.reassign]
    exact this.trans hs₁
  · have : (bs₂.map (Bound.reassign g)).map Bound.implicit? = bs₂.map Bound.implicit? := by
      simp [List.map_map, Function.comp_def, Bound.reassign]
    exact this.trans hs₂
  · intro b hb
    simp only [APart.reassign, List.mem_map] at hb
    obtain ⟨b', hb', rfl⟩ := hb
    simpa [Bound.reassign] using hr b' hb'

@[simp] theorem Bound.defs_reassign (g : α → GPR) (b : Bound (α × GPR)) :
    (b.reassign g).defs = b.defs.map fun q => (q.1, g q.1) := by
  simp [Bound.reassign]

@[simp] theorem Bound.uses_reassign (g : α → GPR) (b : Bound (α × GPR)) :
    (b.reassign g).uses = b.uses.map fun q => (q.1, g q.1) := by
  simp [Bound.reassign]

/-! ## What a row writes -/

theorem slotWrites_eq :
    ∀ {bs : List (Bound (α × GPR))} {ss : List X86.Slot} {as : List X86.Arg},
      bs.map Bound.slot? = ss.map some → (∀ b ∈ bs, b.RoleOk) → (∀ b ∈ bs, b.Assigned) →
      slotArgs some some (bs.map (Bound.map Prod.snd)) = some as →
      slotWrites ss as = (bs.flatMap Bound.defs).map (·.2)
  | [], ss, as, hs, _, _, h => by
      cases ss with
      | cons => simp at hs
      | nil => simp [slotArgs] at h; subst h; rfl
  | b :: bs, ss, as, hs, hr, ha, h => by
      cases ss with
      | nil => simp at hs
      | cons s ss =>
      simp only [List.map_cons, List.cons.injEq] at hs
      obtain ⟨hs₀, hs⟩ := hs
      have hslot : b.isSlot = true := isSlot_of_slot? hs₀
      rw [List.map_cons, slotArgs_cons, Bound.isSlot_map, hslot] at h
      simp only [↓reduceIte, Option.bind_eq_some_iff] at h
      obtain ⟨a, hm, h⟩ := h
      cases hr' : slotArgs some some (bs.map (Bound.map Prod.snd)) with
      | none => simp [hr'] at h
      | some as' =>
      simp only [hr', Option.map_eq_map, Option.map_some, Option.some.injEq] at h
      subst h
      have ih := slotWrites_eq hs (fun b hb => hr b (List.mem_cons_of_mem _ hb))
        (fun b hb => ha b (List.mem_cons_of_mem _ hb)) hr'
      have hr₀ := hr b List.mem_cons_self
      have ha₀ := ha b List.mem_cons_self
      simp only [List.flatMap_cons, List.map_append]
      rw [← ih]
      cases b <;> simp only [Bound.slot?, Option.some.injEq, reduceCtorEq] at hs₀ <;> subst hs₀
      case input s x =>
        simp only [Bound.RoleOk] at hr₀
        cases x <;> simp [Bound.map, XArg.map, Bound.machine] at hm <;>
          (try obtain ⟨m, -, rfl⟩ := hm) <;> (try subst hm) <;> simp [slotWrites, hr₀, Bound.defs]
      case output s q =>
        simp only [Bound.RoleOk] at hr₀
        simp only [Bound.map, Bound.machine, Option.map_eq_map, Option.map_some,
          Option.some.injEq] at hm
        subst hm
        simp [slotWrites, hr₀, X86.Role.writes, Bound.defs]
      case tied s a x =>
        simp only [Bound.RoleOk] at hr₀
        simp only [Bound.Assigned] at ha₀
        simp only [Bound.map, Bound.machine, Option.map_eq_map, Option.map_some,
          Option.some.injEq] at hm
        subst hm
        simp [slotWrites, hr₀, X86.Role.writes, Bound.defs, ha₀]
      case memory s m =>
        simp only [Bound.map, Bound.machine, Option.map_eq_map, Option.map_eq_some_iff] at hm
        obtain ⟨m', -, rfl⟩ := hm
        simp [slotWrites, Bound.defs]

theorem implicitWrites_eq :
    ∀ {bs : List (Bound (α × GPR))} {is : List X86.Implicit},
      bs.map Bound.implicit? = is.map some → (∀ b ∈ bs, b.RoleOk) → (∀ b ∈ bs, b.Assigned) →
      implicitWrites is = (bs.flatMap Bound.defs).map (·.2)
  | [], is, hi, _, _ => by
      cases is with
      | cons => simp at hi
      | nil => rfl
  | b :: bs, is, hi, hr, ha => by
      cases is with
      | nil => simp at hi
      | cons i is =>
      simp only [List.map_cons, List.cons.injEq] at hi
      obtain ⟨hi₀, hi⟩ := hi
      have ih := implicitWrites_eq hi (fun b hb => hr b (List.mem_cons_of_mem _ hb))
        (fun b hb => ha b (List.mem_cons_of_mem _ hb))
      have hr₀ := hr b List.mem_cons_self
      have ha₀ := ha b List.mem_cons_self
      unfold implicitWrites at ih ⊢
      simp only [List.flatMap_cons, List.map_append, List.filter_cons]
      rw [← ih]
      cases b <;> simp only [Bound.implicit?, Option.some.injEq, reduceCtorEq] at hi₀ <;> subst hi₀ <;>
        simp only [Bound.RoleOk, Bound.Assigned] at hr₀ ha₀
      · simp [hr₀.2, Bound.defs]
      · simp [hr₀.2, Bound.defs, ha₀]
      · simp [hr₀.2, Bound.defs, ha₀.2]

/-- The registers a row writes are its definitions' registers. -/
theorem rowWrites_eq {ap : APart α} (hs : PartShape ap) (ha : ∀ b ∈ ap.2, b.Assigned)
    {args : List X86.Arg} (hargs : slotArgs some some (ap.2.map (Bound.map Prod.snd)) = some args) :
    rowWrites ap.1 args = (ap.2.flatMap Bound.defs).map (·.2) := by
  obtain ⟨⟨bs₁, bs₂, he, hs₁, hs₂⟩, hr⟩ := hs
  rw [he] at hr ha hargs ⊢
  rw [List.map_append, slotArgs_append_implicits] at hargs
  · unfold rowWrites
    rw [slotWrites_eq hs₁ (fun b hb => hr b (List.mem_append_left _ hb))
      (fun b hb => ha b (List.mem_append_left _ hb)) hargs,
      implicitWrites_eq hs₂ (fun b hb => hr b (List.mem_append_right _ hb))
      (fun b hb => ha b (List.mem_append_right _ hb))]
    simp
  · intro b hb
    simp only [List.mem_map] at hb
    obtain ⟨b', hb', rfl⟩ := hb
    have : b'.implicit? ∈ (X86.desc ap.1).implicit.map some := hs₂ ▸ List.mem_map_of_mem hb'
    simp only [List.mem_map] at this
    obtain ⟨i, -, e⟩ := this
    rw [Bound.isSlot_map]
    exact not_isSlot_of_implicit? e.symm

/-! ## One row -/

/-- Unfold one row of `execRows`-style execution. -/
theorem execRow_eq (o : X86.Op) (args : List X86.Arg) (core : X86.Core) (flags : X86.ByteEval.Flags) :
    execRow o args core flags =
      match o.exec args core flags with
      | .ok r => some r
      | .error _ => none := rfl

/-- One part, run on two cores whose operands correspond. -/
theorem part_corr {val : α → Word} {g : α → GPR} {ap : APart α} {args₁ args₂ : List X86.Arg}
    {c₁ c₂ c₁' : X86.Core} {fl fl' : X86.ByteEval.Flags}
    (hs : PartShape ap) (hstack : (X86.desc ap.1).stack = .none)
    (hwide : ∀ i ∈ (X86.desc ap.1).implicit, i.role.reads = true ∨ Wide i.width)
    (ha₁ : ∀ b ∈ ap.2, b.Assigned) (ha₂ : ∀ b ∈ ap.2, (b.reassign g).Assigned)
    (hargs₁ : slotArgs some some (ap.2.map (Bound.map Prod.snd)) = some args₁)
    (hargs₂ : slotArgs some some (ap.2.map (Bound.map fun q => g q.1)) = some args₂)
    (hmem : c₁.memory = c₂.memory) (hctx : c₁.readReg .r15 = c₂.readReg .r15)
    (hv₁ : ∀ q ∈ ap.2.flatMap Bound.uses, c₁.readReg q.2 = val q.1)
    (hv₂ : ∀ q ∈ ap.2.flatMap Bound.uses, c₂.readReg (g q.1) = val q.1)
    (hz₁ : ∀ b ∈ ap.2, b.narrowOutput = true → ∀ q ∈ b.defs, c₁.readReg q.2 = 0)
    (hz₂ : ∀ b ∈ ap.2, b.narrowOutput = true → ∀ q ∈ b.defs, c₂.readReg (g q.1) = 0)
    (hw₁ : ((ap.2.flatMap Bound.defs).map (·.2)).Nodup)
    (hw₂ : ((ap.2.flatMap Bound.defs).map fun q => g q.1).Nodup)
    (h : execRow ap.1 args₁ c₁ fl = some (c₁', fl')) :
    ∃ c₂', execRow ap.1 args₂ c₂ fl = some (c₂', fl') ∧ c₁'.memory = c₂'.memory ∧
      (∀ q ∈ ap.2.flatMap Bound.defs, c₁'.readReg q.2 = c₂'.readReg (g q.1)) ∧
      (∀ r, r ∉ (ap.2.flatMap Bound.defs).map (·.2) → c₁'.readReg r = c₁.readReg r) ∧
      (∀ r, r ∉ (ap.2.flatMap Bound.defs).map (fun q => g q.1) → c₂'.readReg r = c₂.readReg r) := by
  have hs₂ := hs.reassign g
  have ha₂' : ∀ b ∈ (ap.reassign g).2, b.Assigned := by
    intro b hb
    simp only [APart.reassign, List.mem_map] at hb
    obtain ⟨b', hb', rfl⟩ := hb
    exact ha₂ b' hb'
  have hargs₂' : slotArgs some some ((ap.reassign g).2.map (Bound.map Prod.snd)) = some args₂ := by
    simpa [APart.reassign, List.map_map, Function.comp_def, Bound.reassign_snd] using hargs₂
  have hrw₁ := rowWrites_eq hs ha₁ hargs₁
  have hrw₂ := rowWrites_eq hs₂ ha₂' hargs₂'
  have hdefs₂ : ((ap.reassign g).2.flatMap Bound.defs).map (·.2) =
      (ap.2.flatMap Bound.defs).map fun q => g q.1 := by
    simp [APart.reassign, List.flatMap_map, List.map_flatMap, Function.comp_def]
  rw [hdefs₂] at hrw₂
  obtain ⟨⟨bs₁, bs₂, he, hsl, him⟩, hr⟩ := hs
  -- the slot arguments
  have hsl₁ : slotArgs some some (bs₁.map (Bound.map Prod.snd)) = some args₁ := by
    rw [he, List.map_append, slotArgs_append_implicits] at hargs₁
    · exact hargs₁
    · intro b hb
      simp only [List.mem_map] at hb
      obtain ⟨b', hb', rfl⟩ := hb
      have : b'.implicit? ∈ (X86.desc ap.1).implicit.map some := him ▸ List.mem_map_of_mem hb'
      simp only [List.mem_map] at this
      obtain ⟨i, -, e⟩ := this
      rw [Bound.isSlot_map]; exact not_isSlot_of_implicit? e.symm
  have hsl₂ : slotArgs some some ((bs₁.map (Bound.reassign g)).map (Bound.map Prod.snd)) = some args₂ := by
    rw [he, List.map_append, slotArgs_append_implicits] at hargs₂
    · simpa [List.map_map, Function.comp_def, Bound.reassign_snd] using hargs₂
    · intro b hb
      simp only [List.mem_map] at hb
      obtain ⟨b', hb', rfl⟩ := hb
      have : b'.implicit? ∈ (X86.desc ap.1).implicit.map some := him ▸ List.mem_map_of_mem hb'
      simp only [List.mem_map] at this
      obtain ⟨i, -, e⟩ := this
      rw [Bound.isSlot_map]; exact not_isSlot_of_implicit? e.symm
  have hmem₁ : ∀ b ∈ bs₁, b ∈ ap.2 := fun b hb => he ▸ List.mem_append_left _ hb
  have hmem₂ : ∀ b ∈ bs₂, b ∈ ap.2 := fun b hb => he ▸ List.mem_append_right _ hb
  have hcorr : SlotsCorr c₁ c₂ (X86.desc ap.1).slots args₁ args₂ :=
    slotsCorr_of_assign (val := val) hctx (bs₁ := bs₁) (bs₂ := bs₁.map (Bound.reassign g))
      (by simp [List.map_map, Function.comp_def, Bound.reassign_fst])
      hsl (fun b hb => hr b (hmem₁ b hb)) hsl₁ hsl₂
      (fun q hq => hv₁ q (List.mem_flatMap.2 (by
        obtain ⟨b, hb, hq⟩ := List.mem_flatMap.1 hq; exact ⟨b, hmem₁ b hb, hq⟩)))
      (fun q hq => by
        obtain ⟨b, hb, hq⟩ := List.mem_flatMap.1 hq
        simp only [List.mem_map] at hb
        obtain ⟨b', hb', rfl⟩ := hb
        rw [Bound.uses_reassign, List.mem_map] at hq
        obtain ⟨q', hq', rfl⟩ := hq
        exact hv₂ q' (List.mem_flatMap.2 ⟨b', hmem₁ b' hb', hq'⟩))
      (fun b hb => hz₁ b (hmem₁ b hb))
      (fun b hb hn q hq => by
        simp only [List.mem_map] at hb
        obtain ⟨b', hb', rfl⟩ := hb
        rw [Bound.defs_reassign, List.mem_map] at hq
        obtain ⟨q', hq', rfl⟩ := hq
        exact hz₂ b' (hmem₁ b' hb') (by simpa [Bound.reassign] using hn) q' hq')
  -- implicit registers
  have himp : ∀ i ∈ (X86.desc ap.1).implicit,
      (i.role.reads = true ∨ (i.role.writes = true ∧ ¬ Wide i.width)) →
      c₁.readReg i.reg = c₂.readReg i.reg := by
    intro i hi hcond
    have : some i ∈ bs₂.map Bound.implicit? := him ▸ List.mem_map_of_mem hi
    simp only [List.mem_map] at this
    obtain ⟨b, hb, e⟩ := this
    have hr₀ := hr b (hmem₂ b hb)
    have ha₀ := ha₁ b (hmem₂ b hb)
    have ha₀' := ha₂ b (hmem₂ b hb)
    cases b <;> simp only [Bound.implicit?, Option.some.injEq, reduceCtorEq] at e <;> subst e <;>
      simp only [Bound.RoleOk, Bound.Assigned, Bound.reassign, Bound.map] at hr₀ ha₀ ha₀'
    case fixedUse a =>
      have e₁ : c₁.readReg a.2 = val a.1 := hv₁ a (List.mem_flatMap.2 ⟨_, hmem₂ _ hb, by simp [Bound.uses]⟩)
      have e₂ : c₂.readReg (g a.1) = val a.1 :=
        hv₂ a (List.mem_flatMap.2 ⟨_, hmem₂ _ hb, by simp [Bound.uses]⟩)
      rw [ha₀] at e₁
      rw [ha₀'] at e₂
      rw [e₁, e₂]
    case fixedDef x =>
      rcases hcond with hc | ⟨-, hc⟩
      · rw [hr₀.1] at hc; cases hc
      · rcases hwide _ hi with hw | hw
        · rw [hr₀.1] at hw; cases hw
        · exact absurd hw hc
    case fixedTied a x =>
      have e₁ : c₁.readReg a.2 = val a.1 := hv₁ a (List.mem_flatMap.2 ⟨_, hmem₂ _ hb, by simp [Bound.uses]⟩)
      have e₂ : c₂.readReg (g a.1) = val a.1 :=
        hv₂ a (List.mem_flatMap.2 ⟨_, hmem₂ _ hb, by simp [Bound.uses]⟩)
      rw [ha₀.1] at e₁
      rw [ha₀'.1] at e₂
      rw [e₁, e₂]
  -- run
  simp only [execRow_eq] at h ⊢
  cases hx : ap.1.exec args₁ c₁ fl with
  | error e => simp [hx] at h
  | ok r =>
    simp only [hx, Option.some.injEq] at h
    subst h
    obtain ⟨c₂', hx₂, hm', hwc, himpw, hfr₁, hfr₂⟩ := op_exec_corr hstack hmem hcorr himp
      (hrw₁ ▸ hw₁) (hrw₂ ▸ hw₂) hx
    refine ⟨c₂', by rw [hx₂], hm', ?_, fun r hr => hfr₁ r (hrw₁ ▸ hr), fun r hr => hfr₂ r (hrw₂ ▸ hr)⟩
    intro q hq
    rw [he, List.flatMap_append, List.mem_append] at hq
    rcases hq with hq | hq
    · exact written_defs hsl (fun b hb => hr b (hmem₁ b hb)) (fun b hb => ha₁ b (hmem₁ b hb))
        (fun b hb => ha₂ b (hmem₁ b hb)) hsl₁
        (by simpa [List.map_map, Function.comp_def, Bound.reassign_snd] using hsl₂) hwc q hq
    · exact implicit_defs himpw him (fun b hb => hr b (hmem₂ b hb)) (fun b hb => ha₁ b (hmem₂ b hb))
        (fun b hb => ha₂ b (hmem₂ b hb)) q hq

end Compilatrix.Xv
