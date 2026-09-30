import Compilatrix.Xv.Validate.Proof.Place
import Compilatrix.Xv.Validate.Proof.Exec

/-!
# Two assignments of one row

Two register assignments of the same bound operands (payloads equal, as
`Bound (α × GPR)`) give corresponding machine arguments when each use's
register holds the payload's value in its core (`slotsCorr_of_assign`), and
the definitions' registers end equal when the row's written registers do
(`written_defs`, `implicit_defs`). Xv's placement and Xl's locations are the
two assignments the validator soundness proof compares.

The shape facts come from binding: `bindRow` fills the row's slots in order
with slot bounds, each form in the role it serves (`Bound.RoleOk`), then the
implicit registers in order (`bindRow_shape`).
-/

namespace Compilatrix.Xv

open Compilatrix.Lir (VReg Word)
open X86 (GPR)
open Compilatrix.Xv.Validate (SlotCorr SlotsCorr WrittenCorr Wide)

variable {α β : Type}

/-! ## Shapes -/

/-- The slot a slot bound fills. -/
def Bound.slot? : Bound α → Option X86.Slot
  | .input s _ | .output s _ | .tied s _ _ | .memory s _ => some s
  | _ => none

/-- The implicit register an implicit bound fills. -/
def Bound.implicit? : Bound α → Option X86.Implicit
  | .fixedUse i _ | .fixedDef i _ | .fixedTied i _ _ => some i
  | _ => none

/-- Each form in the role binding gives it. -/
def Bound.RoleOk : Bound α → Prop
  | .output s _ => s.role = .write
  | .tied s _ _ => s.role = .readWrite
  | .fixedUse i _ => i.role.reads = true ∧ i.role.writes = false
  | .fixedDef i _ => i.role.reads = false ∧ i.role.writes = true
  | .fixedTied i _ _ => i.role.reads = true ∧ i.role.writes = true
  | _ => True

@[simp] theorem Bound.slot?_map (f : α → β) (b : Bound α) : (b.map f).slot? = b.slot? := by
  cases b <;> rfl

@[simp] theorem Bound.implicit?_map (f : α → β) (b : Bound α) : (b.map f).implicit? = b.implicit? := by
  cases b <;> rfl

@[simp] theorem Bound.roleOk_map (f : α → β) (b : Bound α) : (b.map f).RoleOk ↔ b.RoleOk := by
  cases b <;> rfl

theorem bindSlots_shape :
    ∀ {slots : List X86.Slot} {defs : List α} {args : List (XArg α)}
      {bs : List (Bound α)} {defs' : List α} {args' : List (XArg α)},
      bindSlots slots defs args = some (bs, defs', args') →
      bs.map Bound.slot? = slots.map some ∧ ∀ b ∈ bs, b.RoleOk
  | [], _, _, bs, _, _, h => by
      simp [bindSlots] at h
      obtain ⟨rfl, -, -⟩ := h
      simp
  | ⟨kinds, width, role⟩ :: ss, defs, args, bs, defs', args', h => by
      have cons_eq : ∀ (b : Bound α) (defs₁ : List α) (args₁ : List (XArg α)),
          ((fun r => (b :: r.1, r.2)) <$> bindSlots ss defs₁ args₁) = some (bs, defs', args') →
          b.slot? = some ⟨kinds, width, role⟩ → b.RoleOk →
          bs.map Bound.slot? = (⟨kinds, width, role⟩ :: ss).map some ∧ ∀ b ∈ bs, b.RoleOk := by
        intro b defs₁ args₁ h hs hr
        cases hb : bindSlots ss defs₁ args₁ with
        | none => simp [hb] at h
        | some r =>
          obtain ⟨bs₁, d, a⟩ := r
          simp only [hb, Option.map_eq_map, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl, rfl⟩ := h
          have ih := bindSlots_shape hb
          refine ⟨by simp [hs, ih.1], ?_⟩
          intro b' hb'
          rcases List.mem_cons.1 hb' with rfl | hb'
          · exact hr
          · exact ih.2 b' hb'
      cases role with
      | read | address =>
        cases args with
        | nil => simp [bindSlots] at h
        | cons a args => exact cons_eq _ _ _ h rfl trivial
      | readWrite =>
        cases args with
        | nil => simp [bindSlots] at h
        | cons a args =>
          cases a with
          | r a =>
            cases defs with
            | nil => simp [bindSlots] at h
            | cons x defs => exact cons_eq _ _ _ h rfl rfl
          | m m => exact cons_eq _ _ _ h rfl trivial
          | i w => simp [bindSlots] at h
      | write =>
        cases args with
        | nil =>
          cases defs with
          | nil => simp [bindSlots] at h
          | cons x defs => exact cons_eq _ _ _ h rfl rfl
        | cons a args =>
          cases a with
          | m m =>
            by_cases hk : kinds.contains .mem = true
            · simp only [bindSlots, hk, ↓reduceIte] at h
              exact cons_eq _ _ _ h rfl trivial
            · have hk' : X86.ArgKind.mem ∉ kinds := fun hm => hk (List.contains_iff_mem.2 hm)
              cases defs with
              | nil => simp [bindSlots, hk'] at h
              | cons x defs =>
                simp only [bindSlots, hk, Bool.false_eq_true, ↓reduceIte] at h
                exact cons_eq _ _ _ h rfl rfl
          | r a =>
            cases defs with
            | nil => simp [bindSlots] at h
            | cons x defs => exact cons_eq _ _ _ h rfl rfl
          | i w =>
            cases defs with
            | nil => simp [bindSlots] at h
            | cons x defs => exact cons_eq _ _ _ h rfl rfl

theorem bindImplicits_shape :
    ∀ {is : List X86.Implicit} {defs : List α} {args : List (XArg α)} {bs : List (Bound α)},
      bindImplicits is defs args = some bs →
      bs.map Bound.implicit? = is.map some ∧ ∀ b ∈ bs, b.RoleOk
  | [], [], [], bs, h => by simp [bindImplicits] at h; subst h; simp
  | [], _ :: _, _, _, h => by simp [bindImplicits] at h
  | [], [], _ :: _, _, h => by simp [bindImplicits] at h
  | i :: is, defs, args, bs, h => by
      have map_eq : ∀ (b : Bound α) (defs₁ : List α) (args₁ : List (XArg α)),
          ((b :: ·) <$> bindImplicits is defs₁ args₁) = some bs → b.implicit? = some i → b.RoleOk →
          bs.map Bound.implicit? = (i :: is).map some ∧ ∀ b ∈ bs, b.RoleOk := by
        intro b defs₁ args₁ h hi hr
        cases hb : bindImplicits is defs₁ args₁ with
        | none => simp [hb] at h
        | some bs₁ =>
          simp only [hb, Option.map_eq_map, Option.map_some, Option.some.injEq] at h
          subst h
          have ih := bindImplicits_shape hb
          refine ⟨by simp [hi, ih.1], ?_⟩
          intro b' hb'
          rcases List.mem_cons.1 hb' with rfl | hb'
          · exact hr
          · exact ih.2 b' hb'
      cases hr : i.role.reads <;> cases hw : i.role.writes
      · cases args <;> cases defs <;> simp [bindImplicits, hr, hw] at h
      · cases defs with
        | nil => cases args <;> simp [bindImplicits, hr, hw] at h
        | cons x defs =>
          have h' : ((Bound.fixedDef i x :: ·) <$> bindImplicits is defs args) = some bs := by
            cases args with
            | nil => simpa [bindImplicits, hr, hw] using h
            | cons a args => cases a <;> simpa [bindImplicits, hr, hw] using h
          exact map_eq _ _ _ h' rfl ⟨hr, hw⟩
      · cases args with
        | nil => simp [bindImplicits, hr, hw] at h
        | cons a args =>
          cases a with
          | r a =>
            simp only [bindImplicits, hr, hw] at h
            exact map_eq _ _ _ h rfl ⟨hr, hw⟩
          | m m => simp [bindImplicits, hr, hw] at h
          | i w => simp [bindImplicits, hr, hw] at h
      · cases args with
        | nil => simp [bindImplicits, hr, hw] at h
        | cons a args =>
          cases a with
          | r a =>
            cases defs with
            | nil => simp [bindImplicits, hr, hw] at h
            | cons x defs =>
              simp only [bindImplicits, hr, hw] at h
              exact map_eq _ _ _ h rfl ⟨hr, hw⟩
          | m m => cases defs <;> simp [bindImplicits, hr, hw] at h
          | i w => cases defs <;> simp [bindImplicits, hr, hw] at h

/-- A bound row: its slot bounds in slot order, then its implicit bounds. -/
theorem bindRow_shape {o : X86.Op} {defs : List α} {args : List (XArg α)} {bs : List (Bound α)}
    (h : bindRow o defs args = some bs) :
    ∃ bs₁ bs₂, bs = bs₁ ++ bs₂ ∧ bs₁.map Bound.slot? = (X86.desc o).slots.map some ∧
      bs₂.map Bound.implicit? = (X86.desc o).implicit.map some ∧ ∀ b ∈ bs, b.RoleOk := by
  unfold bindRow at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, pure] at h
  obtain ⟨⟨bs₁, defs', args'⟩, h₁, bs₂, h₂, he⟩ := h
  cases he
  obtain ⟨s₁, r₁⟩ := bindSlots_shape h₁
  obtain ⟨s₂, r₂⟩ := bindImplicits_shape h₂
  refine ⟨bs₁, bs₂, rfl, s₁, s₂, fun b hb => ?_⟩
  rcases List.mem_append.1 hb with hb | hb
  · exact r₁ b hb
  · exact r₂ b hb

theorem isSlot_of_slot? {b : Bound α} {s : X86.Slot} (h : b.slot? = some s) : b.isSlot = true := by
  cases b <;> simp_all [Bound.slot?, Bound.isSlot]

theorem not_isSlot_of_implicit? {b : Bound α} {i : X86.Implicit} (h : b.implicit? = some i) :
    b.isSlot = false := by
  cases b <;> simp_all [Bound.implicit?, Bound.isSlot]

theorem slotArgs_append_implicits {ρ : Type} (place addr : ρ → Option GPR) (bs₁ bs₂ : List (Bound ρ))
    (h : ∀ b ∈ bs₂, b.isSlot = false) :
    slotArgs place addr (bs₁ ++ bs₂) = slotArgs place addr bs₁ := by
  unfold slotArgs
  have : bs₂.filter Bound.isSlot = [] := List.filter_eq_nil_iff.2 (fun b hb => by simp [h b hb])
  rw [List.filter_append, this, List.append_nil]

/-! ## Addresses -/

theorem indexReg_gpr {r : GPR} {i : X86.IndexReg} (h : indexReg r = some i) : i.gpr = r := by
  cases r <;> simp [indexReg] at h <;> subst h <;> rfl

/-- The base of an assigned address, as the row reads it. -/
def Amode.baseVal (c : X86.Core) (am : Amode (α × GPR)) : Word :=
  match am.base with
  | none => 0
  | some .ctx => c.readReg .r15
  | some (.r q) => c.readReg q.2

/-- The scaled index of an assigned address. -/
def Amode.indexVal (c : X86.Core) (am : Amode (α × GPR)) : Word :=
  match am.index with
  | none => 0
  | some (q, s) => c.readReg q.2 * s.word

theorem Amode.eval_toMem {am : Amode (α × GPR)} {m : X86.MemAddr}
    (h : (am.map Prod.snd).toMem some = some m) (c : X86.Core) :
    m.eval c = am.baseVal c + am.indexVal c + X86.signExtend32 am.disp.toUInt32 := by
  rcases am with ⟨base, index, disp⟩
  rcases index with _ | ⟨q', s⟩
  · rcases base with _ | (q | _) <;> simp [Amode.toMem, Amode.map, Base.map] at h <;> subst h <;>
      simp [X86.MemAddr.eval, Amode.baseVal, Amode.indexVal]
  · cases hi : indexReg q'.2 with
    | none => rcases base with _ | (q | _) <;> simp [Amode.toMem, Amode.map, Base.map, hi] at h
    | some i =>
      rcases base with _ | (q | _) <;> simp [Amode.toMem, Amode.map, Base.map, hi] at h <;> subst h <;>
        simp [X86.MemAddr.eval, Amode.baseVal, Amode.indexVal, indexReg_gpr hi]

theorem amode_eval_corr {c₁ c₂ : X86.Core} {val : α → Word}
    (hctx : c₁.readReg .r15 = c₂.readReg .r15) {am₁ am₂ : Amode (α × GPR)} {m₁ m₂ : X86.MemAddr}
    (hsk : am₁.map Prod.fst = am₂.map Prod.fst)
    (h₁ : (am₁.map Prod.snd).toMem some = some m₁) (h₂ : (am₂.map Prod.snd).toMem some = some m₂)
    (hv₁ : ∀ q ∈ am₁.regs, c₁.readReg q.2 = val q.1) (hv₂ : ∀ q ∈ am₂.regs, c₂.readReg q.2 = val q.1) :
    m₁.eval c₁ = m₂.eval c₂ := by
  rw [Amode.eval_toMem h₁, Amode.eval_toMem h₂]
  rcases am₁ with ⟨base₁, index₁, disp₁⟩
  rcases am₂ with ⟨base₂, index₂, disp₂⟩
  simp only [Amode.map, Amode.mk.injEq] at hsk
  obtain ⟨hb, hi, rfl⟩ := hsk
  have hbase : Amode.baseVal c₁ ⟨base₁, index₁, disp₁⟩ = Amode.baseVal c₂ ⟨base₂, index₂, disp₁⟩ := by
    rcases base₁ with _ | (q₁ | _) <;> rcases base₂ with _ | (q₂ | _) <;>
      simp [Base.map] at hb <;> simp [Amode.baseVal, hctx]
    rw [hv₁ q₁ (by simp [Amode.regs]), hv₂ q₂ (by simp [Amode.regs]), hb]
  have hindex : Amode.indexVal c₁ ⟨base₁, index₁, disp₁⟩ = Amode.indexVal c₂ ⟨base₂, index₂, disp₁⟩ := by
    rcases index₁ with _ | ⟨p₁, s₁⟩ <;> rcases index₂ with _ | ⟨p₂, s₂⟩ <;> simp at hi <;>
      simp [Amode.indexVal]
    obtain ⟨hp, rfl⟩ := hi
    rw [hv₁ p₁ (by cases base₁ <;> (try rename_i b; cases b) <;> simp [Amode.regs]),
      hv₂ p₂ (by cases base₂ <;> (try rename_i b; cases b) <;> simp [Amode.regs]), hp]
  rw [hbase, hindex]

/-! ## Corresponding arguments -/

theorem Bound.map_fst_eq {b₁ b₂ : Bound (α × GPR)} (h : b₁.map Prod.fst = b₂.map Prod.fst) :
    b₁.slot? = b₂.slot? ∧ b₁.implicit? = b₂.implicit? := by
  have h1 := congrArg Bound.slot? h
  have h2 := congrArg Bound.implicit? h
  simp only [Bound.slot?_map, Bound.implicit?_map] at h1 h2
  exact ⟨h1, h2⟩

/-- Two assignments of the same slot bounds whose uses hold the same values
(and whose narrow write-only registers are zero) give corresponding machine
arguments. -/
theorem slotsCorr_of_assign {c₁ c₂ : X86.Core} {val : α → Word}
    (hctx : c₁.readReg .r15 = c₂.readReg .r15) :
    ∀ {bs₁ bs₂ : List (Bound (α × GPR))} {ss : List X86.Slot} {as₁ as₂ : List X86.Arg},
      bs₁.map (Bound.map Prod.fst) = bs₂.map (Bound.map Prod.fst) →
      bs₁.map Bound.slot? = ss.map some → (∀ b ∈ bs₁, b.RoleOk) →
      slotArgs some some (bs₁.map (Bound.map Prod.snd)) = some as₁ →
      slotArgs some some (bs₂.map (Bound.map Prod.snd)) = some as₂ →
      (∀ q ∈ bs₁.flatMap Bound.uses, c₁.readReg q.2 = val q.1) →
      (∀ q ∈ bs₂.flatMap Bound.uses, c₂.readReg q.2 = val q.1) →
      (∀ b ∈ bs₁, b.narrowOutput = true → ∀ q ∈ b.defs, c₁.readReg q.2 = 0) →
      (∀ b ∈ bs₂, b.narrowOutput = true → ∀ q ∈ b.defs, c₂.readReg q.2 = 0) →
      SlotsCorr c₁ c₂ ss as₁ as₂
  | [], bs₂, ss, as₁, as₂, hsk, hs, _, h₁, h₂, _, _, _, _ => by
      cases bs₂ with
      | cons => simp at hsk
      | nil =>
        cases ss with
        | cons => simp at hs
        | nil => simp [slotArgs] at h₁ h₂; subst h₁ h₂; trivial
  | b₁ :: bs₁, bs₂, ss, as₁, as₂, hsk, hs, hr, h₁, h₂, hv₁, hv₂, hz₁, hz₂ => by
      cases bs₂ with
      | nil => simp at hsk
      | cons b₂ bs₂ =>
      cases ss with
      | nil => simp at hs
      | cons s ss =>
      simp only [List.map_cons, List.cons.injEq] at hsk hs
      obtain ⟨hsk₀, hsk⟩ := hsk
      obtain ⟨hs₀, hs⟩ := hs
      have hslot₁ : b₁.isSlot = true := isSlot_of_slot? hs₀
      have hslot₂ : b₂.isSlot = true := isSlot_of_slot? (by rw [← (Bound.map_fst_eq hsk₀).1]; exact hs₀)
      rw [List.map_cons, slotArgs_cons, Bound.isSlot_map, hslot₁] at h₁
      rw [List.map_cons, slotArgs_cons, Bound.isSlot_map, hslot₂] at h₂
      simp only [↓reduceIte, Option.bind_eq_some_iff] at h₁ h₂
      obtain ⟨a₁, ha₁, h₁⟩ := h₁
      obtain ⟨a₂, ha₂, h₂⟩ := h₂
      cases hr₁ : slotArgs some some (bs₁.map (Bound.map Prod.snd)) with
      | none => simp [hr₁] at h₁
      | some as₁' =>
      cases hr₂ : slotArgs some some (bs₂.map (Bound.map Prod.snd)) with
      | none => simp [hr₂] at h₂
      | some as₂' =>
      simp only [hr₁, hr₂, Option.map_eq_map, Option.map_some, Option.some.injEq] at h₁ h₂
      subst h₁ h₂
      refine ⟨?_, slotsCorr_of_assign hctx hsk hs (fun b hb => hr b (List.mem_cons_of_mem _ hb)) hr₁ hr₂
        (fun q hq => hv₁ q (by simp only [List.flatMap_cons]; exact List.mem_append_right _ hq))
        (fun q hq => hv₂ q (by simp only [List.flatMap_cons]; exact List.mem_append_right _ hq))
        (fun b hb => hz₁ b (List.mem_cons_of_mem _ hb)) (fun b hb => hz₂ b (List.mem_cons_of_mem _ hb))⟩
      have hu₁ : ∀ q ∈ b₁.uses, c₁.readReg q.2 = val q.1 := fun q hq =>
        hv₁ q (by simp only [List.flatMap_cons]; exact List.mem_append_left _ hq)
      have hu₂ : ∀ q ∈ b₂.uses, c₂.readReg q.2 = val q.1 := fun q hq =>
        hv₂ q (by simp only [List.flatMap_cons]; exact List.mem_append_left _ hq)
      have hr₀ := hr b₁ List.mem_cons_self
      have hz₁' := hz₁ b₁ List.mem_cons_self
      have hz₂' := hz₂ b₂ List.mem_cons_self
      cases b₁ <;> cases b₂ <;> simp only [Bound.map, reduceCtorEq, Bound.input.injEq,
        Bound.output.injEq, Bound.tied.injEq, Bound.memory.injEq] at hsk₀ <;>
        simp only [Bound.slot?, Option.some.injEq, reduceCtorEq] at hs₀ <;> subst hs₀
      case input.input s₁ x₁ s₂ x₂ =>
        obtain ⟨rfl, hx⟩ := hsk₀
        cases x₁ <;> cases x₂ <;> simp only [XArg.map, reduceCtorEq, XArg.r.injEq, XArg.m.injEq,
          XArg.i.injEq] at hx
        · rename_i q₁ q₂
          simp only [Bound.map, XArg.map, Bound.machine, Option.map_eq_map, Option.map_some,
            Option.some.injEq] at ha₁ ha₂
          subst ha₁ ha₂
          refine .inr ?_
          rw [hu₁ q₁ (by simp [Bound.uses, XArg.regs]), hu₂ q₂ (by simp [Bound.uses, XArg.regs]), hx]
        · rename_i am₁ am₂
          simp only [Bound.map, XArg.map, Bound.machine, Option.map_eq_map, Option.map_eq_some_iff] at ha₁ ha₂
          obtain ⟨m₁, hm₁, rfl⟩ := ha₁
          obtain ⟨m₂, hm₂, rfl⟩ := ha₂
          exact amode_eval_corr hctx hx hm₁ hm₂ (fun q hq => hu₁ q (by simpa [Bound.uses, XArg.regs] using hq))
            (fun q hq => hu₂ q (by simpa [Bound.uses, XArg.regs] using hq))
        · subst hx
          simp only [Bound.map, XArg.map, Bound.machine, Option.some.injEq] at ha₁ ha₂
          subst ha₁ ha₂
          rfl
      case output.output s₁ q₁ s₂ q₂ =>
        obtain ⟨rfl, hq⟩ := hsk₀
        simp only [Bound.map, Bound.machine, Option.map_eq_map, Option.map_some,
          Option.some.injEq] at ha₁ ha₂
        subst ha₁ ha₂
        simp only [Bound.RoleOk] at hr₀
        by_cases hw : Wide s₁.width
        · exact .inl ⟨hr₀, hw⟩
        · have hn : (Bound.output s₁ q₁).narrowOutput = true := by
            simp only [Bound.narrowOutput]
            rcases hs : s₁.width <;> simp_all [Wide]
          have hn' : (Bound.output s₁ q₂).narrowOutput = true := hn
          refine .inr ?_
          rw [hz₁' hn q₁ (by simp [Bound.defs]), hz₂' hn' q₂ (by simp [Bound.defs])]
      case tied.tied s₁ a₁ x₁ s₂ a₂ x₂ =>
        obtain ⟨rfl, ha, -⟩ := hsk₀
        simp only [Bound.map, Bound.machine, Option.map_eq_map, Option.map_some,
          Option.some.injEq] at ha₁ ha₂
        subst ha₁ ha₂
        refine .inr ?_
        rw [hu₁ a₁ (by simp [Bound.uses]), hu₂ a₂ (by simp [Bound.uses]), ha]
      case memory.memory s₁ am₁ s₂ am₂ =>
        obtain ⟨rfl, hx⟩ := hsk₀
        simp only [Bound.map, Bound.machine, Option.map_eq_map, Option.map_eq_some_iff] at ha₁ ha₂
        obtain ⟨m₁, hm₁, rfl⟩ := ha₁
        obtain ⟨m₂, hm₂, rfl⟩ := ha₂
        exact amode_eval_corr hctx hx hm₁ hm₂ (fun q hq => hu₁ q (by simpa [Bound.uses] using hq))
          (fun q hq => hu₂ q (by simpa [Bound.uses] using hq))

/-! ## Corresponding definitions -/

/-- An assignment re-assigned by `g` on the payload. -/
def Bound.reassign (g : α → GPR) (b : Bound (α × GPR)) : Bound (α × GPR) :=
  b.map fun q => (q.1, g q.1)

theorem Bound.reassign_fst (g : α → GPR) (b : Bound (α × GPR)) :
    (b.reassign g).map Prod.fst = b.map Prod.fst := by
  simp [Bound.reassign, Bound.map_map, Function.comp_def]

theorem Bound.reassign_snd (g : α → GPR) (b : Bound (α × GPR)) :
    (b.reassign g).map Prod.snd = b.map (fun q => g q.1) := by
  simp [Bound.reassign, Bound.map_map, Function.comp_def]

/-- When the written slots of two assignments end equal, so do the
definitions of the slot bounds: each definition's register in the first
assignment against `g` of its payload in the second. -/
theorem written_defs {f₁ f₂ : X86.Core} {g : α → GPR} :
    ∀ {bs : List (Bound (α × GPR))} {ss : List X86.Slot} {as₁ as₂ : List X86.Arg},
      bs.map Bound.slot? = ss.map some → (∀ b ∈ bs, b.RoleOk) → (∀ b ∈ bs, b.Assigned) →
      (∀ b ∈ bs, (b.reassign g).Assigned) →
      slotArgs some some (bs.map (Bound.map Prod.snd)) = some as₁ →
      slotArgs some some (bs.map (Bound.map fun q => g q.1)) = some as₂ →
      WrittenCorr f₁ f₂ ss as₁ as₂ →
      ∀ q ∈ bs.flatMap Bound.defs, f₁.readReg q.2 = f₂.readReg (g q.1)
  | [], _, _, _, _, _, _, _, _, _, _, q, hq => by simp at hq
  | b :: bs, ss, as₁, as₂, hs, hr, ha₁, ha₂, h₁, h₂, hw, q, hq => by
      cases ss with
      | nil => simp at hs
      | cons s ss =>
      simp only [List.map_cons, List.cons.injEq] at hs
      obtain ⟨hs₀, hs⟩ := hs
      have hslot : b.isSlot = true := isSlot_of_slot? hs₀
      rw [List.map_cons, slotArgs_cons, Bound.isSlot_map, hslot] at h₁ h₂
      simp only [↓reduceIte, Option.bind_eq_some_iff] at h₁ h₂
      obtain ⟨a₁, hm₁, h₁⟩ := h₁
      obtain ⟨a₂, hm₂, h₂⟩ := h₂
      cases hr₁ : slotArgs some some (bs.map (Bound.map Prod.snd)) with
      | none => simp [hr₁] at h₁
      | some as₁' =>
      cases hr₂ : slotArgs some some (bs.map (Bound.map fun q => g q.1)) with
      | none => simp [hr₂] at h₂
      | some as₂' =>
      simp only [hr₁, hr₂, Option.map_eq_map, Option.map_some, Option.some.injEq] at h₁ h₂
      subst h₁ h₂
      obtain ⟨hw₀, hw⟩ := hw
      simp only [List.flatMap_cons, List.mem_append] at hq
      rcases hq with hq | hq
      · have hr₀ := hr b List.mem_cons_self
        have ha₁₀ := ha₁ b List.mem_cons_self
        have ha₂₀ := ha₂ b List.mem_cons_self
        cases b <;> simp only [Bound.slot?, Option.some.injEq, reduceCtorEq] at hs₀ <;> subst hs₀ <;>
          simp only [Bound.defs, List.mem_singleton, List.not_mem_nil] at hq
        case output s q' =>
          subst hq
          simp only [Bound.map, Bound.machine, Option.map_eq_map, Option.map_some,
            Option.some.injEq] at hm₁ hm₂
          simp only [Bound.RoleOk] at hr₀
          exact hw₀ (by simp [hr₀, X86.Role.writes]) _ _ hm₁.symm hm₂.symm
        case tied s a x =>
          subst hq
          simp only [Bound.map, Bound.machine, Option.map_eq_map, Option.map_some,
            Option.some.injEq] at hm₁ hm₂
          simp only [Bound.RoleOk] at hr₀
          simp only [Bound.Assigned, Bound.reassign, Bound.map] at ha₁₀ ha₂₀
          rw [← ha₁₀, ← ha₂₀]
          exact hw₀ (by simp [hr₀, X86.Role.writes]) _ _ hm₁.symm hm₂.symm
      · exact written_defs hs (fun b hb => hr b (List.mem_cons_of_mem _ hb))
          (fun b hb => ha₁ b (List.mem_cons_of_mem _ hb)) (fun b hb => ha₂ b (List.mem_cons_of_mem _ hb))
          hr₁ hr₂ hw q hq

/-- The implicit definitions of two assignments end equal when the row's
written implicit registers do. -/
theorem implicit_defs {f₁ f₂ : X86.Core} {g : α → GPR} {is : List X86.Implicit}
    (hw : ∀ i ∈ is, i.role.writes = true → f₁.readReg i.reg = f₂.readReg i.reg) :
    ∀ {bs : List (Bound (α × GPR))}, bs.map Bound.implicit? = is.map some → (∀ b ∈ bs, b.RoleOk) →
      (∀ b ∈ bs, b.Assigned) → (∀ b ∈ bs, (b.reassign g).Assigned) →
      ∀ q ∈ bs.flatMap Bound.defs, f₁.readReg q.2 = f₂.readReg (g q.1) := by
  intro bs hi hr ha₁ ha₂ q hq
  simp only [List.mem_flatMap] at hq
  obtain ⟨b, hb, hq⟩ := hq
  have hbi : ∃ i ∈ is, b.implicit? = some i := by
    have : b.implicit? ∈ is.map some := hi ▸ List.mem_map_of_mem hb
    simp only [List.mem_map] at this
    obtain ⟨i, hi, e⟩ := this
    exact ⟨i, hi, e.symm⟩
  obtain ⟨i, hi', hbi⟩ := hbi
  have hr₀ := hr b hb
  have ha₁₀ := ha₁ b hb
  have ha₂₀ := ha₂ b hb
  cases b with
  | fixedUse i' a => simp [Bound.defs] at hq
  | fixedDef i' x =>
    simp only [Bound.implicit?, Option.some.injEq] at hbi
    subst hbi
    simp only [Bound.defs, List.mem_singleton] at hq
    subst hq
    simp only [Bound.RoleOk, Bound.Assigned, Bound.reassign, Bound.map] at hr₀ ha₁₀ ha₂₀
    rw [ha₁₀, ha₂₀]; exact hw _ hi' hr₀.2
  | fixedTied i' a x =>
    simp only [Bound.implicit?, Option.some.injEq] at hbi
    subst hbi
    simp only [Bound.defs, List.mem_singleton] at hq
    subst hq
    simp only [Bound.RoleOk, Bound.Assigned, Bound.reassign, Bound.map] at hr₀ ha₁₀ ha₂₀
    rw [ha₁₀.2, ha₂₀.2]; exact hw _ hi' hr₀.2
  | _ => simp [Bound.implicit?] at hbi

end Compilatrix.Xv

