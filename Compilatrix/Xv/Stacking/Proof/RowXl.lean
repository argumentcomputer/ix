import Compilatrix.Xv.Stacking.Proof.RowRel
import Compilatrix.Xv.Stacking.Emit
import Compilatrix.Xv.Validate.Proof.RowSim
import Compilatrix.Xv.Validate.Proof.Assign

/-!
# An Xl row and its stacked instruction

Xl runs a bound row (`Xl.execBound`) on a core that lends each stack cell a
scratch register; Stacking emits the same row with each cell as its frame
operand (`FnCtx.rowArgs`). When the two runs agree on the row's locations
(`LocAgree`: a register holds the same value; a cell, addressed from the
machine's `rsp`, holds the word Xl lends), their machine arguments
correspond slot by slot (`ArgsRel`, `bounds_argsRel`), so `run_rel` applies.
-/

namespace Compilatrix.Xv.Stacking.Proof

open Compilatrix.X86
open Compilatrix.Xv.Xl (placeL xlLocs xlNamed xlCells xlFree xlTable)
open Compilatrix.Xv.Validate (Wide rowWrites implicitWrites)

/-- A location as the two runs see it: a register with the same value, or
a cell of the frame `c`, addressed from `c₂`, holding the word in the
scratch register Xl lends it. -/
def LocAgree (c : FnCtx) (LB : List (Bound Loc)) (c₁ c₂ : Core) : Loc → Prop
  | .reg r => c₁.readReg r = c₂.readReg r
  | l => ∃ m, c.cell l = .ok m ∧ Cell c₁.memory c₂.memory (m.eval c₂) ∧
      c₂.memory.read64 (m.eval c₂) = c₁.readReg (placeL LB l)

/-! ## Addresses -/

theorem indexReg_gpr {r : GPR} {i : IndexReg} (h : indexReg r = some i) : i.gpr = r := by
  cases r <;> simp [indexReg] at h <;> subst h <;> rfl

theorem Amode.toMem_congr {ρ : Type} {f g : ρ → Option GPR} (am : Amode ρ) (h : ∀ x ∈ am.regs, f x = g x) :
    am.toMem f = am.toMem g := by
  rcases am with ⟨base, index, disp⟩
  rcases base with _ | (b | _) <;> rcases index with _ | ⟨x, s⟩ <;>
    simp [Amode.toMem, Amode.regs] at h ⊢ <;> simp [h]


/-- Stacking's address of an addressing mode is Xl's. -/
theorem amode_eq {am : Amode Loc} {m₁ : MemAddr} (h₁ : am.toMem Xl.Loc.reg? = some m₁)
    (hres : ∀ r, Loc.reg r ∈ am.regs → Xl.reserved r = false) {m₂ : MemAddr} (h₂ : amode am = .ok m₂) :
    m₁ = m₂ := by
  rcases am with ⟨base, index, disp⟩
  rcases base with _ | (b | _) <;> rcases index with _ | ⟨x, s⟩ <;> (try cases b) <;> (try cases x) <;>
    simp_all [amode, Amode.toMem, Amode.regs, Xl.Loc.reg?, pure, Except.pure, throw, throwThe,
      MonadExceptOf.throw]
  all_goals
    first
    | (split at h₂ <;> simp_all)
    | skip

theorem toMem_spec {am : Amode Loc} {m : MemAddr} (h : am.toMem Xl.Loc.reg? = some m) :
    (m.base = none ∨ m.base = some .r15 ∨ ∃ r, m.base = some r ∧ Loc.reg r ∈ am.regs) ∧
    (m.index = none ∨ ∃ i, m.index = some i ∧ Loc.reg i.gpr ∈ am.regs) := by
  rcases am with ⟨base, index, disp⟩
  rcases base with _ | (b | _) <;> rcases index with _ | ⟨x, s⟩ <;> (try cases b) <;> (try cases x) <;>
    simp [Amode.toMem, Amode.regs, Xl.Loc.reg?, Option.bind_eq_some_iff] at h ⊢
  all_goals
    first
    | (subst h; simp)
    | (obtain ⟨i, hi, rfl⟩ := h; simp [indexReg_gpr hi])
    | (obtain ⟨i, hi, rfl⟩ := h; exact ⟨by simp, .inr ⟨i, rfl, by simp [indexReg_gpr hi]⟩⟩)
    | skip

/-- An address both runs compute from the same registers. -/
theorem toMem_eval {am : Amode Loc} {m : MemAddr} (h : am.toMem Xl.Loc.reg? = some m) {c₁ c₂ : Core}
    (hregs : ∀ r, Loc.reg r ∈ am.regs → c₁.readReg r = c₂.readReg r) (h15 : c₁.readReg .r15 = c₂.readReg .r15) :
    m.eval c₁ = m.eval c₂ := by
  obtain ⟨hb, hi⟩ := toMem_spec h
  unfold MemAddr.eval
  rcases hb with hb | hb | ⟨r, hb, hr⟩ <;> rcases hi with hi | ⟨i, hi, hr'⟩ <;> simp only [hb, hi]
  · rw [hregs _ hr']
  · rw [h15]
  · rw [h15, hregs _ hr']
  · rw [hregs _ hr]
  · rw [hregs _ hr, hregs _ hr']

/-! ## Operands -/

theorem arg_reg {c : FnCtx} {r : GPR} {a : Arg} (h : c.arg (.reg r) = .ok a) :
    Xl.reserved r = false ∧ a = .reg r := by
  simp only [FnCtx.arg, gpr] at h
  cases hr : Xl.reserved r <;> simp [hr, Functor.map, Except.map, throw, throwThe, MonadExceptOf.throw, pure, Except.pure] at h
  · exact ⟨rfl, h.symm⟩

theorem arg_cell {c : FnCtx} {l : Loc} (hl : l.isCell = true) {a : Arg} (h : c.arg l = .ok a) :
    ∃ m, c.cell l = .ok m ∧ a = .mem m := by
  cases l with
  | reg r => simp [Loc.isCell] at hl
  | _ =>
    simp only [FnCtx.arg, Functor.map, Except.map] at h
    split at h
    · simp at h
    · rename_i m hm
      simp only [Except.ok.injEq] at h
      exact ⟨m, hm, h.symm⟩

/-- A slot bound's operands in the two runs correspond. -/
theorem bound_argRel {c : FnCtx} {LB : List (Bound Loc)} (hcells : (xlCells LB).length ≤ (xlFree LB).length)
    {c₁ c₂ : Core} {b : Bound Loc} (hb : b ∈ LB) (hrole : b.RoleOk) {s : Slot} (hs : b.slot? = some s)
    (hplace : Xl.Bound.placeable b = true)
    (huse : ∀ u ∈ b.uses, LocAgree c LB c₁ c₂ u)
    (hres : ∀ u ∈ b.uses, ∀ r, u = .reg r → Xl.reserved r = false)
    (hdef : ∀ d ∈ b.defs, d.isCell = true → ∀ m, c.cell d = .ok m → Cell c₁.memory c₂.memory (m.eval c₂))
    (hnarrow : b.narrowOutput = true → ∀ d ∈ b.defs, ∀ r, d = .reg r → c₁.readReg r = c₂.readReg r)
    (h15 : c₁.readReg .r15 = c₂.readReg .r15)
    {a₁ a₂ : Arg} (h₁ : b.machine (Xl.placeIn (xlTable LB)) Xl.Loc.reg? = some a₁) (h₂ : c.slotArg b = .ok a₂) :
    ArgRel c₁ c₂ s a₁ a₂ := by
  have hloc : ∀ l ∈ b.uses ++ b.defs, Xl.placeIn (xlTable LB) l = some (placeL LB l) := fun l hl =>
    Xl.placeIn_locs hcells (List.mem_flatMap.2 ⟨b, hb, Xl.Bound.mem_locs.2 hl⟩)
  cases b with
  | input s' a =>
    simp only [Bound.slot?, Option.some.injEq] at hs
    subst hs
    simp only [Bound.RoleOk] at hrole
    cases a with
    | r l =>
      have hpl := hloc l (by simp [Bound.uses, XArg.regs])
      simp only [Bound.machine, hpl, Option.map_eq_map, Option.map_some, Option.some.injEq,
        Functor.map] at h₁
      subst h₁
      simp only [FnCtx.slotArg] at h₂
      split at h₂
      · simp [throw, throwThe, MonadExceptOf.throw] at h₂
      rename_i hna
      have hu := huse l (by simp [Bound.uses, XArg.regs])
      have hread : s'.role = .read := by
        cases hr : s'.role <;> simp_all [Role.writes]
      cases l with
      | reg r =>
        obtain ⟨-, rfl⟩ := arg_reg h₂
        exact ⟨rfl, .inl hu⟩
      | _ =>
        obtain ⟨m', hm', rfl⟩ := arg_cell rfl h₂
        obtain ⟨m, hm, hc, hv⟩ := hu
        rw [hm] at hm'
        cases hm'
        exact ⟨by simp_all, .inl hread, hc, .inr hv⟩
    | m am =>
      simp only [Bound.machine, Option.map_eq_map, Functor.map, Option.map_eq_some_iff] at h₁
      obtain ⟨m₁, hm₁, rfl⟩ := h₁
      simp only [FnCtx.slotArg, Functor.map, Except.map] at h₂
      split at h₂
      · simp at h₂
      rename_i m₂ hm₂
      simp only [Except.ok.injEq] at h₂
      subst h₂
      have hregs : ∀ r, Loc.reg r ∈ am.regs → Xl.reserved r = false := fun r hr =>
        hres _ (by simpa [Bound.uses, XArg.regs] using hr) r rfl
      obtain rfl := amode_eq hm₁ hregs hm₂
      show m₁.eval c₁ = m₁.eval c₂
      have hr : ∀ r, Loc.reg r ∈ am.regs → c₁.readReg r = c₂.readReg r := fun r hr =>
        huse (.reg r) (by simpa [Bound.uses, XArg.regs] using hr)
      exact toMem_eval hm₁ hr h15
    | i w =>
      simp only [Bound.machine, Option.some.injEq] at h₁
      subst h₁
      simp only [FnCtx.slotArg, pure, Except.pure, Except.ok.injEq] at h₂
      subst h₂
      rfl
  | output s' l =>
    simp only [Bound.slot?, Option.some.injEq] at hs
    subst hs
    simp only [Bound.RoleOk] at hrole
    have hpl := hloc l (by simp [Bound.defs])
    simp only [Bound.machine, hpl, Option.map_eq_map, Option.map_some, Option.some.injEq,
      Functor.map] at h₁
    subst h₁
    simp only [FnCtx.slotArg] at h₂
    cases l with
    | reg r =>
      obtain ⟨-, rfl⟩ := arg_reg h₂
      refine ⟨rfl, ?_⟩
      by_cases hn : (Bound.output s' (Loc.reg r)).narrowOutput = true
      · exact .inl (hnarrow hn _ (by simp [Bound.defs]) r rfl)
      · refine .inr ⟨hrole, ?_⟩
        simp only [Bound.narrowOutput, Bool.or_eq_true, beq_iff_eq, not_or] at hn
        unfold Wide
        cases hw : s'.width <;> simp_all
    | _ =>
      obtain ⟨m, hm, rfl⟩ := arg_cell rfl h₂
      have hc := hdef _ (by simp [Bound.defs]) rfl m hm
      simp only [Xl.Bound.placeable, Loc.isCell, Bool.not_true, Bool.false_or, Bool.and_eq_true,
        beq_iff_eq] at hplace
      exact ⟨by simp [hrole], .inr hplace.2, hc, .inl hrole⟩
  | tied s' a x =>
    simp only [Bound.slot?, Option.some.injEq] at hs
    subst hs
    simp only [Bound.RoleOk] at hrole
    have hpl := hloc a (by simp [Bound.uses])
    simp only [Bound.machine, hpl, Option.map_eq_map, Option.map_some, Option.some.injEq,
      Functor.map] at h₁
    subst h₁
    simp only [FnCtx.slotArg] at h₂
    have hu := huse a (by simp [Bound.uses])
    cases a with
    | reg r =>
      obtain ⟨-, rfl⟩ := arg_reg h₂
      exact ⟨rfl, .inl hu⟩
    | _ =>
      obtain ⟨m, hm, rfl⟩ := arg_cell rfl h₂
      obtain ⟨m', hm', hc, hv⟩ := hu
      rw [hm] at hm'
      cases hm'
      simp only [Xl.Bound.placeable, Loc.isCell, Bool.not_true, Bool.false_or, Bool.and_eq_true,
        beq_iff_eq] at hplace
      exact ⟨by simp [hrole], .inr hplace.2.2, hc, .inr hv⟩
  | memory s' am =>
    simp only [Bound.slot?, Option.some.injEq] at hs
    subst hs
    simp only [Bound.machine, Option.map_eq_map, Functor.map, Option.map_eq_some_iff] at h₁
    obtain ⟨m₁, hm₁, rfl⟩ := h₁
    simp only [FnCtx.slotArg, Functor.map, Except.map] at h₂
    split at h₂
    · simp at h₂
    rename_i m₂ hm₂
    simp only [Except.ok.injEq] at h₂
    subst h₂
    have hregs : ∀ r, Loc.reg r ∈ am.regs → Xl.reserved r = false := fun r hr =>
      hres _ (by simpa [Bound.uses] using hr) r rfl
    obtain rfl := amode_eq hm₁ hregs hm₂
    show m₁.eval c₁ = m₁.eval c₂
    have hr : ∀ r, Loc.reg r ∈ am.regs → c₁.readReg r = c₂.readReg r := fun r hr =>
      huse (.reg r) (by simpa [Bound.uses] using hr)
    exact toMem_eval hm₁ hr h15
  | fixedUse _ _ | fixedDef _ _ | fixedTied _ _ _ => simp [Bound.slot?] at hs

/-- What `bound_argRel` asks of each slot bound. -/
structure BoundOk (c : FnCtx) (LB : List (Bound Loc)) (c₁ c₂ : Core) (b : Bound Loc) : Prop where
  mem : b ∈ LB
  role : b.RoleOk
  placeable : Xl.Bound.placeable b = true
  use : ∀ u ∈ b.uses, LocAgree c LB c₁ c₂ u
  res : ∀ u ∈ b.uses, ∀ r, u = .reg r → Xl.reserved r = false
  def_ : ∀ d ∈ b.defs, d.isCell = true → ∀ m, c.cell d = .ok m → Cell c₁.memory c₂.memory (m.eval c₂)
  narrow : b.narrowOutput = true → ∀ d ∈ b.defs, ∀ r, d = .reg r → c₁.readReg r = c₂.readReg r

/-- Slot bounds give corresponding argument lists. -/
theorem bounds_argsRel {c : FnCtx} {LB : List (Bound Loc)} (hcells : (xlCells LB).length ≤ (xlFree LB).length)
    {c₁ c₂ : Core} (h15 : c₁.readReg .r15 = c₂.readReg .r15) :
    ∀ {L : List (Bound Loc)} {S : List Slot} {xs₁ xs₂ : List Arg},
      L.map Bound.slot? = S.map some → (∀ b ∈ L, BoundOk c LB c₁ c₂ b) →
      L.mapM (Bound.machine (Xl.placeIn (xlTable LB)) Xl.Loc.reg?) = some xs₁ →
      L.mapM c.slotArg = .ok xs₂ → ArgsRel c₁ c₂ S xs₁ xs₂
  | [], S, xs₁, xs₂, hS, _, h₁, h₂ => by
      cases S with
      | cons => simp at hS
      | nil =>
        simp only [List.mapM_nil, pure, Option.some.injEq] at h₁
        simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at h₂
        subst h₁ h₂
        trivial
  | b :: L, S, xs₁, xs₂, hS, hok, h₁, h₂ => by
      cases S with
      | nil => simp at hS
      | cons s S =>
      simp only [List.map_cons, List.cons.injEq] at hS
      simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h₁
      obtain ⟨a₁, ha₁, as₁, has₁, rfl⟩ := h₁
      simp only [List.mapM_cons, bind, Except.bind, pure, Except.pure] at h₂
      split at h₂
      · simp at h₂
      rename_i a₂ ha₂
      split at h₂
      · simp at h₂
      rename_i as₂ has₂
      simp only [Except.ok.injEq] at h₂
      subst h₂
      have hb := hok b List.mem_cons_self
      exact ⟨bound_argRel hcells hb.mem hb.role hS.1 hb.placeable hb.use hb.res hb.def_ hb.narrow h15 ha₁ ha₂,
        bounds_argsRel hcells h15 hS.2 (fun b' hb' => hok b' (List.mem_cons_of_mem _ hb')) has₁ has₂⟩

/-! ## Positions -/

/-- Four lists, position by position. -/
inductive Zip4 {α β γ δ : Type} (P : α → β → γ → δ → Prop) : List α → List β → List γ → List δ → Prop
  | nil : Zip4 P [] [] [] []
  | cons {a b c d as bs cs ds} : P a b c d → Zip4 P as bs cs ds → Zip4 P (a :: as) (b :: bs) (c :: cs) (d :: ds)

/-- A slot bound, its slot, and its operand in each run. -/
def Pos (c : FnCtx) (LB : List (Bound Loc)) (b : Bound Loc) (s : Slot) (a₁ a₂ : Arg) : Prop :=
  b.slot? = some s ∧ b.machine (Xl.placeIn (xlTable LB)) Xl.Loc.reg? = some a₁ ∧ c.slotArg b = .ok a₂

theorem zip4_of_mapM {c : FnCtx} {LB : List (Bound Loc)} :
    ∀ {L : List (Bound Loc)} {S : List Slot} {xs₁ xs₂ : List Arg}, L.map Bound.slot? = S.map some →
      L.mapM (Bound.machine (Xl.placeIn (xlTable LB)) Xl.Loc.reg?) = some xs₁ →
      L.mapM c.slotArg = .ok xs₂ → Zip4 (Pos c LB) L S xs₁ xs₂
  | [], S, xs₁, xs₂, hS, h₁, h₂ => by
      cases S with
      | cons => simp at hS
      | nil =>
        simp only [List.mapM_nil, pure, Option.some.injEq] at h₁
        simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at h₂
        subst h₁ h₂
        exact .nil
  | b :: L, S, xs₁, xs₂, hS, h₁, h₂ => by
      cases S with
      | nil => simp at hS
      | cons s S =>
      simp only [List.map_cons, List.cons.injEq] at hS
      simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h₁
      obtain ⟨a₁, ha₁, as₁, has₁, rfl⟩ := h₁
      simp only [List.mapM_cons, bind, Except.bind, pure, Except.pure] at h₂
      split at h₂
      · simp at h₂
      rename_i a₂ ha₂
      split at h₂
      · simp at h₂
      rename_i as₂ has₂
      simp only [Except.ok.injEq] at h₂
      subst h₂
      exact .cons ⟨hS.1, ha₁, ha₂⟩ (zip4_of_mapM hS.2 has₁ has₂)

theorem Zip4.mem {α β γ δ : Type} {P : α → β → γ → δ → Prop} {Q : α → Prop} {R : α → β → γ → δ → Prop} :
    ∀ {as bs cs ds}, Zip4 P as bs cs ds → (∀ a ∈ as, Q a) → (∀ a b c d, Q a → P a b c d → R a b c d) →
      Zip4 R as bs cs ds
  | _, _, _, _, .nil, _, _ => .nil
  | _, _, _, _, .cons h t, hq, hr => .cons (hr _ _ _ _ (hq _ List.mem_cons_self) h)
      (Zip4.mem t (fun a ha => hq a (List.mem_cons_of_mem _ ha)) hr)

/-- What one position can be: the same register, a cell and its scratch
register, two memory operands, or two immediates. -/
theorem pos_cases {c : FnCtx} {LB : List (Bound Loc)} (hcells : (xlCells LB).length ≤ (xlFree LB).length)
    {b : Bound Loc} (hb : b ∈ LB) (hrole : b.RoleOk) (hplace : Xl.Bound.placeable b = true)
    {s : Slot} {a₁ a₂ : Arg} (h : Pos c LB b s a₁ a₂) :
    (∃ r, a₁ = .reg r ∧ a₂ = .reg r ∧ Xl.reserved r = false ∧
        ((s.role.writes = false ∧ b.defs = []) ∨ (s.role.writes = true ∧ b.defs = [.reg r]))) ∨
    (∃ l m, l.isCell = true ∧ c.cell l = .ok m ∧ a₁ = .reg (placeL LB l) ∧ a₂ = .mem m ∧
        (l ∈ b.uses ++ b.defs ∧ (s.role ≠ .write → l ∈ b.uses) ∧ (s.role.writes = true → s.width = .w64)) ∧
        ((s.role.writes = false ∧ b.defs = []) ∨ (s.role.writes = true ∧ b.defs = [l]))) ∨
    (∃ m₁ m₂, a₁ = .mem m₁ ∧ a₂ = .mem m₂ ∧ b.defs = []) ∨
    (∃ v, a₁ = .imm v ∧ a₂ = .imm v ∧ b.defs = []) := by
  obtain ⟨hs, h₁, h₂⟩ := h
  have hloc : ∀ l ∈ b.uses ++ b.defs, Xl.placeIn (xlTable LB) l = some (placeL LB l) := fun l hl =>
    Xl.placeIn_locs hcells (List.mem_flatMap.2 ⟨b, hb, Xl.Bound.mem_locs.2 hl⟩)
  cases b with
  | input s' a =>
    simp only [Bound.slot?, Option.some.injEq] at hs
    subst hs
    simp only [Bound.RoleOk] at hrole
    cases a with
    | r l =>
      have hpl := hloc l (by simp [Bound.uses, XArg.regs])
      simp only [Bound.machine, hpl, Option.map_eq_map, Option.map_some, Option.some.injEq,
        Functor.map] at h₁
      subst h₁
      simp only [FnCtx.slotArg] at h₂
      split at h₂
      · simp [throw, throwThe, MonadExceptOf.throw] at h₂
      cases l with
      | reg r =>
        obtain ⟨hr, rfl⟩ := arg_reg h₂
        exact .inl ⟨r, rfl, rfl, hr, .inl ⟨hrole, rfl⟩⟩
      | _ =>
        obtain ⟨m, hm, rfl⟩ := arg_cell rfl h₂
        exact .inr (.inl ⟨_, m, rfl, hm, rfl, rfl, ⟨by simp [Bound.uses, XArg.regs], fun _ => by simp [Bound.uses, XArg.regs], fun h => by rw [hrole] at h; cases h⟩, .inl ⟨hrole, rfl⟩⟩)
    | m am =>
      simp only [Bound.machine, Option.map_eq_map, Functor.map, Option.map_eq_some_iff] at h₁
      obtain ⟨m₁, -, rfl⟩ := h₁
      simp only [FnCtx.slotArg, Functor.map, Except.map] at h₂
      split at h₂
      · simp at h₂
      rename_i m₂ _
      simp only [Except.ok.injEq] at h₂
      exact .inr (.inr (.inl ⟨m₁, m₂, rfl, h₂.symm, rfl⟩))
    | i w =>
      simp only [Bound.machine, Option.some.injEq] at h₁
      simp only [FnCtx.slotArg, pure, Except.pure, Except.ok.injEq] at h₂
      exact .inr (.inr (.inr ⟨w, h₁.symm, h₂.symm, rfl⟩))
  | output s' l =>
    simp only [Bound.slot?, Option.some.injEq] at hs
    subst hs
    simp only [Bound.RoleOk] at hrole
    have hw : s'.role.writes = true := by rw [hrole]; rfl
    have hpl := hloc l (by simp [Bound.defs])
    simp only [Bound.machine, hpl, Option.map_eq_map, Option.map_some, Option.some.injEq,
      Functor.map] at h₁
    subst h₁
    simp only [FnCtx.slotArg] at h₂
    cases l with
    | reg r =>
      obtain ⟨hr, rfl⟩ := arg_reg h₂
      exact .inl ⟨r, rfl, rfl, hr, .inr ⟨hw, rfl⟩⟩
    | _ =>
      obtain ⟨m, hm, rfl⟩ := arg_cell rfl h₂
      exact .inr (.inl ⟨_, m, rfl, hm, rfl, rfl, ⟨by simp [Bound.defs], fun h => absurd hrole h, fun _ => by simp [Xl.Bound.placeable, Loc.isCell] at hplace; exact hplace.2⟩, .inr ⟨hw, rfl⟩⟩)
  | tied s' a x =>
    simp only [Bound.slot?, Option.some.injEq] at hs
    subst hs
    simp only [Bound.RoleOk] at hrole
    have hw : s'.role.writes = true := by rw [hrole]; rfl
    simp only [Xl.Bound.placeable, Bool.and_eq_true, beq_iff_eq] at hplace
    obtain ⟨rfl, hplace⟩ := hplace
    have hpl := hloc a (by simp [Bound.uses])
    simp only [Bound.machine, hpl, Option.map_eq_map, Option.map_some, Option.some.injEq,
      Functor.map] at h₁
    subst h₁
    simp only [FnCtx.slotArg] at h₂
    cases a with
    | reg r =>
      obtain ⟨hr, rfl⟩ := arg_reg h₂
      exact .inl ⟨r, rfl, rfl, hr, .inr ⟨hw, rfl⟩⟩
    | _ =>
      obtain ⟨m, hm, rfl⟩ := arg_cell rfl h₂
      exact .inr (.inl ⟨_, m, rfl, hm, rfl, rfl, ⟨by simp [Bound.uses], fun _ => by simp [Bound.uses], fun _ => by simp [Loc.isCell] at hplace; exact hplace.2⟩, .inr ⟨hw, rfl⟩⟩)
  | memory s' am =>
    simp only [Bound.machine, Option.map_eq_map, Functor.map, Option.map_eq_some_iff] at h₁
    obtain ⟨m₁, -, rfl⟩ := h₁
    simp only [FnCtx.slotArg, Functor.map, Except.map] at h₂
    split at h₂
    · simp at h₂
    rename_i m₂ _
    simp only [Except.ok.injEq] at h₂
    exact .inr (.inr (.inl ⟨m₁, m₂, rfl, h₂.symm, rfl⟩))
  | fixedUse _ _ | fixedDef _ _ | fixedTied _ _ _ => simp [Bound.slot?] at hs

/-- A position `pos_cases` describes. -/
def PosOk (c : FnCtx) (LB : List (Bound Loc)) (b : Bound Loc) (s : Slot) (a₁ a₂ : Arg) : Prop :=
  Pos c LB b s a₁ a₂ ∧ b ∈ LB ∧ b.RoleOk ∧ Xl.Bound.placeable b = true

section Zipped

variable {c : FnCtx} {LB : List (Bound Loc)} (hcells : (xlCells LB).length ≤ (xlFree LB).length)
include hcells

/-- The registers the stacked row writes: its register definitions. -/
theorem zip_slotWrites₂ :
    ∀ {L : List (Bound Loc)} {S : List Slot} {xs₁ xs₂ : List Arg}, Zip4 (PosOk c LB) L S xs₁ xs₂ →
      Validate.slotWrites S xs₂ = (L.flatMap Bound.defs).filterMap Xl.Loc.reg?
  | _, _, _, _, .nil => by simp [Validate.slotWrites]
  | _, _, _, _, .cons ⟨hp, hb, hr, hpl⟩ t => by
      have ih := zip_slotWrites₂ t
      rcases pos_cases hcells hb hr hpl hp with ⟨r, rfl, rfl, -, ⟨hw, hd⟩ | ⟨hw, hd⟩⟩ |
          ⟨l, m, hl, -, rfl, rfl, -, ⟨hw, hd⟩ | ⟨hw, hd⟩⟩ | ⟨m₁, m₂, rfl, rfl, hd⟩ | ⟨v, rfl, rfl, hd⟩
      · simp [Validate.slotWrites, hd, ih, hw]
      · simp [Validate.slotWrites, hd, ih, hw, Xl.Loc.reg?]
      · simp [Validate.slotWrites, hd, ih]
      · simp only [Validate.slotWrites, List.flatMap_cons, hd, ih, List.filterMap_append]
        cases l <;> simp [Xl.Loc.reg?, Loc.isCell] at hl ⊢
      · simp [Validate.slotWrites, hd, ih]
      · simp [Validate.slotWrites, hd, ih]

/-- The registers Xl's row writes: the places of its definitions. -/
theorem zip_slotWrites₁ :
    ∀ {L : List (Bound Loc)} {S : List Slot} {xs₁ xs₂ : List Arg}, Zip4 (PosOk c LB) L S xs₁ xs₂ →
      Validate.slotWrites S xs₁ = (L.flatMap Bound.defs).map (placeL LB)
  | _, _, _, _, .nil => by simp [Validate.slotWrites]
  | _, _, _, _, .cons ⟨hp, hb, hr, hpl⟩ t => by
      have ih := zip_slotWrites₁ t
      rcases pos_cases hcells hb hr hpl hp with ⟨r, rfl, rfl, -, ⟨hw, hd⟩ | ⟨hw, hd⟩⟩ |
          ⟨l, m, hl, -, rfl, rfl, -, ⟨hw, hd⟩ | ⟨hw, hd⟩⟩ | ⟨m₁, m₂, rfl, rfl, hd⟩ | ⟨v, rfl, rfl, hd⟩
      · simp [Validate.slotWrites, hd, ih, hw]
      · simp [Validate.slotWrites, hd, ih, hw, Xl.placeL_reg]
      · simp [Validate.slotWrites, hd, ih, hw]
      · simp [Validate.slotWrites, hd, ih, hw]
      · simp [Validate.slotWrites, hd, ih]
      · simp [Validate.slotWrites, hd, ih]

/-- A cell the stacked row writes is one of its definitions. -/
theorem zip_cellWrite {core : Core} {a : Word} {r : GPR} :
    ∀ {L : List (Bound Loc)} {S : List Slot} {xs₁ xs₂ : List Arg}, Zip4 (PosOk c LB) L S xs₁ xs₂ →
      CellWrite core a r S xs₁ xs₂ →
      ∃ l ∈ L.flatMap Bound.defs, l.isCell = true ∧ ∃ m, c.cell l = .ok m ∧ a = m.eval core ∧ r = placeL LB l
  | _, _, _, _, .nil, h => h.elim
  | _, _, _, _, .cons ⟨hp, hb, hr, hpl⟩ t, h => by
      rcases h with ⟨hw, h₁, m', h₂, ha⟩ | h
      · rcases pos_cases hcells hb hr hpl hp with ⟨r', rfl, rfl, -, -⟩ |
            ⟨l, m, hl, hm, rfl, rfl, -, ⟨hw', hd⟩ | ⟨hw', hd⟩⟩ | ⟨m₁, m₂, rfl, rfl, hd⟩ | ⟨v, rfl, rfl, hd⟩
        · cases h₂
        · rw [hw] at hw'; cases hw'
        · cases h₁; cases h₂
          exact ⟨l, by simp [hd], hl, _, hm, ha.symm, rfl⟩
        · cases h₁
        · cases h₁
      · obtain ⟨l, hl, rest⟩ := zip_cellWrite t h
        exact ⟨l, List.mem_append_right _ hl, rest⟩

/-- Each cell definition is a cell the stacked row writes. -/
theorem zip_cellWrite_of {core : Core} {l : Loc} (hl : l.isCell = true) {m : MemAddr} (hm : c.cell l = .ok m) :
    ∀ {L : List (Bound Loc)} {S : List Slot} {xs₁ xs₂ : List Arg}, Zip4 (PosOk c LB) L S xs₁ xs₂ →
      l ∈ L.flatMap Bound.defs → CellWrite core (m.eval core) (placeL LB l) S xs₁ xs₂
  | _, _, _, _, .nil, h => by simp at h
  | _, _, _, _, .cons ⟨hp, hb, hr, hpl⟩ t, h => by
      rw [List.flatMap_cons, List.mem_append] at h
      rcases h with h | h
      · rcases pos_cases hcells hb hr hpl hp with ⟨r, rfl, rfl, -, ⟨-, hd⟩ | ⟨-, hd⟩⟩ |
            ⟨l', m', hl', hm', rfl, rfl, -, ⟨-, hd⟩ | ⟨hw, hd⟩⟩ | ⟨m₁, m₂, rfl, rfl, hd⟩ | ⟨v, rfl, rfl, hd⟩ <;>
          rw [hd] at h <;> simp at h
        · subst h; simp [Loc.isCell] at hl
        · subst h
          rw [hm] at hm'
          cases hm'
          exact .inl ⟨hw, rfl, m, rfl, rfl⟩
      · exact .inr (zip_cellWrite_of hl hm t h)

/-- The stacked row writes each cell definition's eight bytes. -/
theorem zip_write_of_def {core : Core} {l : Loc} (hl : l.isCell = true) {m : MemAddr} (hm : c.cell l = .ok m) :
    ∀ {L : List (Bound Loc)} {S : List Slot} {xs₁ xs₂ : List Arg}, Zip4 (PosOk c LB) L S xs₁ xs₂ →
      l ∈ L.flatMap Bound.defs → (⟨m.eval core, 8⟩ : Access) ∈ slotWrites core S xs₂
  | _, _, _, _, .nil, h => by simp at h
  | _, _, _, _, .cons (a := b) (b := s) (d := a₂) (as := L) (bs := S) (ds := xs₂) ⟨hp, hb, hr, hpl⟩ t, h => by
      have hcons : slotWrites core (s :: S) (a₂ :: xs₂) =
          (if s.role.writes then a₂.access core s.width else []) ++ slotWrites core S xs₂ := by
        obtain ⟨kinds, width, role⟩ := s
        cases role <;> rfl
      rw [hcons, List.mem_append]
      rw [List.flatMap_cons, List.mem_append] at h
      rcases h with h | h
      · left
        rcases pos_cases hcells hb hr hpl hp with ⟨r, -, -, -, ⟨-, hd⟩ | ⟨-, hd⟩⟩ |
            ⟨l', m', hl', hm', -, rfl, ⟨-, -, hw64⟩, ⟨-, hd⟩ | ⟨hw, hd⟩⟩ | ⟨-, -, -, -, hd⟩ | ⟨-, -, -, hd⟩ <;>
          rw [hd] at h <;> simp at h
        · subst h; simp [Loc.isCell] at hl
        · subst h
          rw [hm] at hm'
          cases hm'
          simp [hw, hw64 hw, Arg.access, Width.bytes]
      · exact .inr (zip_write_of_def hl hm t h)

/-- A cell the stacked row reads is one of its uses. -/
theorem zip_cellArg {core : Core} {a : Word} {r : GPR} :
    ∀ {L : List (Bound Loc)} {S : List Slot} {xs₁ xs₂ : List Arg}, Zip4 (PosOk c LB) L S xs₁ xs₂ →
      CellArg core a r S xs₁ xs₂ →
      ∃ b ∈ L, ∃ l ∈ b.uses, l.isCell = true ∧ ∃ m, c.cell l = .ok m ∧ a = m.eval core
  | _, _, _, _, .nil, h => h.elim
  | _, _, _, _, .cons ⟨hp, hb, hr, hpl⟩ t, h => by
      rcases h with ⟨hrw, h₁, m', h₂, ha⟩ | h
      · rcases pos_cases hcells hb hr hpl hp with ⟨r', rfl, rfl, -, -⟩ |
            ⟨l, m, hl, hm, rfl, rfl, hlb, -⟩ | ⟨m₁, m₂, rfl, rfl, hd⟩ | ⟨v, rfl, rfl, hd⟩
        · cases h₂
        · cases h₁; cases h₂
          exact ⟨_, List.mem_cons_self, l, hlb.2.1 hrw, hl, _, hm, ha.symm⟩
        · cases h₁
        · cases h₁
      · obtain ⟨b, hb', rest⟩ := zip_cellArg t h
        exact ⟨b, List.mem_cons_of_mem _ hb', rest⟩


end Zipped

theorem memCount_eq : ∀ xs : List Arg, memCount xs = memArgs xs
  | [] => rfl
  | a :: xs => by
      cases a <;> simp [memCount, memArgs, memCount_eq xs, List.filter_cons]

/-! ## Xl's side of a row -/

theorem optGuard_some {p : Prop} [Decidable p] {u : Unit} (h : optGuard p = some u) : p := by
  unfold optGuard at h
  by_cases hp : p
  · exact hp
  · simp [guard, hp] at h

theorem readAll_some {regs : Xl.Regs} {fr : Xl.Frame} :
    ∀ {ls : List Loc} {vs : List Word}, Xl.readAll regs fr ls = some vs → ∀ l ∈ ls, ∃ v, Xl.read regs fr l = some v
  | [], _, _, l, hl => by simp at hl
  | l :: ls, vs, h, l', hl' => by
      simp only [Xl.readAll, List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨v, hv, vs', hvs', -⟩ := h
      rcases List.mem_cons.1 hl' with rfl | hl'
      · exact ⟨v, hv⟩
      · exact readAll_some (ls := ls) hvs' l' hl'

theorem filter_isSlot {bs₁ bs₂ : List (Bound Loc)} {S : List Slot} {I : List Implicit}
    (h₁ : bs₁.map Bound.slot? = S.map some) (h₂ : bs₂.map Bound.implicit? = I.map some) :
    (bs₁ ++ bs₂).filter Bound.isSlot = bs₁ := by
  rw [List.filter_append, List.filter_eq_self.2, List.filter_eq_nil_iff.2, List.append_nil]
  · intro b hb
    obtain ⟨i, hi⟩ : ∃ i, b.implicit? = some i := by
      have : b.implicit? ∈ I.map some := h₂ ▸ List.mem_map_of_mem hb
      obtain ⟨i, -, e⟩ := List.mem_map.1 this
      exact ⟨i, e.symm⟩
    cases b <;> simp_all [Bound.implicit?, Bound.isSlot]
  · intro b hb
    have : b.slot? ∈ S.map some := h₁ ▸ List.mem_map_of_mem hb
    obtain ⟨s, -, e⟩ := List.mem_map.1 this
    exact isSlot_of_slot? e.symm

/-- An implicit bound: its register's definition, if it writes, at that register. -/
theorem implicit_bounds {LB : List (Bound Loc)} :
    ∀ {bs₂ : List (Bound Loc)} {I : List Implicit}, bs₂.map Bound.implicit? = I.map some →
      (∀ b ∈ bs₂, b.RoleOk) → (∀ b ∈ bs₂, Xl.Bound.placeable b = true) →
      implicitWrites I = (bs₂.flatMap Bound.defs).map (placeL LB) ∧
        (∀ d ∈ bs₂.flatMap Bound.defs, ∃ r, d = .reg r) ∧
        ∀ i ∈ I, i.role.reads = true → ∃ b ∈ bs₂, Loc.reg i.reg ∈ b.uses
  | [], I, h, _, _ => by
      cases I with
      | nil => simp [implicitWrites]
      | cons => simp at h
  | b :: bs₂, I, h, hr, hp => by
      cases I with
      | nil => simp at h
      | cons i I =>
      simp only [List.map_cons, List.cons.injEq] at h
      obtain ⟨ih₁, ih₂, ih₃⟩ := implicit_bounds (LB := LB) h.2 (fun b hb => hr b (List.mem_cons_of_mem _ hb))
        (fun b hb => hp b (List.mem_cons_of_mem _ hb))
      have hr₀ := hr b List.mem_cons_self
      have hp₀ := hp b List.mem_cons_self
      cases b with
      | fixedUse i' a =>
        simp only [Bound.implicit?, Option.some.injEq] at h
        obtain ⟨rfl, -⟩ := h
        simp only [Bound.RoleOk] at hr₀
        simp only [Xl.Bound.placeable, beq_iff_eq] at hp₀
        subst hp₀
        refine ⟨?_, ?_, ?_⟩
        · simpa [implicitWrites, hr₀.2, Bound.defs] using ih₁
        · simpa [Bound.defs] using ih₂
        · intro j hj hjr
          rcases List.mem_cons.1 hj with rfl | hj
          · exact ⟨_, List.mem_cons_self, by simp [Bound.uses]⟩
          · obtain ⟨b, hb, hu⟩ := ih₃ j hj hjr
            exact ⟨b, List.mem_cons_of_mem _ hb, hu⟩
      | fixedDef i' x =>
        simp only [Bound.implicit?, Option.some.injEq] at h
        obtain ⟨rfl, -⟩ := h
        simp only [Bound.RoleOk] at hr₀
        simp only [Xl.Bound.placeable, beq_iff_eq] at hp₀
        subst hp₀
        refine ⟨?_, ?_, ?_⟩
        · simp only [implicitWrites, List.filter_cons, hr₀.2, ↓reduceIte, List.map_cons, List.flatMap_cons,
            Bound.defs, List.cons_append, List.nil_append]
          rw [Xl.placeL_reg]
          simpa [implicitWrites] using ih₁
        · intro d hd
          simp only [List.flatMap_cons, Bound.defs, List.cons_append, List.nil_append, List.mem_cons] at hd
          rcases hd with rfl | hd
          · exact ⟨_, rfl⟩
          · exact ih₂ d hd
        · intro j hj hjr
          rcases List.mem_cons.1 hj with rfl | hj
          · rw [hr₀.1] at hjr; cases hjr
          · obtain ⟨b, hb, hu⟩ := ih₃ j hj hjr
            exact ⟨b, List.mem_cons_of_mem _ hb, hu⟩
      | fixedTied i' a x =>
        simp only [Bound.implicit?, Option.some.injEq] at h
        obtain ⟨rfl, -⟩ := h
        simp only [Bound.RoleOk] at hr₀
        simp only [Xl.Bound.placeable, Bool.and_eq_true, beq_iff_eq] at hp₀
        obtain ⟨rfl, rfl⟩ := hp₀
        refine ⟨?_, ?_, ?_⟩
        · simp only [implicitWrites, List.filter_cons, hr₀.2, ↓reduceIte, List.map_cons, List.flatMap_cons,
            Bound.defs, List.cons_append, List.nil_append]
          rw [Xl.placeL_reg]
          simpa [implicitWrites] using ih₁
        · intro d hd
          simp only [List.flatMap_cons, Bound.defs, List.cons_append, List.nil_append, List.mem_cons] at hd
          rcases hd with rfl | hd
          · exact ⟨_, rfl⟩
          · exact ih₂ d hd
        · intro j hj hjr
          rcases List.mem_cons.1 hj with rfl | hj
          · exact ⟨_, List.mem_cons_self, by simp [Bound.uses]⟩
          · obtain ⟨b, hb, hu⟩ := ih₃ j hj hjr
            exact ⟨b, List.mem_cons_of_mem _ hb, hu⟩
      | _ => simp [Bound.implicit?] at h

/-- Xl reads each definition back from the register it ran in. -/
theorem readback_loc {LB : List (Bound Loc)} (hcells : (xlCells LB).length ≤ (xlFree LB).length) :
    ∀ {bs : List (Bound Loc)}, (∀ b ∈ bs, b ∈ LB) → (∀ b ∈ bs, Xl.Bound.placeable b = true) →
      bs.flatMap (Bound.readback (Xl.placeIn (xlTable LB))) =
        (bs.flatMap Bound.defs).map fun l => (l, some (placeL LB l))
  | [], _, _ => rfl
  | b :: bs, hm, hp => by
      simp only [List.flatMap_cons, List.map_append]
      rw [readback_loc hcells (fun b hb => hm b (List.mem_cons_of_mem _ hb))
        (fun b hb => hp b (List.mem_cons_of_mem _ hb))]
      congr 1
      have hp₀ := hp b List.mem_cons_self
      have hloc : ∀ l ∈ b.uses ++ b.defs, Xl.placeIn (xlTable LB) l = some (placeL LB l) := fun l hl =>
        Xl.placeIn_locs hcells (List.mem_flatMap.2 ⟨b, hm b List.mem_cons_self, Xl.Bound.mem_locs.2 hl⟩)
      cases b with
      | output s x => simp [Bound.readback, Bound.defs, hloc x (by simp [Bound.defs])]
      | tied s a x =>
        simp only [Xl.Bound.placeable, Bool.and_eq_true, beq_iff_eq] at hp₀
        obtain ⟨rfl, -⟩ := hp₀
        simp [Bound.readback, Bound.defs, hloc a (by simp [Bound.defs])]
      | fixedDef i x =>
        simp only [Xl.Bound.placeable, beq_iff_eq] at hp₀
        subst hp₀
        simp [Bound.readback, Bound.defs, Xl.placeL_reg]
      | fixedTied i a x =>
        simp only [Xl.Bound.placeable, Bool.and_eq_true, beq_iff_eq] at hp₀
        obtain ⟨-, rfl⟩ := hp₀
        simp [Bound.readback, Bound.defs, Xl.placeL_reg]
      | _ => rfl

/-- Xl's write-back, from its success. -/
theorem writeBacks_of {core : Core} :
    ∀ {L : List (Loc × GPR)} {regs : Xl.Regs} {fr : Xl.Frame} {regs' : Xl.Regs} {fr' : Xl.Frame},
      regs.size = 16 → (L.map Prod.fst).Nodup →
      (L.map fun p => (p.1, some p.2)).foldlM (Xl.writeBack core) (regs, fr) = some (regs', fr') →
      regs'.size = 16 ∧ Xl.Frame.SameCtl fr fr' ∧ (∀ p ∈ L, Xl.read regs' fr' p.1 = some (core.readReg p.2)) ∧
        (∀ l, l ∉ L.map Prod.fst → Xl.read regs' fr' l = Xl.read regs fr l)
  | [], regs, fr, regs', fr', hs, _, h => by
      simp only [List.map_nil, List.foldlM_nil, pure, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨hs, Xl.Frame.SameCtl.refl _, by simp, fun _ _ => rfl⟩
  | p :: L, regs, fr, regs', fr', hs, hn, h => by
      simp only [List.map_cons, List.nodup_cons, List.mem_map] at hn
      simp only [List.map_cons, List.foldlM_cons, Xl.writeBack, Option.bind_eq_bind, Option.bind_some,
        Option.bind_eq_some_iff] at h
      obtain ⟨⟨regs₁, fr₁⟩, hw, h⟩ := h
      obtain ⟨hread, hother, hctl, hs₁⟩ := Xl.write_spec hs hw
      obtain ⟨hs', hctl', hL, hL'⟩ := writeBacks_of (L := L) hs₁ hn.2 h
      refine ⟨hs', hctl.trans hctl', ?_, ?_⟩
      · intro q hq
        rcases List.mem_cons.1 hq with rfl | hq
        · rw [hL' q.1 (fun hm => hn.1 (by
            obtain ⟨q', hq', e⟩ := List.mem_map.1 hm
            exact ⟨q', hq', e⟩)), hread]
        · exact hL q hq
      · intro l hl
        simp only [List.map_cons, List.mem_cons, not_or] at hl
        rw [hL' l hl.2, hother l hl.1]

/-! ## Agreement of the running frame -/

/-- The registers Xl knows hold the machine's values. -/
def RegsRel (regs : Xl.Regs) (core : Core) : Prop :=
  ∀ r, Xl.reserved r = false → ∀ v, regs.get r = some v → core.readReg r = v

/-- The frame's cells, as the stacked code addresses them from `core`, hold
Xl's values where Xl knows them. -/
def CellsRel (c : FnCtx) (regs : Xl.Regs) (fr : Xl.Frame) (core : Core) : Prop :=
  ∀ l, l.isCell = true → ∀ v, Xl.read regs fr l = some v →
    ∃ m, c.cell l = .ok m ∧ core.memory.read64 (m.eval core) = v

/-- The frame's cells are cells, and distinct ones do not overlap. -/
structure FrameCells (c : FnCtx) (xm : Memory) (core : Core) : Prop where
  cell : ∀ l m, c.cell l = .ok m → Cell xm core.memory (m.eval core)
  disjoint : ∀ l l' m m', c.cell l = .ok m → c.cell l' = .ok m' → l ≠ l' →
    ∀ i < 8, ∀ j < 8, m.eval core + UInt64.ofNat i ≠ m'.eval core + UInt64.ofNat j

/-- Xl's running frame and the machine agree. -/
structure Agree (c : FnCtx) (regs : Xl.Regs) (fr : Xl.Frame) (mem : Memory) (ctx : Word) (core : Core) :
    Prop where
  size : regs.size = 16
  regsRel : RegsRel regs core
  ctxReg : core.readReg .r15 = ctx
  inside : Inside mem core.memory
  cells : CellsRel c regs fr core
  frame : FrameCells c mem core

/-- What an instruction defining `defs` leaves: agreement again, the frame's
control fields, `rsp`, permissions, every register outside the definitions,
and every machine byte outside the defined cells that Xl cannot write. -/
structure After (c : FnCtx) (defs : List Loc) (fr : Xl.Frame) (mem : Memory) (core : Core)
    (regs' : Xl.Regs) (fr' : Xl.Frame) (mem' : Memory) (ctx : Word) (core' : Core) : Prop where
  agree : Agree c regs' fr' mem' ctx core'
  ctl : Xl.Frame.SameCtl fr fr'
  rsp : core'.readReg .rsp = core.readReg .rsp
  readable₁ : mem'.readable = mem.readable
  writable₁ : mem'.writable = mem.writable
  readable₂ : core'.memory.readable = core.memory.readable
  writable₂ : core'.memory.writable = core.memory.writable
  regsKept : ∀ r, Loc.reg r ∉ defs → core'.readReg r = core.readReg r
  bytes : ∀ x, mem.writable x = false →
    (∀ l ∈ defs, l.isCell = true → ∀ m, c.cell l = .ok m → ∀ i < 8, x ≠ m.eval core + UInt64.ofNat i) →
    core'.memory.bytes x = core.memory.bytes x

/-- The memory a stacked row touches: what Xl may touch, or a cell of the
frame. -/
structure Foot (c : FnCtx) (o : Op) (xs : List Arg) (mem : Memory) (core : Core) (U D : List Loc) : Prop where
  reads : ∀ acc ∈ Op.reads o xs core,
    (∀ i < acc.bytes, mem.readable (acc.address + UInt64.ofNat i) = true) ∨
      (acc.bytes ≤ 8 ∧ ∃ l ∈ U, l.isCell = true ∧ ∃ m, c.cell l = .ok m ∧ acc.address = m.eval core)
  writes : ∀ acc ∈ Op.writes o xs core,
    (∀ i < acc.bytes, mem.writable (acc.address + UInt64.ofNat i) = true) ∨
      (acc.bytes = 8 ∧ ∃ l, l.isCell = true ∧ ∃ m, c.cell l = .ok m ∧ acc.address = m.eval core)
  defs : ∀ l ∈ D, l.isCell = true → ∀ m, c.cell l = .ok m → (⟨m.eval core, 8⟩ : Access) ∈ Op.writes o xs core

theorem cell_rsp {c : FnCtx} {l : Loc} {m : MemAddr} (h : c.cell l = .ok m) {c₁ c₂ : Core}
    (hrsp : c₁.readReg .rsp = c₂.readReg .rsp) : m.eval c₁ = m.eval c₂ := by
  cases l with
  | reg r => simp [FnCtx.cell, throw, throwThe, MonadExceptOf.throw] at h
  | slot i =>
    simp only [FnCtx.cell] at h
    split at h
    · simp only [pure, Except.pure, Except.ok.injEq] at h
      subst h
      simp [rspAt, MemAddr.eval, hrsp]
    · simp [throw, throwThe, MonadExceptOf.throw] at h
  | outArg i =>
    simp only [FnCtx.cell] at h
    split at h
    · simp only [pure, Except.pure, Except.ok.injEq] at h
      subst h
      simp [rspAt, MemAddr.eval, hrsp]
    · simp [throw, throwThe, MonadExceptOf.throw] at h
  | inArg i =>
    simp only [FnCtx.cell] at h
    split at h
    · simp only [pure, Except.pure, Except.ok.injEq] at h
      subst h
      simp [rspAt, MemAddr.eval, hrsp]
    · simp [throw, throwThe, MonadExceptOf.throw] at h

theorem FrameCells.keep {c : FnCtx} {xm xm' : Memory} {core core' : Core} (h : FrameCells c xm core)
    (hrsp : core'.readReg .rsp = core.readReg .rsp) (h₁ : xm'.readable = xm.readable)
    (h₂ : xm'.writable = xm.writable) (h₃ : core'.memory.readable = core.memory.readable)
    (h₄ : core'.memory.writable = core.memory.writable) : FrameCells c xm' core' := by
  refine ⟨fun l m hm => ?_, fun l l' m m' hm hm' hne => ?_⟩
  · rw [cell_rsp hm hrsp]
    exact (h.cell l m hm).perm h₁ h₂ h₃ h₄
  · rw [cell_rsp hm hrsp, cell_rsp hm' hrsp]
    exact h.disjoint l l' m m' hm hm' hne

theorem read64_congr {m m' : Memory} {a : Word} (h : ∀ i < 8, m'.bytes (a + UInt64.ofNat i) = m.bytes (a + UInt64.ofNat i)) :
    m'.read64 a = m.read64 a :=
  Memory.readLittle_congr _ _ _ _ h

theorem distinctLocs_nodup : ∀ {ls : List Loc}, distinctLocs ls = true → ls.Nodup
  | [], _ => List.nodup_nil
  | l :: ls, h => by
      simp only [distinctLocs, Bool.and_eq_true, Bool.not_eq_true', List.contains_eq_any_beq,
        List.any_eq_false, beq_iff_eq] at h
      exact List.nodup_cons.2 ⟨fun hm => h.1 l hm rfl, distinctLocs_nodup h.2⟩

theorem zip_def_cell {c : FnCtx} {LB : List (Bound Loc)} (hcells : (xlCells LB).length ≤ (xlFree LB).length)
    {l : Loc} (hl : l.isCell = true) :
    ∀ {L : List (Bound Loc)} {S : List Slot} {xs₁ xs₂ : List Arg}, Zip4 (PosOk c LB) L S xs₁ xs₂ →
      l ∈ L.flatMap Bound.defs → ∃ m, c.cell l = .ok m
  | _, _, _, _, .nil, h => by simp at h
  | _, _, _, _, .cons ⟨hp, hb, hr, hpl⟩ t, h => by
      rw [List.flatMap_cons, List.mem_append] at h
      rcases h with h | h
      · rcases pos_cases hcells hb hr hpl hp with ⟨r, -, -, -, ⟨-, hd⟩ | ⟨-, hd⟩⟩ |
            ⟨l', m', -, hm', -, -, -, ⟨-, hd⟩ | ⟨-, hd⟩⟩ | ⟨-, -, -, -, hd⟩ | ⟨-, -, -, hd⟩ <;>
          rw [hd] at h <;> simp at h
        · subst h; simp [Loc.isCell] at hl
        · subst h; exact ⟨m', hm'⟩
      · exact zip_def_cell hcells hl t h

/-- One row run by Xl (on `c₁`) and by the stacked code (on `c₂`), whose
locations agree: the stacked run succeeds, with the same flags, leaving
related cores (`RowOut`). The stacked row writes exactly the register
definitions, and each cell definition from the register Xl lent it. -/
theorem part_rel {c : FnCtx} {LB : List (Bound Loc)} (hcells : (xlCells LB).length ≤ (xlFree LB).length)
    {o : Op} {defs : List Loc} {args : List (XArg Loc)} {bs : List (Bound Loc)}
    (hbind : bindRow o defs args = some bs) (hsub : ∀ b ∈ bs, b ∈ LB)
    (hplace : ∀ b ∈ bs, Xl.Bound.placeable b = true)
    {xs₁ xs₂ : List Arg} (hx₁ : slotArgs (Xl.placeIn (xlTable LB)) Xl.Loc.reg? bs = some xs₁)
    (hx₂ : (bs.filter Bound.isSlot).mapM c.slotArg = .ok xs₂) {narrowOk : Bool}
    (hshape : rowShape o bs xs₂ narrowOk = true) {c₁ c₂ : Core}
    (huse : ∀ u ∈ bs.flatMap Bound.uses, LocAgree c LB c₁ c₂ u)
    (hres : ∀ u ∈ bs.flatMap Bound.uses, ∀ r, u = .reg r → Xl.reserved r = false)
    (hdef : ∀ d ∈ bs.flatMap Bound.defs, d.isCell = true → ∀ m, c.cell d = .ok m →
      Cell c₁.memory c₂.memory (m.eval c₂))
    (hnarrow : ∀ b ∈ bs, b.narrowOutput = true → ∀ d ∈ b.defs, ∀ r, d = .reg r → c₁.readReg r = c₂.readReg r)
    (h15 : c₁.readReg .r15 = c₂.readReg .r15) (hin : Inside c₁.memory c₂.memory)
    {fl fl' : ByteEval.Flags} {c₁' : Core} (h : o.exec xs₁ c₁ fl = .ok (c₁', fl')) :
    ∃ c₂', o.exec xs₂ c₂ fl = .ok (c₂', fl') ∧ RowOut o c₁ c₂ c₁' c₂' xs₁ xs₂ ∧
      (∀ r, r ∈ rowWrites o xs₂ ↔ Loc.reg r ∈ bs.flatMap Bound.defs) ∧
      (∀ r, r ∈ rowWrites o xs₁ ↔ ∃ l ∈ bs.flatMap Bound.defs, r = placeL LB l) ∧
      (∀ a r, CellWrite c₂ a r (desc o).slots xs₁ xs₂ →
        ∃ l ∈ bs.flatMap Bound.defs, l.isCell = true ∧ ∃ m, c.cell l = .ok m ∧ a = m.eval c₂ ∧ r = placeL LB l) ∧
      (∀ l ∈ bs.flatMap Bound.defs, l.isCell = true → ∃ m, c.cell l = .ok m ∧
        CellWrite c₂ (m.eval c₂) (placeL LB l) (desc o).slots xs₁ xs₂) ∧
      (∀ a r, CellArg c₂ a r (desc o).slots xs₁ xs₂ →
        ∃ l ∈ bs.flatMap Bound.uses, l.isCell = true ∧ ∃ m, c.cell l = .ok m ∧ a = m.eval c₂) ∧
      (∀ l ∈ bs.flatMap Bound.defs, l.isCell = true → ∀ m, c.cell l = .ok m →
        (⟨m.eval c₂, 8⟩ : Access) ∈ Op.writes o xs₂ c₂) ∧
      (desc o).stack = .none := by
  simp only [rowShape, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true,
    Bool.or_eq_true] at hshape
  obtain ⟨⟨⟨⟨hstack, hwide⟩, hmem⟩, hdist⟩, -⟩ := hshape
  obtain ⟨bs₁, bs₂, rfl, hs₁, hs₂, hrole⟩ := bindRow_shape hbind
  have hfilt := filter_isSlot hs₁ hs₂
  rw [hfilt] at hx₂
  unfold slotArgs at hx₁
  rw [hfilt] at hx₁
  have hz : Zip4 (PosOk c LB) bs₁ (desc o).slots xs₁ xs₂ :=
    (zip4_of_mapM (c := c) (LB := LB) hs₁ hx₁ hx₂).mem
      (Q := fun b => b ∈ LB ∧ b.RoleOk ∧ Xl.Bound.placeable b = true)
      (fun b hb => ⟨hsub b (List.mem_append_left _ hb), hrole b (List.mem_append_left _ hb),
        hplace b (List.mem_append_left _ hb)⟩)
      (fun _ _ _ _ hq hp => ⟨hp, hq⟩)
  obtain ⟨hI₁, hI₂, hI₃⟩ := implicit_bounds (LB := LB) hs₂ (fun b hb => hrole b (List.mem_append_right _ hb))
    (fun b hb => hplace b (List.mem_append_right _ hb))
  have hargs : ArgsRel c₁ c₂ (desc o).slots xs₁ xs₂ :=
    bounds_argsRel hcells h15 hs₁ (fun b hb =>
      { mem := hsub b (List.mem_append_left _ hb)
        role := hrole b (List.mem_append_left _ hb)
        placeable := hplace b (List.mem_append_left _ hb)
        use := fun u hu => huse u (List.mem_flatMap.2 ⟨b, List.mem_append_left _ hb, hu⟩)
        res := fun u hu => hres u (List.mem_flatMap.2 ⟨b, List.mem_append_left _ hb, hu⟩)
        def_ := fun d hd => hdef d (List.mem_flatMap.2 ⟨b, List.mem_append_left _ hb, hd⟩)
        narrow := hnarrow b (List.mem_append_left _ hb) }) hx₁ hx₂
  have himp : ∀ i ∈ (desc o).implicit, (i.role.reads = true ∨ (i.role.writes = true ∧ ¬ Wide i.width)) →
      c₁.readReg i.reg = c₂.readReg i.reg := by
    intro i hi hc
    have hrd : i.role.reads = true := by
      rcases hc with hc | ⟨-, hnw⟩
      · exact hc
      · rcases hwide i hi with (hr | hw) | hw
        · exact hr
        · exact absurd (.inl hw) hnw
        · exact absurd (.inr hw) hnw
    obtain ⟨b, hb, hu⟩ := hI₃ i hi hrd
    exact huse _ (List.mem_flatMap.2 ⟨b, List.mem_append_right _ hb, hu⟩)
  have hw₁ : rowWrites o xs₁ = ((bs₁ ++ bs₂).flatMap Bound.defs).map (placeL LB) := by
    rw [rowWrites, zip_slotWrites₁ hcells hz, hI₁, List.flatMap_append, List.map_append]
  have hdefsLoc : ∀ l ∈ (bs₁ ++ bs₂).flatMap Bound.defs, l ∈ xlLocs LB := fun l hl => by
    obtain ⟨b, hb, hl⟩ := List.mem_flatMap.1 hl
    exact List.mem_flatMap.2 ⟨b, hsub b hb, Xl.Bound.mem_locs.2 (List.mem_append_right _ hl)⟩
  have hnd : (rowWrites o xs₁).Nodup := by
    rw [hw₁]
    exact nodup_map_on (fun x hx y hy e => Xl.placeL_inj hcells (hdefsLoc x hx) (hdefsLoc y hy) e)
      (distinctLocs_nodup hdist)
  have hone : memCount xs₂ ≤ 1 := by rw [memCount_eq]; exact hmem
  obtain ⟨c₂', h₂, out⟩ := exec_rel hstack hin hargs himp hnd hone h
  refine ⟨c₂', h₂, out, fun r => ?_, fun r => ?_, fun a r hc => ?_, fun l hl hc => ?_,
    fun a r hc => ?_, fun l hl hc m hm => ?_, hstack⟩
  · rw [rowWrites, zip_slotWrites₂ hcells hz, hI₁, List.mem_append, List.flatMap_append, List.mem_append,
      List.mem_filterMap, List.mem_map]
    constructor
    · rintro (⟨l, hl, e⟩ | ⟨l, hl, e⟩)
      · cases l <;> simp [Xl.Loc.reg?] at e
        subst e
        exact .inl hl
      · obtain ⟨r', rfl⟩ := hI₂ l hl
        rw [Xl.placeL_reg] at e
        subst e
        exact .inr hl
    · rintro (hl | hl)
      · exact .inl ⟨_, hl, rfl⟩
      · exact .inr ⟨_, hl, Xl.placeL_reg _ _⟩
  · rw [hw₁, List.mem_map]
    constructor
    · rintro ⟨l, hl, rfl⟩; exact ⟨l, hl, rfl⟩
    · rintro ⟨l, hl, rfl⟩; exact ⟨l, hl, rfl⟩
  · obtain ⟨l, hl, rest⟩ := zip_cellWrite hcells hz hc
    exact ⟨l, by rw [List.flatMap_append]; exact List.mem_append_left _ hl, rest⟩
  · rw [List.flatMap_append, List.mem_append] at hl
    rcases hl with hl | hl
    · obtain ⟨m, hm⟩ := zip_def_cell hcells hc hz hl
      exact ⟨m, hm, zip_cellWrite_of hcells hc hm hz hl⟩
    · obtain ⟨r, rfl⟩ := hI₂ l hl
      simp [Loc.isCell] at hc
  · obtain ⟨b, hb, l, hlu, hl, m, hm, ha⟩ := zip_cellArg hcells hz hc
    exact ⟨l, List.mem_flatMap.2 ⟨b, List.mem_append_left _ hb, hlu⟩, hl, m, hm, ha⟩
  · rw [List.flatMap_append, List.mem_append] at hl
    simp only [Op.writes, Op.pushes, hstack, List.nil_append]
    rcases hl with hl | hl
    · exact zip_write_of_def hcells hc hm hz hl
    · obtain ⟨r, rfl⟩ := hI₂ l hl
      simp [Loc.isCell] at hc

/-- Xl's locations, lent registers in the row core it builds, agree with
the machine's where Xl reads them. -/
theorem uses_agree {c : FnCtx} {LB : List (Bound Loc)} (hcells : (xlCells LB).length ≤ (xlFree LB).length)
    {regs : Xl.Regs} {fr : Xl.Frame} {mem : Memory} {ctx : Word} {core : Core} (ha : Agree c regs fr mem ctx core)
    {z : List GPR} (hz : ∀ r ∈ z, r ∈ xlNamed LB) (hres : (xlNamed LB).all (!Xl.reserved ·) = true)
    {u : Loc} (hu : u ∈ xlLocs LB) (hzu : ∀ r, u = .reg r → r ∉ z) {v : Word} (hv : Xl.read regs fr u = some v) :
    LocAgree c LB ⟨Xl.rowRegisters regs fr ctx (xlTable LB) z, mem⟩ core u := by
  have hres' : ∀ r, u = .reg r → Xl.reserved r = false := fun r e => by
    subst e
    have := List.all_eq_true.1 hres r (Xl.mem_xlNamed.2 hu)
    simpa using this
  have hrow := Xl.rowRegisters_use hcells (regs := regs) (fr := fr) (ctx := ctx) hz hu hres' hzu
  cases u with
  | reg r =>
    change Xl.rowRegisters regs fr ctx (xlTable LB) z r = core.readReg r
    rw [Xl.placeL_reg] at hrow
    rw [hrow, hv, Option.getD_some]
    rw [Xl.read_reg (hres' r rfl)] at hv
    exact (ha.regsRel r (hres' r rfl) v hv).symm
  | _ =>
    obtain ⟨m, hm, hm'⟩ := ha.cells _ rfl v hv
    refine ⟨m, hm, ha.frame.cell _ m hm, ?_⟩
    change _ = Xl.rowRegisters regs fr ctx (xlTable LB) z (placeL LB _)
    rw [hrow, hv, Option.getD_some, hm']

/-- A row instruction: when Xl runs `op o defs args`, its stacked `.op`
runs, and the frame agrees again. -/
theorem op_sim {c : FnCtx} {o : Op} {defs : List Loc} {args : List (XArg Loc)} {bs : List (Bound Loc)}
    (hbind : bindRow o defs args = some bs) {xs : List Arg} (hxs : c.rowArgs bs = .ok xs)
    (hshape : rowShape o bs xs false = true)
    {regs : Xl.Regs} {fr : Xl.Frame} {mem : Memory} {ctx : Word} {core : Core} (ha : Agree c regs fr mem ctx core)
    {regs' : Xl.Regs} {fr' : Xl.Frame} {mem' : Memory} {flags : ByteEval.Flags}
    (h : Xl.execBound [(o, bs)] regs fr mem ctx false = some (regs', fr', mem', flags)) :
    ∃ core', o.exec xs core {} = .ok (core', flags) ∧
      After c (bs.flatMap Bound.defs) fr mem core regs' fr' mem' ctx core' ∧ Foot c o xs mem core (bs.flatMap Bound.uses) (bs.flatMap Bound.defs) ∧
      (desc o).stack = .none := by
  rw [Xl.execBound_eq] at h
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, Option.bind_eq_some_iff] at h
  obtain ⟨_, hg₁, _, hg₂, _, hg₃, vs, hread, _, -, margs, hmargs, cf, hrows, rf, hrf, hfin⟩ := h
  have hplace : bs.all Xl.Bound.placeable = true := optGuard_some hg₁
  have hnamed := optGuard_some hg₂
  have hcells : (xlCells bs).length ≤ (xlFree bs).length := optGuard_some hg₃
  simp only [List.mapM_cons, List.mapM_nil, partArgs_eq, Option.bind_eq_bind, Option.bind_eq_some_iff,
    Option.map_eq_map, Option.map_eq_some_iff, Option.pure_def, Option.bind_some, Option.some.injEq] at hmargs
  obtain ⟨_, ⟨xs₁, hx₁, rfl⟩, rfl⟩ := hmargs
  have hz : Xl.zeroedRegs [(o, bs)] false = [] := rfl
  rw [hz] at hrows
  simp only [execRows, List.foldlM_cons, List.foldlM_nil, execRow, Option.bind_eq_bind] at hrows
  split at hrows
  · rename_i res hex
    simp only [Option.bind_some, pure, Option.some.injEq] at hrows
    subst hrows
    simp only [Option.some.injEq, Prod.mk.injEq] at hfin
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hfin
    unfold FnCtx.rowArgs at hxs
    simp only [hplace, Bool.not_true, Bool.false_eq_true, ↓reduceIte, pure_bind] at hxs
    have hall := List.all_eq_true.1 hplace
    have hshape' := hshape
    simp only [rowShape, Bool.and_eq_true, Bool.or_eq_true, Bool.false_eq_true, false_or,
      Bool.not_eq_true', List.any_eq_false] at hshape'
    have hnn := hshape'.2
    have huse : ∀ u ∈ bs.flatMap Bound.uses, LocAgree c bs ⟨Xl.rowRegisters regs fr ctx (xlTable bs) [], mem⟩ core u :=
      fun u hu => by
        have hl : u ∈ xlLocs bs := by
          obtain ⟨b, hb, hu⟩ := List.mem_flatMap.1 hu
          exact List.mem_flatMap.2 ⟨b, hb, Xl.Bound.mem_locs.2 (List.mem_append_left _ hu)⟩
        obtain ⟨v, hv⟩ := readAll_some hread u hu
        exact uses_agree hcells ha (by simp) hnamed hl (by simp) hv
    have hres : ∀ u ∈ bs.flatMap Bound.uses, ∀ r, u = .reg r → Xl.reserved r = false := fun u hu r e => by
      subst e
      have hl : Loc.reg r ∈ xlLocs bs := by
        obtain ⟨b, hb, hu⟩ := List.mem_flatMap.1 hu
        exact List.mem_flatMap.2 ⟨b, hb, Xl.Bound.mem_locs.2 (List.mem_append_left _ hu)⟩
      simpa using List.all_eq_true.1 hnamed r (Xl.mem_xlNamed.2 hl)
    obtain ⟨core', h₂, out, hW₂, -, hCW, hCWof, hCA, hWD, hstack⟩ :=
      part_rel (c := c) hcells hbind (fun b hb => hb) hall hx₁ hxs hshape huse hres
        (fun d _ _ m hm => ha.frame.cell d m hm)
        (fun b hb hn => absurd hn (by simp [hnn b hb]))
        (by change Xl.rowRegisters regs fr ctx (xlTable bs) [] .r15 = _; rw [Xl.rowRegisters_r15, ha.ctxReg]) ha.inside hex
    have hdefsLoc : ∀ l ∈ bs.flatMap Bound.defs, l ∈ xlLocs bs := fun l hl => by
      obtain ⟨b, hb, hl⟩ := List.mem_flatMap.1 hl
      exact List.mem_flatMap.2 ⟨b, hb, Xl.Bound.mem_locs.2 (List.mem_append_right _ hl)⟩
    have hdefsRes : ∀ r, Loc.reg r ∈ bs.flatMap Bound.defs → Xl.reserved r = false := fun r hr => by
      simpa using List.all_eq_true.1 hnamed r (Xl.mem_xlNamed.2 (hdefsLoc _ hr))
    have hnd : (bs.flatMap Bound.defs).Nodup := by
      simp only [rowShape, Bool.and_eq_true] at hshape
      exact distinctLocs_nodup hshape.1.2
    rw [readback_loc hcells (fun b hb => hb) hall] at hrf
    have hrf' : (((bs.flatMap Bound.defs).map fun l => (l, placeL bs l)).map fun p => (p.1, some p.2)).foldlM
        (Xl.writeBack res.1) (regs, fr) = some rf := by
      rw [List.map_map]; exact hrf
    obtain ⟨hsize', hctl, hdefR, hother⟩ := writeBacks_of ha.size (by simpa [List.map_map, Function.comp_def] using hnd) hrf'
    have hkept : ∀ r, Loc.reg r ∉ bs.flatMap Bound.defs → core'.readReg r = core.readReg r := fun r hr =>
      out.frame₂ r fun hm => hr ((hW₂ r).1 hm)
    have hrsp : core'.readReg .rsp = core.readReg .rsp := hkept _ fun hm => by
      have := hdefsRes _ hm; simp [Xl.reserved] at this
    have h15' : core'.readReg .r15 = core.readReg .r15 := hkept _ fun hm => by
      have := hdefsRes _ hm; simp [Xl.reserved] at this
    have hother' : ∀ l, l ∉ bs.flatMap Bound.defs → Xl.read rf.1 rf.2 l = Xl.read regs fr l := fun l hl =>
      hother l (by simpa [List.map_map] using hl)
    have hdefR' : ∀ l ∈ bs.flatMap Bound.defs, Xl.read rf.1 rf.2 l = some (res.1.readReg (placeL bs l)) :=
      fun l hl => hdefR (l, placeL bs l) (List.mem_map_of_mem hl)
    refine ⟨core', h₂, ⟨⟨hsize', fun r hr v hv => ?_, by rw [h15', ha.ctxReg], out.inside, fun l hl v hv => ?_,
      ha.frame.keep hrsp out.readable₁ out.writable₁ out.readable₂ out.writable₂⟩, hctl, hrsp,
      out.readable₁, out.writable₁, out.readable₂, out.writable₂, hkept, fun x hx hout => ?_⟩, ⟨?_, ?_, hWD⟩, hstack⟩
    · by_cases hd : Loc.reg r ∈ bs.flatMap Bound.defs
      · have := hdefR' _ hd
        rw [Xl.read_reg hr, Xl.placeL_reg] at this
        rw [this] at hv
        cases hv
        exact out.written r ((hW₂ r).2 hd)
      · have := hother' _ hd
        rw [Xl.read_reg hr, Xl.read_reg hr, hv] at this
        rw [hkept r hd]
        exact ha.regsRel r hr v this.symm
    · by_cases hd : l ∈ bs.flatMap Bound.defs
      · rw [hdefR' l hd] at hv
        cases hv
        obtain ⟨m, hm, hcw⟩ := hCWof l hd hl
        exact ⟨m, hm, by rw [cell_rsp hm hrsp]; exact out.cell _ _ hcw⟩
      · rw [hother' l hd] at hv
        obtain ⟨m, hm, hm'⟩ := ha.cells l hl v hv
        refine ⟨m, hm, ?_⟩
        rw [cell_rsp hm hrsp, ← hm']
        refine read64_congr fun i hi => out.bytes _ ((ha.frame.cell l m hm).noWrite i hi) fun a r hcw j hj => ?_
        obtain ⟨l', hl', -, m', hm'', rfl, -⟩ := hCW a r hcw
        exact ha.frame.disjoint l l' m m' hm hm'' (fun e => hd (e ▸ hl')) i hi j hj
    · refine out.bytes x hx fun a r hcw i hi => ?_
      obtain ⟨l, hl, hc, m, hm, rfl, -⟩ := hCW a r hcw
      exact hout l hl hc m hm i hi
    · intro acc hacc
      rcases out.reads acc hacc with h | ⟨hb, r, hca⟩
      · exact .inl h
      · exact .inr ⟨hb, hCA _ r hca⟩
    · intro acc hacc
      rcases out.writes acc hacc with h | ⟨hb, r, hcw⟩
      · exact .inl h
      · obtain ⟨l, -, hl, m, hm, ha, -⟩ := hCW _ r hcw
        exact .inr ⟨hb, l, hl, m, hm, ha⟩
  · simp at hrows

end Compilatrix.Xv.Stacking.Proof
