import IxCC.Xv.Validate.Proof.XlLoc
import IxCC.Xv.Validate.Proof.Part

/-!
# The Xl placement

How `Xl.execBound` places a row's operands (05 §3): register locations run
in themselves, and the distinct stack cells borrow, in order, the scratch
registers the row does not name. With enough scratch registers, every
operand location gets a register (`placeL`), different locations get
different registers (`placeL_inj`), a borrowed register starts with its
cell's value, and an allocatable register location with its own
(`rowRegisters_use`).
-/

namespace IxCC.Xv.Xl

open IxCC.Lir (VReg Word)
open X86 (GPR)
open IxCC.Xv

/-! ## `dedup` -/

theorem mem_dedup {α : Type} [BEq α] [LawfulBEq α] {x : α} : ∀ {l : List α}, x ∈ dedup l ↔ x ∈ l
  | [] => by simp [dedup]
  | y :: ys => by
      simp only [dedup, List.mem_cons, List.mem_filter, mem_dedup, bne_iff_ne, ne_eq]
      by_cases h : x = y <;> simp [h]

theorem nodup_dedup {α : Type} [BEq α] [LawfulBEq α] : ∀ {l : List α}, (dedup l).Nodup
  | [] => by simp [dedup]
  | y :: ys => by
      unfold dedup
      rw [List.nodup_cons]
      refine ⟨fun hm => ?_, nodup_dedup.filter _⟩
      simp [List.mem_filter] at hm

/-! ## Lending tables -/

theorem lookup_mem : ∀ {t : List (Loc × GPR)} {l : Loc} {r : GPR}, t.lookup l = some r → (l, r) ∈ t
  | [], _, _, h => by simp at h
  | (k, v) :: t, l, r, h => by
      rw [List.lookup_cons] at h
      split at h
      · rename_i e
        simp only [beq_iff_eq] at e
        simp only [Option.some.injEq] at h
        subst e h
        exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (lookup_mem h)

theorem lookup_of_mem : ∀ {t : List (Loc × GPR)} {l : Loc} {r : GPR}, (t.map Prod.fst).Nodup →
    (l, r) ∈ t → t.lookup l = some r
  | [], _, _, _, h => by simp at h
  | (k, v) :: t, l, r, hn, h => by
      simp only [List.map_cons, List.nodup_cons, List.mem_map] at hn
      rw [List.lookup_cons]
      rcases List.mem_cons.1 h with e | h
      · simp only [Prod.mk.injEq] at e
        obtain ⟨rfl, rfl⟩ := e
        simp
      · have : l ≠ k := fun e => hn.1 ⟨(l, r), h, e⟩
        have : (l == k) = false := by simpa using this
        simp only [this]
        exact lookup_of_mem hn.2 h

theorem find?_snd_of_mem : ∀ {t : List (Loc × GPR)} {l : Loc} {r : GPR}, (t.map Prod.snd).Nodup →
    (l, r) ∈ t → t.find? (·.2 == r) = some (l, r)
  | [], _, _, _, h => by simp at h
  | (k, v) :: t, l, r, hn, h => by
      simp only [List.map_cons, List.nodup_cons, List.mem_map] at hn
      rw [List.find?_cons]
      rcases List.mem_cons.1 h with e | h
      · simp only [Prod.mk.injEq] at e
        obtain ⟨rfl, rfl⟩ := e
        simp
      · have : v ≠ r := fun e => hn.1 ⟨(l, r), h, e.symm⟩
        have : (v == r) = false := by simpa using this
        simp only [this]
        exact find?_snd_of_mem hn.2 h

theorem find?_snd_none {t : List (Loc × GPR)} {r : GPR} (h : r ∉ t.map Prod.snd) :
    t.find? (·.2 == r) = none := by
  rw [List.find?_eq_none]
  intro p hp e
  simp only [beq_iff_eq] at e
  exact h (List.mem_map.2 ⟨p, hp, e⟩)

theorem zip_snd_sublist {α β : Type} : ∀ {as : List α} {bs : List β}, ((as.zip bs).map Prod.snd).Sublist bs
  | [], bs => by simp
  | _ :: _, [] => by simp
  | a :: as, b :: bs => by
      simp only [List.zip_cons_cons, List.map_cons]
      exact zip_snd_sublist.cons_cons _

theorem exists_mem_zip {α β : Type} : ∀ {as : List α} {bs : List β}, as.length ≤ bs.length →
    ∀ {a : α}, a ∈ as → ∃ b, (a, b) ∈ as.zip bs
  | [], _, _, _, h => by simp at h
  | _ :: _, [], hl, _, _ => by simp at hl
  | a :: as, b :: bs, hl, x, h => by
      simp only [List.length_cons, Nat.add_le_add_iff_right] at hl
      rcases List.mem_cons.1 h with rfl | h
      · exact ⟨b, by simp⟩
      · obtain ⟨b', hb'⟩ := exists_mem_zip hl h
        exact ⟨b', List.mem_cons_of_mem _ hb'⟩

/-! ## The placement of a row -/

section Placement

variable (LB : List (Bound Loc))

def xlLocs : List Loc := LB.flatMap Bound.locs

def xlNamed : List GPR := (xlLocs LB).filterMap Loc.reg?

def xlCells : List Loc := dedup ((xlLocs LB).filter Loc.isCell)

def xlFree : List GPR := scratch.filter (!(xlNamed LB).contains ·)

def xlTable : List (Loc × GPR) := (xlCells LB).zip (xlFree LB)

/-- The register an operand location runs in. -/
def placeL (l : Loc) : GPR := (placeIn (xlTable LB) l).getD .rax

end Placement

theorem scratch_nodup : scratch.Nodup := by decide

theorem xlTable_fst_nodup (LB : List (Bound Loc)) (h : (xlCells LB).length ≤ (xlFree LB).length) :
    ((xlTable LB).map Prod.fst).Nodup := by
  unfold xlTable
  rw [List.map_fst_zip h]
  exact nodup_dedup

theorem xlTable_snd_nodup (LB : List (Bound Loc)) : ((xlTable LB).map Prod.snd).Nodup :=
  (zip_snd_sublist).nodup (scratch_nodup.filter _)

theorem xlTable_snd_free {LB : List (Bound Loc)} {p : Loc × GPR} (hp : p ∈ xlTable LB) :
    p.2 ∈ xlFree LB :=
  zip_snd_sublist.subset (List.mem_map_of_mem hp)

theorem mem_xlNamed {LB : List (Bound Loc)} {r : GPR} : r ∈ xlNamed LB ↔ Loc.reg r ∈ xlLocs LB := by
  unfold xlNamed
  rw [List.mem_filterMap]
  constructor
  · rintro ⟨l, hl, e⟩
    cases l <;> simp [Loc.reg?] at e
    subst e; exact hl
  · intro h; exact ⟨_, h, rfl⟩

theorem xlFree_not_named {LB : List (Bound Loc)} {r : GPR} (h : r ∈ xlFree LB) : r ∉ xlNamed LB := by
  unfold xlFree at h
  rw [List.mem_filter] at h
  intro hm
  have := h.2
  rw [List.contains_iff_mem.2 hm] at this
  cases this

theorem xlFree_scratch {LB : List (Bound Loc)} {r : GPR} (h : r ∈ xlFree LB) : r ∈ scratch := by
  unfold xlFree at h
  exact (List.mem_filter.1 h).1

theorem r15_not_scratch : GPR.r15 ∉ scratch := by decide

/-- Every operand location has a register. -/
theorem placeIn_locs {LB : List (Bound Loc)} (h : (xlCells LB).length ≤ (xlFree LB).length) {l : Loc}
    (hl : l ∈ xlLocs LB) : placeIn (xlTable LB) l = some (placeL LB l) := by
  unfold placeL
  cases l with
  | reg r => rfl
  | _ =>
    have hc : _ ∈ xlCells LB := mem_dedup.2 (List.mem_filter.2 ⟨hl, rfl⟩)
    obtain ⟨r, hr⟩ := exists_mem_zip h hc
    have := lookup_of_mem (xlTable_fst_nodup LB h) hr
    simp only [placeIn, xlTable] at this ⊢
    rw [this]; rfl

theorem placeL_reg (LB : List (Bound Loc)) (r : GPR) : placeL LB (.reg r) = r := rfl

theorem placeL_cell {LB : List (Bound Loc)} (h : (xlCells LB).length ≤ (xlFree LB).length) {l : Loc}
    (hl : l ∈ xlLocs LB) (hc : l.isCell = true) : (l, placeL LB l) ∈ xlTable LB := by
  have hp := placeIn_locs h hl
  cases l with
  | reg r => simp [Loc.isCell] at hc
  | _ => exact lookup_mem hp

/-- Different operand locations run in different registers. -/
theorem placeL_inj {LB : List (Bound Loc)} (h : (xlCells LB).length ≤ (xlFree LB).length)
    {l₁ l₂ : Loc} (h₁ : l₁ ∈ xlLocs LB) (h₂ : l₂ ∈ xlLocs LB) (he : placeL LB l₁ = placeL LB l₂) :
    l₁ = l₂ := by
  have cellFree : ∀ l, l ∈ xlLocs LB → l.isCell = true → placeL LB l ∈ xlFree LB :=
    fun l hl hc => xlTable_snd_free (placeL_cell h hl hc)
  have regNamed : ∀ r, Loc.reg r ∈ xlLocs LB → r ∈ xlNamed LB := fun r hr => mem_xlNamed.2 hr
  cases hc₁ : l₁.isCell <;> cases hc₂ : l₂.isCell
  · cases l₁ <;> simp [Loc.isCell] at hc₁
    cases l₂ <;> simp [Loc.isCell] at hc₂
    simp only [placeL_reg] at he
    rw [he]
  · cases l₁ <;> simp [Loc.isCell] at hc₁
    rename_i r
    rw [placeL_reg] at he
    exact absurd (regNamed r h₁) (he ▸ xlFree_not_named (cellFree l₂ h₂ hc₂))
  · cases l₂ <;> simp [Loc.isCell] at hc₂
    rename_i r
    rw [placeL_reg] at he
    exact absurd (regNamed r h₂) (he ▸ xlFree_not_named (cellFree l₁ h₁ hc₁))
  · have m₁ := placeL_cell h h₁ hc₁
    have m₂ := placeL_cell h h₂ hc₂
    rw [he] at m₁
    have f₁ := find?_snd_of_mem (xlTable_snd_nodup LB) m₁
    have f₂ := find?_snd_of_mem (xlTable_snd_nodup LB) m₂
    rw [f₁] at f₂
    simpa using f₂

/-! ## The registers before a row -/

theorem rowRegisters_r15 (regs : Regs) (fr : Frame) (ctx : Word) (t : List (Loc × GPR)) (z : List GPR) :
    rowRegisters regs fr ctx t z .r15 = ctx := by
  simp [rowRegisters]

theorem rowRegisters_zeroed {regs : Regs} {fr : Frame} {ctx : Word} {t : List (Loc × GPR)} {z : List GPR}
    {r : GPR} (hr : r ≠ .r15) (hz : r ∈ z) : rowRegisters regs fr ctx t z r = 0 := by
  have : (r == .r15) = false := by simpa using hr
  simp [rowRegisters, this, hz]

/-- A use location's register starts with the location's value. -/
theorem rowRegisters_use {LB : List (Bound Loc)} (h : (xlCells LB).length ≤ (xlFree LB).length)
    {regs : Regs} {fr : Frame} {ctx : Word} {z : List GPR} (hz : ∀ r ∈ z, r ∈ xlNamed LB)
    {l : Loc} (hl : l ∈ xlLocs LB) (hres : ∀ r, l = .reg r → reserved r = false)
    (hlz : ∀ r, l = .reg r → r ∉ z) :
    rowRegisters regs fr ctx (xlTable LB) z (placeL LB l) = (read regs fr l).getD 0 := by
  cases hc : l.isCell with
  | false =>
    cases l <;> simp [Loc.isCell] at hc
    rename_i r
    have hr := hres r rfl
    have hne : r ≠ .r15 := by intro e; subst e; simp [reserved] at hr
    have h15 : (r == .r15) = false := by simpa using hne
    have hzr : z.contains r = false := by
      cases hcz : z.contains r
      · rfl
      · exact absurd (List.contains_iff_mem.1 hcz) (hlz r rfl)
    have hnone : (xlTable LB).find? (·.2 == r) = none :=
      find?_snd_none fun hm => by
        obtain ⟨p, hp, e⟩ := List.mem_map.1 hm
        exact xlFree_not_named (e ▸ xlTable_snd_free hp) (mem_xlNamed.2 hl)
    have hrz : r ∉ z := hlz r rfl
    simp [rowRegisters, placeL_reg, h15, hrz, hnone, read, hr]
  | true =>
    have hm := placeL_cell h hl hc
    have hfree := xlTable_snd_free hm
    have hne : placeL LB l ≠ .r15 := fun e => r15_not_scratch (e ▸ xlFree_scratch hfree)
    have h15 : (placeL LB l == .r15) = false := by simpa using hne
    have hzr : z.contains (placeL LB l) = false := by
      cases hcz : z.contains (placeL LB l)
      · rfl
      · exact absurd (hz _ (List.contains_iff_mem.1 hcz)) (xlFree_not_named hfree)
    simp only [rowRegisters, h15, hzr, Bool.false_eq_true, ↓reduceIte]
    rw [find?_snd_of_mem (xlTable_snd_nodup LB) hm]

/-! ## Machine arguments under a placement -/

/-- The operand positions a machine argument places (address registers
aside). -/
def _root_.IxCC.Xv.Bound.placed {σ : Type} : Bound σ → List σ
  | .input _ (.r x) => [x]
  | .output _ x => [x]
  | .tied _ a _ => [a]
  | _ => []

/-- The address registers of a bound. -/
def _root_.IxCC.Xv.Bound.addrRegs {σ : Type} : Bound σ → List σ
  | .input _ (.m am) => am.regs
  | .memory _ am => am.regs
  | _ => []

theorem Amode.toMem_rename {σ : Type} {f : σ → Option GPR} {h : σ → GPR} (am : Amode σ)
    (hf : ∀ x ∈ am.regs, f x = some (h x)) : am.toMem f = (am.map h).toMem some := by
  rcases am with ⟨base, index, disp⟩
  rcases base with _ | (b | _) <;> rcases index with _ | ⟨x, s⟩ <;>
    simp [Amode.toMem, Amode.map, Base.map, Amode.regs] at hf ⊢ <;> simp [hf]

theorem Bound.machine_rename {σ : Type} {place addr : σ → Option GPR} {h : σ → GPR} (b : Bound σ)
    (hp : ∀ x ∈ b.placed, place x = some (h x)) (ha : ∀ x ∈ b.addrRegs, addr x = some (h x)) :
    b.machine place addr = (b.map h).machine some some := by
  cases b with
  | input s a =>
    cases a with
    | r x => simp [Bound.machine, Bound.map, XArg.map, hp x (by simp [Bound.placed])]
    | m am => simp [Bound.machine, Bound.map, XArg.map, Amode.toMem_rename am ha]
    | i w => rfl
  | output s x => simp [Bound.machine, Bound.map, hp x (by simp [Bound.placed])]
  | tied s a x => simp [Bound.machine, Bound.map, hp a (by simp [Bound.placed])]
  | memory s am => simp [Bound.machine, Bound.map, Amode.toMem_rename am ha]
  | _ => rfl

theorem slotArgs_rename {σ : Type} {place addr : σ → Option GPR} {h : σ → GPR} :
    ∀ (bs : List (Bound σ)), (∀ b ∈ bs, ∀ x ∈ b.placed, place x = some (h x)) →
      (∀ b ∈ bs, ∀ x ∈ b.addrRegs, addr x = some (h x)) →
      slotArgs place addr bs = slotArgs some some (bs.map (Bound.map h))
  | [], _, _ => rfl
  | b :: bs, hp, ha => by
      rw [List.map_cons, slotArgs_cons, slotArgs_cons, Bound.isSlot_map,
        Bound.machine_rename b (hp b List.mem_cons_self) (ha b List.mem_cons_self),
        slotArgs_rename bs (fun b hb => hp b (List.mem_cons_of_mem _ hb))
          (fun b hb => ha b (List.mem_cons_of_mem _ hb))]

theorem Bound.placed_map {α β : Type} (f : α → β) (b : Bound α) : (b.map f).placed = b.placed.map f := by
  cases b with
  | input s a => cases a <;> rfl
  | _ => rfl

theorem Bound.addrRegs_map {α β : Type} (f : α → β) (b : Bound α) :
    (b.map f).addrRegs = b.addrRegs.map f := by
  cases b with
  | input s a => cases a <;> simp [Bound.addrRegs, Bound.map, XArg.map]
  | memory s m => simp [Bound.addrRegs, Bound.map]
  | _ => rfl

theorem Bound.placed_sub {α : Type} {b : Bound α} {x : α} (h : x ∈ b.placed) : x ∈ b.uses ++ b.defs := by
  cases b with
  | input s a => cases a <;> simp_all [Bound.placed, Bound.uses, XArg.regs]
  | _ => simp_all [Bound.placed, Bound.uses, Bound.defs]

theorem Bound.addrRegs_sub {α : Type} {b : Bound α} {x : α} (h : x ∈ b.addrRegs) : x ∈ b.uses := by
  cases b with
  | input s a => cases a <;> simp_all [Bound.addrRegs, Bound.uses, XArg.regs]
  | _ => simp_all [Bound.addrRegs, Bound.uses]

theorem Bound.mem_locs {b : Bound Loc} {l : Loc} : l ∈ Bound.locs b ↔ l ∈ b.uses ++ b.defs := by
  cases b with
  | input s a => cases a <;> simp [Bound.locs, Bound.uses, Bound.defs, XArg.regs]
  | tied s a x => simp [Bound.locs, Bound.uses, Bound.defs]
  | fixedTied i a x => simp [Bound.locs, Bound.uses, Bound.defs]
  | _ => simp [Bound.locs, Bound.uses, Bound.defs]

end IxCC.Xv.Xl
