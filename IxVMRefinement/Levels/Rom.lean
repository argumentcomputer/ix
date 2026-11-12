import IxVMRefinement.Levels.Bound
import IxVMRefinement.Core.Bound

/-! # A level argument of a bounded derivation is lower than the field size

The smart constructors (`level_max`, `level_imax`, `level_reduce`, `level_inst_params`) count
successors with field elements (`level_explicit_val`, `level_offset_of`) and compare the
counts. A comparison bounds what it compares, but a count that wrapped around the
characteristic would be compared wrongly, so their refinement is proved for levels lower than
the field size (`fieldSize`). This module supplies that bound from the circuit's: a level
passed to a memoized call of a bounded derivation is represented in a valid ROM, and in a
valid ROM the nodes on a longest path of a level are distinct levels, so they sit at distinct
addresses of one type, of which the field has `fieldSize` (`levelDepth_lt_of_represents`,
`arg_levelDepth_lt`). -/

namespace IxVM.Refinement.Levels

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open IxVM (F)
open IxVM.Refinement.KernelLevels
open IxVM.Consistency (MemoCallsAtMost memoCall Bounded)

/-- In a valid ROM, two level cells represented by one pointer value hold one ROM value: the
same constructor, with arguments represented by the same values. -/
theorem cells_same {rom : ROM F} (valid : rom.Valid) {h₁ h₂ : Heap F} {a₁ a₂ : Nat}
    {c₁ c₂ : String} {vs₁ vs₂ : List (SourceValue F)} {w : Value F}
    (cell₁ : h₁[a₁]? = some (.construct klevelEnum c₁ vs₁))
    (cell₂ : h₂[a₂]? = some (.construct klevelEnum c₂ vs₂))
    (w₁ : Represents rom h₁ (.ptr (.enum klevelEnum) a₁) w)
    (w₂ : Represents rom h₂ (.ptr (.enum klevelEnum) a₂) w) :
    c₁ = c₂ ∧ ∃ ws, List.Forall₂ (Represents rom h₁) vs₁ ws ∧
      List.Forall₂ (Represents rom h₂) vs₂ ws := by
  obtain ⟨b₁, ws₁, mem₁, items₁, rfl⟩ := Core.cell_represented cell₁ w₁
  obtain ⟨b₂, ws₂, mem₂, items₂, hw⟩ := Core.cell_represented cell₂ w₂
  injection hw with _ hb
  have := valid _ mem₁ _ mem₂ hb (by simp [Value.type])
  injection this with _ hc hws
  subst hws
  exact ⟨hc, ws₁, items₁, items₂⟩

/-- **In a valid ROM, a value represents at most one level.** -/
theorem rep_rom_det {rom : ROM F} (valid : rom.Valid) {h₁ h₂ : Heap F}
    {l₁ l₂ : Ix.Kernel.Level} {p₁ p₂ : SourceValue F} {w : Value F}
    (r₁ : RepKLevel h₁ l₁ p₁) (r₂ : RepKLevel h₂ l₂ p₂)
    (w₁ : Represents rom h₁ p₁ w) (w₂ : Represents rom h₂ p₂ w) : l₁ = l₂ := by
  induction r₁ generalizing l₂ p₂ w with
  | zero cell₁ =>
    cases r₂ with
    | zero _ => rfl
    | succ cell₂ _ | max cell₂ _ _ | imax cell₂ _ _ | param _ cell₂ =>
      exact absurd (cells_same valid cell₁ cell₂ w₁ w₂).1 (by decide)
  | succ cell₁ _ ih =>
    cases r₂ with
    | succ cell₂ r₂u =>
      obtain ⟨-, ws, i₁, i₂⟩ := cells_same valid cell₁ cell₂ w₁ w₂
      obtain ⟨wu, u1, hu₁, -, rfl⟩ := List.forall₂_cons_left_iff.mp i₁
      obtain ⟨hu₂, -⟩ := List.forall₂_cons.mp i₂
      rw [ih r₂u hu₁ hu₂]
    | zero cell₂ | max cell₂ _ _ | imax cell₂ _ _ | param _ cell₂ =>
      exact absurd (cells_same valid cell₁ cell₂ w₁ w₂).1 (by decide)
  | max cell₁ _ _ iha ihb =>
    cases r₂ with
    | max cell₂ r₂a r₂b =>
      obtain ⟨-, ws, i₁, i₂⟩ := cells_same valid cell₁ cell₂ w₁ w₂
      obtain ⟨wa, wb, rfl, ha₁, hb₁⟩ := Core.forall₂_pair i₁
      obtain ⟨ha₂, i₂'⟩ := List.forall₂_cons.mp i₂
      obtain ⟨hb₂, -⟩ := List.forall₂_cons.mp i₂'
      rw [iha r₂a ha₁ ha₂, ihb r₂b hb₁ hb₂]
    | zero cell₂ | succ cell₂ _ | imax cell₂ _ _ | param _ cell₂ =>
      exact absurd (cells_same valid cell₁ cell₂ w₁ w₂).1 (by decide)
  | imax cell₁ _ _ iha ihb =>
    cases r₂ with
    | imax cell₂ r₂a r₂b =>
      obtain ⟨-, ws, i₁, i₂⟩ := cells_same valid cell₁ cell₂ w₁ w₂
      obtain ⟨wa, wb, rfl, ha₁, hb₁⟩ := Core.forall₂_pair i₁
      obtain ⟨ha₂, i₂'⟩ := List.forall₂_cons.mp i₂
      obtain ⟨hb₂, -⟩ := List.forall₂_cons.mp i₂'
      rw [iha r₂a ha₁ ha₂, ihb r₂b hb₁ hb₂]
    | zero cell₂ | succ cell₂ _ | max cell₂ _ _ | param _ cell₂ =>
      exact absurd (cells_same valid cell₁ cell₂ w₁ w₂).1 (by decide)
  | param hn₁ cell₁ =>
    cases r₂ with
    | param hn₂ cell₂ =>
      obtain ⟨-, ws, i₁, i₂⟩ := cells_same valid cell₁ cell₂ w₁ w₂
      obtain ⟨wn, u1, hn₁', -, rfl⟩ := List.forall₂_cons_left_iff.mp i₁
      obtain ⟨hn₂', -⟩ := List.forall₂_cons.mp i₂
      have e₁ := represents_field_inv hn₁'
      have e₂ := represents_field_inv hn₂'
      rw [e₁] at e₂
      injection e₂ with e
      rw [natCast_lt_inj hn₁ hn₂ e]
    | zero cell₂ | succ cell₂ _ | max cell₂ _ _ | imax cell₂ _ _ =>
      exact absurd (cells_same valid cell₁ cell₂ w₁ w₂).1 (by decide)

instance : NeZero Aiur.Library.U32.Goldilocks.modulus := ⟨by decide⟩

/-- The addresses of a represented level's nodes, enough of them for its height. -/
theorem rep_rom_addrs {rom : ROM F} (valid : rom.Valid) {h : Heap F} {l : Ix.Kernel.Level}
    {p : SourceValue F} {w : Value F} (rep : RepKLevel h l p) (wr : Represents rom h p w) :
    ∃ S : Finset F, levelDepth l + 1 ≤ S.card ∧
      ∀ a ∈ S, ∃ (h' : Heap F) (l' : Ix.Kernel.Level) (p' : SourceValue F),
        RepKLevel h' l' p' ∧ Represents rom h' p' (.ptr (.enum klevelEnum) a) ∧
          levelDepth l' ≤ levelDepth l := by
  induction rep generalizing w with
  | zero cell =>
    obtain ⟨a₀, -, -, -, rfl⟩ := Core.cell_represented cell wr
    refine ⟨{a₀}, by simp [levelDepth], fun a ha => ?_⟩
    rw [Finset.mem_singleton] at ha
    subst ha
    exact ⟨_, _, _, .zero cell, wr, le_refl _⟩
  | param hn cell =>
    obtain ⟨a₀, -, -, -, rfl⟩ := Core.cell_represented cell wr
    refine ⟨{a₀}, by simp [levelDepth], fun a ha => ?_⟩
    rw [Finset.mem_singleton] at ha
    subst ha
    exact ⟨_, _, _, .param hn cell, wr, le_refl _⟩
  | @succ addr u uPtr cell repU ih =>
    obtain ⟨a₀, ws, -, items, rfl⟩ := Core.cell_represented cell wr
    obtain ⟨wu, -, hu, -, rfl⟩ := List.forall₂_cons_left_iff.mp items
    obtain ⟨S, hcard, hS⟩ := ih hu
    have hnot : a₀ ∉ S := by
      intro hmem
      obtain ⟨h', l', p', rep', wr', hd⟩ := hS a₀ hmem
      have := rep_rom_det valid (.succ cell repU) rep' wr wr'
      subst this
      simp only [levelDepth] at hd
      omega
    refine ⟨insert a₀ S, ?_, fun a ha => ?_⟩
    · rw [Finset.card_insert_of_notMem hnot]
      simp only [levelDepth]
      omega
    · rcases Finset.mem_insert.mp ha with rfl | ha
      · exact ⟨_, _, _, .succ cell repU, wr, le_refl _⟩
      · obtain ⟨h', l', p', rep', wr', hd⟩ := hS a ha
        exact ⟨h', l', p', rep', wr', by simp only [levelDepth]; omega⟩
  | @max addr a b aPtr bPtr cell repA repB iha ihb =>
    obtain ⟨a₀, ws, -, items, rfl⟩ := Core.cell_represented cell wr
    obtain ⟨wa, wb, rfl, ha, hb⟩ := Core.forall₂_pair items
    obtain ⟨SA, hcA, hSA⟩ := iha ha
    obtain ⟨SB, hcB, hSB⟩ := ihb hb
    have hnot : a₀ ∉ SA ∪ SB := by
      intro hmem
      rcases Finset.mem_union.mp hmem with hm | hm
      · obtain ⟨h', l', p', rep', wr', hd⟩ := hSA a₀ hm
        have := rep_rom_det valid (.max cell repA repB) rep' wr wr'
        subst this
        simp only [levelDepth] at hd
        omega
      · obtain ⟨h', l', p', rep', wr', hd⟩ := hSB a₀ hm
        have := rep_rom_det valid (.max cell repA repB) rep' wr wr'
        subst this
        simp only [levelDepth] at hd
        omega
    refine ⟨insert a₀ (SA ∪ SB), ?_, fun x hx => ?_⟩
    · rw [Finset.card_insert_of_notMem hnot]
      have h1 := Finset.card_le_card (Finset.subset_union_left : SA ⊆ SA ∪ SB)
      have h2 := Finset.card_le_card (Finset.subset_union_right : SB ⊆ SA ∪ SB)
      simp only [levelDepth]
      omega
    · rcases Finset.mem_insert.mp hx with rfl | hx
      · exact ⟨_, _, _, .max cell repA repB, wr, le_refl _⟩
      · rcases Finset.mem_union.mp hx with hm | hm
        · obtain ⟨h', l', p', rep', wr', hd⟩ := hSA x hm
          exact ⟨h', l', p', rep', wr', by simp only [levelDepth]; omega⟩
        · obtain ⟨h', l', p', rep', wr', hd⟩ := hSB x hm
          exact ⟨h', l', p', rep', wr', by simp only [levelDepth]; omega⟩
  | @imax addr a b aPtr bPtr cell repA repB iha ihb =>
    obtain ⟨a₀, ws, -, items, rfl⟩ := Core.cell_represented cell wr
    obtain ⟨wa, wb, rfl, ha, hb⟩ := Core.forall₂_pair items
    obtain ⟨SA, hcA, hSA⟩ := iha ha
    obtain ⟨SB, hcB, hSB⟩ := ihb hb
    have hnot : a₀ ∉ SA ∪ SB := by
      intro hmem
      rcases Finset.mem_union.mp hmem with hm | hm
      · obtain ⟨h', l', p', rep', wr', hd⟩ := hSA a₀ hm
        have := rep_rom_det valid (.imax cell repA repB) rep' wr wr'
        subst this
        simp only [levelDepth] at hd
        omega
      · obtain ⟨h', l', p', rep', wr', hd⟩ := hSB a₀ hm
        have := rep_rom_det valid (.imax cell repA repB) rep' wr wr'
        subst this
        simp only [levelDepth] at hd
        omega
    refine ⟨insert a₀ (SA ∪ SB), ?_, fun x hx => ?_⟩
    · rw [Finset.card_insert_of_notMem hnot]
      have h1 := Finset.card_le_card (Finset.subset_union_left : SA ⊆ SA ∪ SB)
      have h2 := Finset.card_le_card (Finset.subset_union_right : SB ⊆ SA ∪ SB)
      simp only [levelDepth]
      omega
    · rcases Finset.mem_insert.mp hx with rfl | hx
      · exact ⟨_, _, _, .imax cell repA repB, wr, le_refl _⟩
      · rcases Finset.mem_union.mp hx with hm | hm
        · obtain ⟨h', l', p', rep', wr', hd⟩ := hSA x hm
          exact ⟨h', l', p', rep', wr', by simp only [levelDepth]; omega⟩
        · obtain ⟨h', l', p', rep', wr', hd⟩ := hSB x hm
          exact ⟨h', l', p', rep', wr', by simp only [levelDepth]; omega⟩

/-- **A level represented in a valid ROM is lower than the field size.** -/
theorem levelDepth_lt_of_represents {rom : ROM F} (valid : rom.Valid) {h : Heap F}
    {l : Ix.Kernel.Level} {p : SourceValue F} {w : Value F}
    (rep : RepKLevel h l p) (wr : Represents rom h p w) : levelDepth l < fieldSize := by
  obtain ⟨S, hcard, -⟩ := rep_rom_addrs valid rep wr
  have hle : S.card ≤ Fintype.card F := Finset.card_le_univ S
  have hF : Fintype.card F = fieldSize := ZMod.card _
  omega

theorem forall₂_exists_of_mem {α β : Type} {R : α → β → Prop} {xs : List α} {ys : List β}
    (h : List.Forall₂ R xs ys) {x : α} (hx : x ∈ xs) : ∃ y, R x y := by
  induction h with
  | nil => cases hx
  | cons hr _ ih =>
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ⟨_, hr⟩
    · exact ih hx

/-- **A level passed to a memoized call of a bounded derivation is lower than the field
size.** -/
theorem arg_levelDepth_lt {calls : List (Call F)} (hb : Bounded calls) {c : Call F}
    (hc : c ∈ calls) (hm : memoCall IxVM.source c.name = true) {p : SourceValue F}
    (hp : p ∈ c.args) {l : Ix.Kernel.Level} (rep : RepKLevel c.heap l p) :
    levelDepth l < fieldSize := by
  obtain ⟨rom, valid, bound⟩ := hb
  obtain ⟨keys, -, cover⟩ := bound c.name hm
  obtain ⟨key, -, hfa⟩ := cover c hc rfl
  obtain ⟨w, hw⟩ := forall₂_exists_of_mem hfa hp
  exact levelDepth_lt_of_represents valid rep hw

end IxVM.Refinement.Levels
