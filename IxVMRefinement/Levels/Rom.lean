import Ix.IxVM.Refinement.KernelLevels
import Ix.IxVM.Consistency.Statement
import Mathlib.Data.List.Forall2

/-! # A level a bounded derivation handles is lower than `2^39`

The smart constructors (`level_max`, `level_imax`, `level_reduce`, `level_inst_params`) count
successors with field elements (`level_explicit_val`, `level_offset_of`), and the normalizer
of `level_leq` and `level_equal` counts them in its offsets. A comparison bounds what it
compares, but a count that wrapped around the characteristic would be compared, or stored,
wrongly. What bounds the counts is the trace's memory: a bounded derivation's calls are
carried by a valid ROM of at most `2^39` addresses (`IxVM.Consistency.Bounded`), and in a
valid ROM the nodes on a longest path of a represented level are distinct levels, hence sit at
pairwise different addresses (`rep_rom_det`, `rep_rom_addrs`). So a level any call of a
bounded derivation receives is lower than `2^39` (`levelDepth_lt_of_rom`,
`arg_levelDepth_lt`), and every count of its successors is below that. -/

namespace IxVM.Refinement.Levels

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open IxVM (F)
open IxVM.Refinement.KernelLevels
open IxVM.Consistency (ROMAddressesAtMost Bounded)

/-! ## Reading represented values -/

theorem represents_ptr_inv {rom : ROM F} {h : Heap F} {t : Aiur.Ty} {loc : Nat} {w : Value F}
    (r : Represents rom h (.ptr t loc) w) :
    ∃ stored address encoded, h[loc]? = some stored ∧ (address, encoded) ∈ rom.entries ∧
      Represents rom h stored encoded ∧ w = .ptr encoded.type address := by
  generalize hp : (Value.ptr t loc : SourceValue F) = p at r
  cases r with
  | ptr source cell contents =>
    injection hp with _ hl
    subst hl
    exact ⟨_, _, _, source, cell, contents, rfl⟩
  | field => cases hp
  | tuple _ => cases hp
  | construct _ => cases hp

theorem represents_construct_inv {rom : ROM F} {h : Heap F} {e c : String}
    {vs : List (SourceValue F)} {w : Value F} (r : Represents rom h (.construct e c vs) w) :
    ∃ ws, w = .construct e c ws ∧ List.Forall₂ (Represents rom h) vs ws := by
  generalize hp : (Value.construct e c vs : SourceValue F) = p at r
  cases r with
  | construct items =>
    injection hp with h1 h2 h3
    subst h1 h2 h3
    exact ⟨_, rfl, items⟩
  | field => cases hp
  | tuple _ => cases hp
  | ptr _ _ _ => cases hp

theorem represents_field_inv {rom : ROM F} {h : Heap F} {x : F} {w : Value F}
    (r : Represents rom h (.field x) w) : w = .field x := by
  generalize hp : (Value.field x : SourceValue F) = p at r
  cases r with
  | field =>
    injection hp with hx
    rw [hx]
  | tuple _ => cases hp
  | construct _ => cases hp
  | ptr _ _ _ => cases hp

theorem forall₂_pair {α β : Type} {R : α → β → Prop} {a b : α} {ws : List β}
    (h : List.Forall₂ R [a, b] ws) : ∃ wa wb, ws = [wa, wb] ∧ R a wa ∧ R b wb := by
  obtain ⟨wa, u, ha, hu, rfl⟩ := List.forall₂_cons_left_iff.mp h
  obtain ⟨wb, u', hb, hu', rfl⟩ := List.forall₂_cons_left_iff.mp hu
  rw [List.forall₂_nil_left_iff] at hu'
  subst hu'
  exact ⟨wa, wb, rfl, ha, hb⟩

/-- The ROM value a represented level cell is stored as. -/
theorem cell_represented {rom : ROM F} {h : Heap F} {en c : String} {addr : Nat}
    {vs : List (SourceValue F)} {w : Value F}
    (cell : h[addr]? = some (.construct en c vs)) (r : Represents rom h (.ptr (.enum en) addr) w) :
    ∃ address ws, (address, .construct en c ws) ∈ rom.entries ∧
      List.Forall₂ (Represents rom h) vs ws ∧ w = .ptr (.enum en) address := by
  obtain ⟨stored, address, encoded, src, mem, rep, rfl⟩ := represents_ptr_inv r
  rw [cell] at src
  cases src
  obtain ⟨ws, rfl, items⟩ := represents_construct_inv rep
  exact ⟨address, ws, mem, items, by simp [Value.type]⟩

/-! ## Distinct levels, distinct addresses -/

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
  obtain ⟨b₁, ws₁, mem₁, items₁, rfl⟩ := cell_represented cell₁ w₁
  obtain ⟨b₂, ws₂, mem₂, items₂, hw⟩ := cell_represented cell₂ w₂
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
      obtain ⟨wa, wb, rfl, ha₁, hb₁⟩ := forall₂_pair i₁
      obtain ⟨ha₂, i₂'⟩ := List.forall₂_cons.mp i₂
      obtain ⟨hb₂, -⟩ := List.forall₂_cons.mp i₂'
      rw [iha r₂a ha₁ ha₂, ihb r₂b hb₁ hb₂]
    | zero cell₂ | succ cell₂ _ | imax cell₂ _ _ | param _ cell₂ =>
      exact absurd (cells_same valid cell₁ cell₂ w₁ w₂).1 (by decide)
  | imax cell₁ _ _ iha ihb =>
    cases r₂ with
    | imax cell₂ r₂a r₂b =>
      obtain ⟨-, ws, i₁, i₂⟩ := cells_same valid cell₁ cell₂ w₁ w₂
      obtain ⟨wa, wb, rfl, ha₁, hb₁⟩ := forall₂_pair i₁
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


/-- The addresses of a represented level's nodes, enough of them for its height. -/
theorem rep_rom_addrs {rom : ROM F} (valid : rom.Valid) {h : Heap F} {l : Ix.Kernel.Level}
    {p : SourceValue F} {w : Value F} (rep : RepKLevel h l p) (wr : Represents rom h p w) :
    ∃ S : Finset F, levelDepth l + 1 ≤ S.card ∧
      ∀ a ∈ S, ∃ (h' : Heap F) (l' : Ix.Kernel.Level) (p' : SourceValue F),
        RepKLevel h' l' p' ∧ Represents rom h' p' (.ptr (.enum klevelEnum) a) ∧
          levelDepth l' ≤ levelDepth l := by
  induction rep generalizing w with
  | zero cell =>
    obtain ⟨a₀, -, -, -, rfl⟩ := cell_represented cell wr
    refine ⟨{a₀}, by simp [levelDepth], fun a ha => ?_⟩
    rw [Finset.mem_singleton] at ha
    subst ha
    exact ⟨_, _, _, .zero cell, wr, le_refl _⟩
  | param hn cell =>
    obtain ⟨a₀, -, -, -, rfl⟩ := cell_represented cell wr
    refine ⟨{a₀}, by simp [levelDepth], fun a ha => ?_⟩
    rw [Finset.mem_singleton] at ha
    subst ha
    exact ⟨_, _, _, .param hn cell, wr, le_refl _⟩
  | @succ addr u uPtr cell repU ih =>
    obtain ⟨a₀, ws, -, items, rfl⟩ := cell_represented cell wr
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
    obtain ⟨a₀, ws, -, items, rfl⟩ := cell_represented cell wr
    obtain ⟨wa, wb, rfl, ha, hb⟩ := forall₂_pair items
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
    obtain ⟨a₀, ws, -, items, rfl⟩ := cell_represented cell wr
    obtain ⟨wa, wb, rfl, ha, hb⟩ := forall₂_pair items
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

/-- **A level represented in a valid ROM of at most `N` addresses is lower than `N`.** -/
theorem levelDepth_lt_of_rom {rom : ROM F} (valid : rom.Valid) {N : Nat}
    (bound : ROMAddressesAtMost rom N) {h : Heap F} {l : Ix.Kernel.Level} {p : SourceValue F}
    {w : Value F} (rep : RepKLevel h l p) (wr : Represents rom h p w) : levelDepth l < N := by
  obtain ⟨S, hcard, hS⟩ := rep_rom_addrs valid rep wr
  obtain ⟨addrs, small, cover⟩ := bound
  have hsub : S ⊆ addrs.toFinset := by
    intro a ha
    obtain ⟨h', l', p', rep', wr', -⟩ := hS a ha
    obtain ⟨addr', rfl⟩ := rep'.isPtr
    obtain ⟨-, address, encoded, -, mem, -, hw⟩ := represents_ptr_inv wr'
    injection hw with _ ha'
    rw [List.mem_toFinset, ha']
    exact cover _ mem
  have h1 := Finset.card_le_card hsub
  have h2 := List.toFinset_card_le addrs
  omega

/-- **A level any call of a bounded derivation receives is lower than `2^39`.** -/
theorem arg_levelDepth_lt {calls : List (Call F)} (hb : Bounded calls) {c : Call F}
    (hc : c ∈ calls) {p : SourceValue F} (hp : p ∈ c.args) {l : Ix.Kernel.Level}
    (rep : RepKLevel c.heap l p) : levelDepth l < 2 ^ 39 := by
  obtain ⟨rom, valid, bound, carried⟩ := hb
  obtain ⟨w, hw⟩ := carried c hc p hp
  exact levelDepth_lt_of_rom valid bound rep hw

/-- The same, against the field size (the bound the smart constructors are proved under). -/
theorem arg_levelDepth_lt_field {calls : List (Call F)} (hb : Bounded calls) {c : Call F}
    (hc : c ∈ calls) {p : SourceValue F} (hp : p ∈ c.args) {l : Ix.Kernel.Level}
    (rep : RepKLevel c.heap l p) : levelDepth l < fieldSize :=
  lt_trans (arg_levelDepth_lt hb hc hp rep) (by decide)

/-- A sub-derivation of a bounded derivation is bounded. -/
theorem bounded_sub {calls₁ calls₂ : List (Call F)} (hb : Bounded calls₂)
    (hsub : ∀ x ∈ calls₁, x ∈ calls₂) : Bounded calls₁ := by
  obtain ⟨rom, valid, bound, carried⟩ := hb
  exact ⟨rom, valid, bound, fun c hc => carried c (hsub c hc)⟩

end IxVM.Refinement.Levels
