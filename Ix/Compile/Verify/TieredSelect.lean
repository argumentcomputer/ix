import Ix.Compile.Verify.SharingExact
import Ix.Sharing.Exact

/-!
# Tiered construction: width selection

`canonicalTieredExpanded` runs the per-phase construction at the phase-1
widths 1, 2 and 3 and returns one of the three candidates: one with the
fewest final layout bytes (`phase3LayoutBytes`), and among those the one of
lowest width (`canonicalTiered_select`). Each candidate is exact per phase
(`TieredTier`, `TieredPhase3`); the selection is the real-byte minimum over
these three candidates only. The composition is NOT claimed to be a global
byte minimum over all tables, orders and encodings.
-/

namespace Ix.Compile.Verify.Tiered

open Ix.Sharing.Exact
open Ix.Compile.Verify.SharingExact (bind_eq_ok)

/-- A successful candidate is assembled from its three phases. -/
theorem tieredAtWidth_parts {layout : ShareLayout} {limits : Limits} {ex : Expanded} {w : Nat}
    {c : TieredSharingResult} (h : tieredAtWidth layout limits ex w = .ok c) :
    ∃ u a m, optimizeUniformExpanded w limits ex = .ok u ∧
      allocate layout limits ex.dag (graphFacts ex.dag ex.roots).deg u.result.tableTerms
        u.result.sharing u.result.roots = .ok a ∧
      rematerialize layout limits ex a.order
        (layoutBytes layout u.result.sharing u.result.roots) = .ok m ∧
      c = tieredResult layout ex w u a m := by
  unfold tieredAtWidth at h
  obtain ⟨u, hu, h⟩ := bind_eq_ok h
  obtain ⟨a, ha, h⟩ := bind_eq_ok h
  obtain ⟨m, hm, h⟩ := bind_eq_ok h
  exact ⟨u, a, m, hu, ha, hm, (Except.ok.inj h).symm⟩

/-- The candidate at width `w` reports width `w`. -/
theorem tieredAtWidth_w {layout : ShareLayout} {limits : Limits} {ex : Expanded} {w : Nat}
    {c : TieredSharingResult} (h : tieredAtWidth layout limits ex w = .ok c) : c.stats.w = w := by
  obtain ⟨u, a, m, -, -, -, rfl⟩ := tieredAtWidth_parts h
  rfl

theorem tieredBetter_iff_of_ne {a b : TieredSharingResult} (hw : a.stats.w ≠ b.stats.w) :
    tieredBetter a b = true ↔
      a.stats.phase3LayoutBytes < b.stats.phase3LayoutBytes ∨
        (a.stats.phase3LayoutBytes = b.stats.phase3LayoutBytes ∧ a.stats.w < b.stats.w) := by
  simp only [tieredBetter, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
  constructor
  · rintro (h | ⟨h1, h2 | ⟨h3, _⟩⟩)
    · exact Or.inl h
    · exact Or.inr ⟨h1, h2⟩
    · exact absurd h3 hw
  · rintro (h | ⟨h1, h2⟩)
    · exact Or.inl h
    · exact Or.inr ⟨h1, Or.inl h2⟩

/-- The chosen candidate of three with widths 1, 2, 3: it is one of them, no
candidate has fewer bytes, and every candidate with as few bytes has at least
its width. -/
theorem select_three (c₁ c₂ c₃ : TieredSharingResult) (h₁ : c₁.stats.w = 1)
    (h₂ : c₂.stats.w = 2) (h₃ : c₃.stats.w = 3) :
    let best := #[c₂, c₃].foldl (fun b c => if tieredBetter c b then c else b) c₁
    (best = c₁ ∨ best = c₂ ∨ best = c₃) ∧
      (∀ c ∈ [c₁, c₂, c₃], best.stats.phase3LayoutBytes ≤ c.stats.phase3LayoutBytes) ∧
      (∀ c ∈ [c₁, c₂, c₃], c.stats.phase3LayoutBytes = best.stats.phase3LayoutBytes →
        best.stats.w ≤ c.stats.w) := by
  intro best
  have hfold : best = (if tieredBetter c₃ (if tieredBetter c₂ c₁ then c₂ else c₁) then c₃
      else if tieredBetter c₂ c₁ then c₂ else c₁) := by
    simp [best]
  rw [hfold]
  have e₁ := tieredBetter_iff_of_ne (a := c₂) (b := c₁) (by omega)
  have e₂ := tieredBetter_iff_of_ne (a := c₃) (b := c₁) (by omega)
  have e₃ := tieredBetter_iff_of_ne (a := c₃) (b := c₂) (by omega)
  rw [h₁, h₂] at e₁
  rw [h₁, h₃] at e₂
  rw [h₂, h₃] at e₃
  have key : ∀ b : TieredSharingResult, (b = c₁ ∨ b = c₂ ∨ b = c₃) →
      (∀ c ∈ [c₁, c₂, c₃], b.stats.phase3LayoutBytes ≤ c.stats.phase3LayoutBytes) →
      (∀ c ∈ [c₁, c₂, c₃], c.stats.phase3LayoutBytes = b.stats.phase3LayoutBytes →
        b.stats.w ≤ c.stats.w) →
      (b = c₁ ∨ b = c₂ ∨ b = c₃) ∧
      (∀ c ∈ [c₁, c₂, c₃], b.stats.phase3LayoutBytes ≤ c.stats.phase3LayoutBytes) ∧
      (∀ c ∈ [c₁, c₂, c₃], c.stats.phase3LayoutBytes = b.stats.phase3LayoutBytes →
        b.stats.w ≤ c.stats.w) := fun _ a b c => ⟨a, b, c⟩
  have mem3 : ∀ (P : TieredSharingResult → Prop), P c₁ → P c₂ → P c₃ →
      ∀ c ∈ [c₁, c₂, c₃], P c := by
    intro P p1 p2 p3 c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl <;> assumption
  by_cases b₁ : tieredBetter c₂ c₁ = true
  · have f₁ := e₁.mp b₁
    rw [if_pos b₁]
    by_cases b₂ : tieredBetter c₃ c₂ = true
    · have f₂ := e₃.mp b₂
      rw [if_pos b₂]
      exact key c₃ (by simp) (mem3 _ (by omega) (by omega) (by omega))
        (mem3 _ (by rw [h₁, h₃]; omega) (by rw [h₂, h₃]; omega) (fun _ => by omega))
    · have f₂ := mt e₃.mpr b₂
      rw [if_neg b₂]
      exact key c₂ (by simp) (mem3 _ (by omega) (by omega) (by omega))
        (mem3 _ (by rw [h₁, h₂]; omega) (fun _ => by omega) (by rw [h₂, h₃]; omega))
  · have f₁ := mt e₁.mpr b₁
    rw [if_neg b₁]
    by_cases b₂ : tieredBetter c₃ c₁ = true
    · have f₂ := e₂.mp b₂
      rw [if_pos b₂]
      exact key c₃ (by simp) (mem3 _ (by omega) (by omega) (by omega))
        (mem3 _ (by rw [h₁, h₃]; omega) (by rw [h₂, h₃]; omega) (fun _ => by omega))
    · have f₂ := mt e₂.mpr b₂
      rw [if_neg b₂]
      exact key c₁ (by simp) (mem3 _ (by omega) (by omega) (by omega))
        (mem3 _ (fun _ => by omega) (by rw [h₁, h₂]; omega) (by rw [h₁, h₃]; omega))

/-- **Width selection.** The canonical tiered construction on a DAG and roots
runs the candidates at widths 1, 2 and 3 and returns one of them (with the
three final lengths recorded): no candidate has fewer final layout bytes,
and every candidate with as few bytes has at least the returned width (so
the lowest width wins a tie; the widths differ, so the `setPrec` tie-break
never decides). This is the real-byte minimum over the three candidates,
NOT a global byte minimum. -/
theorem canonicalTieredCore_select {layout : ShareLayout} {limits : Limits} {dag : Dag}
    {roots : Array Nat} {r : TieredSharingResult}
    (h : canonicalTieredCore layout limits dag roots = .ok r) :
    let ex : Expanded := { dag, roots, visits := 0, internedNodes := 0 }
    ∃ c₁ c₂ c₃, tieredAtWidth layout limits ex 1 = .ok c₁ ∧
      tieredAtWidth layout limits ex 2 = .ok c₂ ∧ tieredAtWidth layout limits ex 3 = .ok c₃ ∧
      (∃ c ∈ [c₁, c₂, c₃], r = { c with stats := { c.stats with candidateLengths :=
        #[(1, c₁.stats.phase3LayoutBytes), (2, c₂.stats.phase3LayoutBytes),
          (3, c₃.stats.phase3LayoutBytes)] } }) ∧
      (∀ c ∈ [c₁, c₂, c₃], r.stats.phase3LayoutBytes ≤ c.stats.phase3LayoutBytes) ∧
      (∀ c ∈ [c₁, c₂, c₃], c.stats.phase3LayoutBytes = r.stats.phase3LayoutBytes →
        r.stats.w ≤ c.stats.w) := by
  intro ex
  unfold canonicalTieredCore at h
  obtain ⟨c₁, hc₁, h⟩ := bind_eq_ok h
  obtain ⟨c₂, hc₂, h⟩ := bind_eq_ok h
  obtain ⟨c₃, hc₃, h⟩ := bind_eq_ok h
  have hw₁ := tieredAtWidth_w hc₁
  have hw₂ := tieredAtWidth_w hc₂
  have hw₃ := tieredAtWidth_w hc₃
  obtain ⟨hmem, hle, htie⟩ := select_three c₁ c₂ c₃ hw₁ hw₂ hw₃
  have hr := (Except.ok.inj h).symm
  refine ⟨c₁, c₂, c₃, hc₁, hc₂, hc₃,
    ⟨#[c₂, c₃].foldl (fun b c => if tieredBetter c b then c else b) c₁, ?_, ?_⟩, ?_, ?_⟩
  · rcases hmem with h' | h' | h' <;> rw [h'] <;> simp
  · rw [hr]
    simp [hw₁, hw₂, hw₃]
  · intro c hc
    rw [hr]
    exact hle c hc
  · intro c hc heq
    rw [hr] at heq ⊢
    exact htie c hc heq

/-- On an expanded input the construction is that of its DAG and roots,
with the expansion statistics recorded (the encoding, the table terms and
the candidate statistics are those of `canonicalTieredCore`). -/
theorem canonicalTiered_core {layout : ShareLayout} {limits : Limits} {ex : Expanded}
    {r : TieredSharingResult} (h : canonicalTieredExpanded layout limits ex = .ok r) :
    ∃ r₀, canonicalTieredCore layout limits ex.dag ex.roots = .ok r₀ ∧
      r = withExpansionStats ex r₀ ∧ r.stats = r₀.stats ∧
      r.result.sharing = r₀.result.sharing ∧ r.result.roots = r₀.result.roots ∧
      r.result.tableTerms = r₀.result.tableTerms ∧ r.phase1.stored = r₀.phase1.stored := by
  unfold canonicalTieredExpanded at h
  obtain ⟨r₀, hr₀, h⟩ := bind_eq_ok h
  have hr := (Except.ok.inj h).symm
  subst hr
  exact ⟨r₀, hr₀, rfl, rfl, rfl, rfl, rfl, rfl⟩

end Ix.Compile.Verify.Tiered
