import Ix.Compile.Verify.TieredPhase3

/-!
# Tiered construction: determinism and idempotence

* `canonicalTiered_det`: the construction on an expanded input depends only
  on its canonical DAG and root IDs (the expansion statistics are recorded
  but do not influence the encoding).
* `canonicalTiered_reexpand`: the output re-expands, against the input's
  canonical DAG, to its table terms and exactly the input root IDs (it
  encodes the same terms).
* `canonicalSharingTieredTable_idem`: normalizing the output again
  reproduces it, provided expanding the output yields the same canonical DAG
  and root IDs as expanding the input. That proviso is the statement that
  canonical expansion depends only on the denoted terms; `canonicalize_det`
  proves it for the canonicalization step, while the interner's pointer
  cache (`Ix.Sharing.Exact.exprPtr`, an opaque pointer comparison) is outside what
  can be proved here, so the proviso is stated, not proved.
-/

namespace Ix.Compile.Verify.Tiered

open Ix.Sharing.Exact
open Ix.Compile.Verify.SharingExact (bind_eq_ok)

/-- The parts of a result the encoding is made of. -/
def encodingOf (r : TieredSharingResult) : Array Ixon.Expr × Array Ixon.Expr × Array Nat :=
  (r.result.sharing, r.result.roots, r.result.tableTerms)

/-- **Determinism.** Two expanded inputs with the same canonical DAG and root
IDs give the same encoding, table terms and candidate statistics. -/
theorem canonicalTiered_det {layout : ShareLayout} {limits : Limits} {fixedWidth : Option Nat}
    {ex₁ ex₂ : Expanded} (hd : ex₁.dag = ex₂.dag) (hr : ex₁.roots = ex₂.roots) :
    (canonicalTieredExpanded layout limits ex₁ fixedWidth).map (fun r => (encodingOf r, r.stats)) =
      (canonicalTieredExpanded layout limits ex₂ fixedWidth).map
        (fun r => (encodingOf r, r.stats)) := by
  unfold canonicalTieredExpanded
  rw [hd, hr]
  cases canonicalTieredCore layout limits ex₂.dag ex₂.roots fixedWidth <;> rfl

/-- The output of a candidate re-expands against the input DAG to its table
terms and the input roots. -/
theorem tieredAtWidth_reexpand {layout : ShareLayout} {limits : Limits} {ex : Expanded} {w : Nat}
    {c : TieredSharingResult} (h : tieredAtWidth layout limits ex w = .ok c) :
    ∃ k, reexpand limits ex.dag c.result.sharing c.result.roots =
      .ok (c.result.tableTerms, ex.roots, k) := by
  obtain ⟨u, a, m, -, -, hm, rfl⟩ := tieredAtWidth_parts h
  obtain ⟨_, -, -, hre, -⟩ := rematerialize_parts hm
  exact hre

/-- **Round trip.** The output of the tiered construction re-expands,
against the input's canonical DAG, to its table terms and exactly the input
root IDs: it encodes the input's terms. -/
theorem canonicalTiered_reexpand {layout : ShareLayout} {limits : Limits} {ex : Expanded}
    {fixedWidth : Option Nat} {r : TieredSharingResult}
    (h : canonicalTieredExpanded layout limits ex fixedWidth = .ok r) :
    ∃ k, reexpand limits ex.dag r.result.sharing r.result.roots =
      .ok (r.result.tableTerms, ex.roots, k) := by
  obtain ⟨r₀, hr₀, rfl, -, -, -, -, -⟩ := canonicalTiered_core h
  show ∃ k, reexpand limits ex.dag r₀.result.sharing r₀.result.roots =
    .ok (r₀.result.tableTerms, ex.roots, k)
  have hcand : ∀ (w : Nat) (c : TieredSharingResult),
      tieredAtWidth layout limits ⟨ex.dag, ex.roots, 0, 0⟩ w = .ok c →
      ∃ k, reexpand limits ex.dag c.result.sharing c.result.roots =
        .ok (c.result.tableTerms, ex.roots, k) :=
    fun w c hc => tieredAtWidth_reexpand (ex := ⟨ex.dag, ex.roots, 0, 0⟩) hc
  cases fixedWidth with
  | some w => exact hcand w r₀ hr₀
  | none =>
    obtain ⟨c₁, c₂, c₃, h₁, h₂, h₃, ⟨c, hc, hrc⟩, -, -⟩ := canonicalTieredCore_select hr₀
    have hres : r₀.result = c.result := by rw [hrc]
    rw [hres]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with hc | hc | hc <;> rw [hc]
    · exact hcand 1 c₁ h₁
    · exact hcand 2 c₂ h₂
    · exact hcand 3 c₃ h₃

/-- **Idempotence.** If expanding the output yields the same canonical DAG
and root IDs as expanding the input, normalizing the output reproduces its
sharing table, roots and table terms. -/
theorem canonicalSharingTieredTable_idem {layout : ShareLayout} {limits : Limits}
    {fixedWidth : Option Nat} {sharing roots : Array Ixon.Expr} {r : TieredSharingResult}
    {ex ex' : Expanded}
    (h : canonicalSharingTieredTable layout sharing roots limits fixedWidth = .ok r)
    (hex : expand limits sharing roots true = .ok ex)
    (hex' : expand limits r.result.sharing r.result.roots true = .ok ex')
    (hd : ex'.dag = ex.dag) (hr : ex'.roots = ex.roots) :
    ∃ r', canonicalSharingTieredTable layout r.result.sharing r.result.roots limits fixedWidth =
        .ok r' ∧ encodingOf r' = encodingOf r ∧ r'.stats = r.stats := by
  unfold canonicalSharingTieredTable at h ⊢
  rw [hex] at h
  rw [hex']
  change canonicalTieredExpanded layout limits ex fixedWidth = .ok r at h
  change ∃ r', canonicalTieredExpanded layout limits ex' fixedWidth = .ok r' ∧ _
  have hdet := canonicalTiered_det (layout := layout) (limits := limits)
    (fixedWidth := fixedWidth) hd hr
  rw [h] at hdet
  cases h' : canonicalTieredExpanded layout limits ex' fixedWidth with
  | error e => rw [h'] at hdet; cases hdet
  | ok r' =>
    rw [h'] at hdet
    simp only [Except.map, Except.ok.injEq, Prod.mk.injEq] at hdet
    exact ⟨r', rfl, hdet.1, hdet.2⟩

end Ix.Compile.Verify.Tiered
