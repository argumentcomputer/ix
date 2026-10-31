import IxSharingVerify.NeverFails
import IxSharingVerify.SufficientBudget
import IxSharingVerify.Builder
import IxC.Kernel.Audit.Axioms

/-!
# Re-sharing a constant never fails

`normalizeConstantSharingTiered` re-shares a complete constant: it runs the
production rule on the constant's sharing table and roots, then puts the
returned roots back (`withRoots`), which refuses a different root count. The
rule returns one root per input root, so once the input expands to a
canonical DAG of fewer than `2^64` terms whose references carry fewer than
`2^64` universes, the constant is re-shared under some budget.
Under `limitsFor N` it is re-shared when its table references only earlier
entries, its roots reference only entries, and the table and the roots
together have size at most `N < 2^64`
(`normalizeConstantSharingTiered_limitsFor`).
-/

namespace Ix.Sharing.Verify.Totality

open Ix.Sharing.Exact
open Ix.Sharing.Family
open Ix.Sharing.Verify.UniformModel
open Ix.Sharing.Verify.CanonicalMeaning (expand_facts expand_correct)
open Ix.Sharing.Verify.Budget (LimitsLe Limits.join)

/-- An expansion returns one root per input root. -/
theorem expand_roots_size {limits : Limits} {sharing roots : Array Ixon.Expr} {allowShare : Bool}
    {ex : Expanded} (ran : expand limits sharing roots allowShare = .ok ex) :
    ex.roots.size = roots.size := by
  obtain ⟨_, rawIds, _, table, result⟩ := expand_correct limits sharing roots allowShare ex ran
  rw [result.size, table.rootSize]

/-- **Re-sharing a constant never fails** once its sharing table and roots
expand to a canonical DAG of fewer than `2^64` terms whose references carry
fewer than `2^64` universes. -/
theorem normalizeConstantSharingTiered_ok (layout : ShareLayout) (c : Ixon.Constant)
    {first : Limits} {ex : Expanded}
    (ran : expand first c.sharing (constantInfoRoots c.info) true = .ok ex)
    (fits : ∀ t, t < ex.dag.size → HeadFits (ex.dag.node t).head)
    (small : ex.dag.size < UInt64.size) :
    ∃ limits out, normalizeConstantSharingTiered layout c limits = .ok out := by
  have ok := expand_facts ran
  obtain ⟨second, out, h⟩ := familyExpanded_ok canonicalFamilyConfig layout ok fits small
  have checked := (familyExpanded_checked ok.wf ok.roots ok.reachable h).2
  have rootsSize : out.result.roots.size = (constantInfoRoots c.info).size := by
    rw [checked.sizes.2, expand_roots_size ran]
  obtain ⟨info', hinfo⟩ := Ix.Sharing.Verify.withRoots_ok_of_size rootsSize
  let limits := Limits.join first second
  have table : canonicalSharingTieredTable layout c.sharing (constantInfoRoots c.info) limits =
      .ok out := by
    unfold canonicalSharingTieredTable
    rw [Budget.bind_ok_eq (Budget.expand_mono (LimitsLe.join_left first second) ran),
      familyReferenceExpanded_eq_cached]
    exact Budget.familyExpanded_mono (LimitsLe.join_right first second) _ _ _ h
  refine ⟨limits, ?_⟩
  unfold normalizeConstantSharingTiered
  rw [Budget.bind_ok_eq table]
  try dsimp only
  rw [Budget.bind_ok_eq hinfo]
  exact ⟨_, rfl⟩

open Ix.Sharing.Verify.SharingExact (SharesIn) in
/-- **Re-sharing a constant succeeds under `limitsFor N`** when its table
references only earlier entries, its roots reference only entries, and the
table and the roots together have size at most `N < 2^64`; every larger
budget returns the same constant. -/
theorem normalizeConstantSharingTiered_limitsFor (layout : ShareLayout) (c : Ixon.Constant)
    (backward : ∀ k (hk : k < c.sharing.size), SharesIn (· < k) c.sharing[k])
    (rootsBack : ∀ e ∈ (constantInfoRoots c.info).toList, SharesIn (· < c.sharing.size) e)
    {N : Nat} (size : inputSize c.sharing + inputSize (constantInfoRoots c.info) ≤ N)
    (small : N < UInt64.size) {limits : Limits} (le : Budget.LimitsLe (limitsFor N) limits) :
    ∃ out, normalizeConstantSharingTiered layout c (limitsFor N) = .ok out ∧
      normalizeConstantSharingTiered layout c limits = .ok out := by
  obtain ⟨out, table⟩ := canonicalSharingTieredTable_limitsFor layout c.sharing
    (constantInfoRoots c.info) backward rootsBack size small
  have rootsSize : out.result.roots.size = (constantInfoRoots c.info).size := by
    have run := table
    unfold canonicalSharingTieredTable at run
    rw [familyReferenceExpanded_eq_cached] at run
    obtain ⟨ex, ranE, ranF⟩ := Ix.Sharing.Verify.SharingExact.bind_eq_ok run
    have ok := expand_facts ranE
    have checked := (familyExpanded_checked ok.wf ok.roots ok.reachable ranF).2
    rw [checked.sizes.2, expand_roots_size ranE]
  obtain ⟨info', hinfo⟩ := Ix.Sharing.Verify.withRoots_ok_of_size rootsSize
  have first : ∃ constant, normalizeConstantSharingTiered layout c (limitsFor N) = .ok constant := by
    unfold normalizeConstantSharingTiered
    rw [Budget.bind_ok_eq table]
    try dsimp only
    rw [Budget.bind_ok_eq hinfo]
    exact ⟨_, rfl⟩
  obtain ⟨constant, ran⟩ := first
  exact ⟨constant, ran, Budget.normalizeConstantSharingTiered_mono le layout c ran⟩

end Ix.Sharing.Verify.Totality

#guard_kernel_axioms Ix.Sharing.Verify.Totality.normalizeConstantSharingTiered_ok [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Sharing.Verify.Totality.normalizeConstantSharingTiered_limitsFor [propext, Classical.choice, Quot.sound]
