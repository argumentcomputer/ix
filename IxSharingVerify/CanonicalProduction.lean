import IxSharingVerify.FamilyDomain

/-! Compiler-facing contracts for `sharing-k16-greedy-v1`. The actual
production entry supplies every domain/check premise. The unchanged old
exact routes and their stronger optimizer contracts remain under Reference. -/

namespace Ix.Sharing.Verify.CanonicalProduction

open Ix.Sharing.Exact Ix.Sharing.Family
open Ix.Sharing.Verify.UniformModel
open Ix.Sharing.Verify.SharingExact (bind_eq_ok)

theorem canonicalSharingTiered_parts {layout : ShareLayout} {limits : Limits} {roots : Array Ixon.Expr}
    {out : TieredSharingResult} (run : canonicalSharingTiered layout roots limits = .ok out) :
    ∃ expanded, expand limits #[] roots false = .ok expanded ∧
      familyExpanded canonicalFamilyConfig layout limits expanded = .ok out := by
  unfold canonicalSharingTiered at run
  obtain ⟨expanded, before, after⟩ := bind_eq_ok run
  rw [familyReferenceExpanded_eq_cached] at after
  exact ⟨expanded, before, after⟩

theorem canonicalSharingTieredTable_parts {layout : ShareLayout} {limits : Limits} {sharing roots : Array Ixon.Expr}
    {out : TieredSharingResult} (run : canonicalSharingTieredTable layout sharing roots limits = .ok out) :
    ∃ expanded, expand limits sharing roots true = .ok expanded ∧
      familyExpanded canonicalFamilyConfig layout limits expanded = .ok out := by
  unfold canonicalSharingTieredTable at run
  obtain ⟨expanded, before, after⟩ := bind_eq_ok run
  rw [familyReferenceExpanded_eq_cached] at after
  exact ⟨expanded, before, after⟩

/-- The selected production width retains its actual least family-product
witness and semantic uniform length. No exact-search success is substituted. -/
theorem canonicalSharingTiered_family_least {layout : ShareLayout} {limits : Limits} {roots : Array Ixon.Expr}
    {out : TieredSharingResult} (run : canonicalSharingTiered layout roots limits = .ok out) :
    ∃ expanded, expand limits #[] roots false = .ok expanded ∧
      ∃ width, width ∈ [1, 2, 3] ∧ ∃ delta set,
        LeastProductOutput canonicalFamilyConfig (stg width expanded).cs.size
          (initialFactors expanded (stg width expanded)) delta set ∧
        out.phase1.stored = mergeSorted (stg width expanded).cs set ∧
        UniformFinished width limits expanded out.phase1 := by
  obtain ⟨expanded, before, after⟩ := canonicalSharingTiered_parts run
  have domain := familyExpanded_domain after
  exact ⟨expanded, before, (familyExpanded_checked domain.wf domain.spines domain.roots domain.reachable after).1⟩

theorem canonicalSharingTiered_output {layout : ShareLayout} {limits : Limits} {roots : Array Ixon.Expr}
    {out : TieredSharingResult} (run : canonicalSharingTiered layout roots limits = .ok out) :
    ∃ expanded, expand limits #[] roots false = .ok expanded ∧ TieredOutput layout limits expanded out := by
  obtain ⟨expanded, before, after⟩ := canonicalSharingTiered_parts run
  exact ⟨expanded, before, familyExpanded_output_of_success after⟩

end Ix.Sharing.Verify.CanonicalProduction

namespace Ix.Sharing.Verify.CanonicalMeaning

open Ix.Sharing.Exact Ix.Sharing.Family Ix.Sharing.Verify.CanonicalProduction

/-- Production sharing preserves every ordered input root, with no new
caller premise beyond the actual successful compiler-facing API run. -/
theorem canonicalSharingTiered_meaning (layout : ShareLayout) (limits : Limits) (sources : Array Ixon.Expr)
    (result : TieredSharingResult) (ran : canonicalSharingTiered layout sources limits = .ok result) :
    SharingMeaning sources result.result.sharing result.result.roots := by
  obtain ⟨expanded, before, after⟩ := canonicalSharingTiered_parts ran
  have meaning := familyExpanded_meaning after
  rw [expand_root_terms limits sources expanded before] at meaning
  exact meaning

end Ix.Sharing.Verify.CanonicalMeaning

namespace Ix.Sharing.Verify.Tiered

open Ix.Sharing.Exact Ix.Sharing.Family Ix.Sharing.Verify.CanonicalProduction

theorem canonicalSharingTiered_format {layout : ShareLayout} {roots : Array Ixon.Expr}
    {limits : Limits} {r : TieredSharingResult} (h : canonicalSharingTiered layout roots limits = .ok r) :
    FormatOK r.result.sharing r.result.roots := by
  obtain ⟨_, _, after⟩ := canonicalSharingTiered_parts h
  exact (familyExpanded_output_of_success after).format

theorem canonicalSharingTieredTable_format {layout : ShareLayout} {sharing roots : Array Ixon.Expr}
    {limits : Limits} {r : TieredSharingResult} (h : canonicalSharingTieredTable layout sharing roots limits = .ok r) :
    FormatOK r.result.sharing r.result.roots := by
  obtain ⟨_, _, after⟩ := canonicalSharingTieredTable_parts h
  exact (familyExpanded_output_of_success after).format

theorem canonicalSharingTiered_serialized {roots : Array Ixon.Expr} {limits : Limits}
    {r : TieredSharingResult} (h : canonicalSharingTiered .tagN roots limits = .ok r) :
    r.result.variableBytes = tag0Size r.result.sharing.size +
        (r.result.sharing ++ r.result.roots).foldl (fun acc e => acc + (Ixon.serExpr e).size) 0 ∧
      r.result.modelBytes = r.result.variableBytes := by
  obtain ⟨_, _, after⟩ := canonicalSharingTiered_parts h
  exact familyExpanded_serialized after

theorem canonicalSharingTieredTable_serialized {sharing roots : Array Ixon.Expr} {limits : Limits}
    {r : TieredSharingResult} (h : canonicalSharingTieredTable .tagN sharing roots limits = .ok r) :
    r.result.variableBytes = tag0Size r.result.sharing.size +
        (r.result.sharing ++ r.result.roots).foldl (fun acc e => acc + (Ixon.serExpr e).size) 0 ∧
      r.result.modelBytes = r.result.variableBytes := by
  obtain ⟨_, _, after⟩ := canonicalSharingTieredTable_parts h
  exact familyExpanded_serialized after

end Ix.Sharing.Verify.Tiered
