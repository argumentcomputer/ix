import IxSharingVerify.FamilyWrapper

/-! Shared-input canonical expansion determinism. Backward-table meanings
are unique; successful ingestion supplies the complete canonicalize_det
contract, including exact interning. Previous tables may differ and contain
unreachable valid entries. Resource success and statistics are not equated. -/

namespace Ix.Sharing.FamilyPrototype

open Ix.Sharing.Exact
open Ix.Sharing.Verify.SharingExact
open Ix.Sharing.Verify.Ingestion
open Ix.Sharing.Verify.CanonicalMeaning (SharingMeaning)

theorem substShares_congr_on (source : Ixon.Expr) {P : Nat → Prop}
    {first second : Nat → Ixon.Expr} (bounded : SharesIn P source)
    (agree : ∀ index, P index → first index = second index) :
    substShares first source = substShares second source := by
  induction source with
  | share index => exact agree index.toNat bounded
  | prj type field value ih => simp only [substShares, ih bounded]
  | app fn arg ihf iha => simp only [substShares, ihf bounded.1, iha bounded.2]
  | lam contract type body iht ihb => simp only [substShares, iht bounded.1, ihb bounded.2]
  | all contract result type body iht ihb => simp only [substShares, iht bounded.1, ihb bounded.2]
  | letE contract type value body iht ihv ihb =>
    simp only [substShares, iht bounded.1, ihv bounded.2.1, ihb bounded.2.2]
  | _ => rfl

/-- Every table slot, including an unreachable one, has one interpretation.
Values of a substitution outside the table remain unrestricted. -/
theorem backward_interpretation_unique (sharing : Array Ixon.Expr) (first second : Nat → Ixon.Expr)
    (backward : ∀ index, index < sharing.size → SharesIn (· < index) sharing[index]!)
    (firstEntries : ∀ index, index < sharing.size → first index = substShares first sharing[index]!)
    (secondEntries : ∀ index, index < sharing.size → second index = substShares second sharing[index]!) :
    ∀ index, index < sharing.size → first index = second index := by
  intro index
  induction index using Nat.strongRecOn with
  | ind index ih =>
    intro bound
    rw [firstEntries index bound, secondEntries index bound]
    exact substShares_congr_on _ (backward index bound)
      (fun earlier before => ih earlier before (Nat.lt_trans before bound))

/-- The same backward table and ordered roots cannot denote two different
ordered source arrays, even when the two witnesses choose different functions. -/
theorem sharingMeaning_unique {sharing roots firstSources secondSources : Array Ixon.Expr}
    (first : SharingMeaning firstSources sharing roots) (second : SharingMeaning secondSources sharing roots) :
    firstSources = secondSources := by
  obtain ⟨sigma, firstEntries, bounded, firstRoots⟩ := first
  obtain ⟨tau, secondEntries, _, secondRoots⟩ := second
  have entries := backward_interpretation_unique sharing sigma tau
    (fun index bound => (firstEntries index bound).2)
    (fun index bound => (firstEntries index bound).1)
    (fun index bound => (secondEntries index bound).1)
  rw [← firstRoots, ← secondRoots]
  apply Array.toList_inj.mp
  simp only [Array.toList_map]
  apply List.map_congr_left
  intro root member
  exact substShares_congr_on root (bounded root (Array.mem_toList_iff.mp member)) entries

/-- Actual shared ingestion denotes the caller's ordered semantic roots.
No structural/semantic injectivity premise is supplied by the caller. -/
theorem ingestTable_meaning_eq (limits : Limits) (sharing roots sources : Array Ixon.Expr)
    (resolved ids : Array Nat) (state : IngestState)
    (meaning : SharingMeaning sources sharing roots)
    (run : (ingestTable limits sharing roots true).run {} = .ok ((resolved, ids), state)) :
    ids.map (termOf state.interner.nodes) = sources :=
  sharingMeaning_unique (tableResult_meaning (ingestTable_initial limits sharing roots true resolved ids state run)) meaning

/-- Two successful shared-input ingestions with the same ordered meaning
canonicalize identically. Unreachable valid table entries are allowed. -/
theorem canonicalize_shared_ingested (limits : Limits) (sources : Array Ixon.Expr)
    (firstSharing firstRoots secondSharing secondRoots : Array Ixon.Expr)
    (firstRefs firstIds secondRefs secondIds : Array Nat) (firstState secondState : IngestState)
    (firstMeaning : SharingMeaning sources firstSharing firstRoots)
    (secondMeaning : SharingMeaning sources secondSharing secondRoots)
    (firstRun : (ingestTable limits firstSharing firstRoots true).run {} = .ok ((firstRefs, firstIds), firstState))
    (secondRun : (ingestTable limits secondSharing secondRoots true).run {} = .ok ((secondRefs, secondIds), secondState)) :
    canonicalize firstState.interner.nodes firstIds = canonicalize secondState.interner.nodes secondIds := by
  apply canonicalize_det
    (ingestTable_run limits firstSharing firstRoots true firstRefs firstIds firstState firstRun)
    (ingestTable_run limits secondSharing secondRoots true secondRefs secondIds secondState secondRun)
  rw [ingestTable_meaning_eq limits firstSharing firstRoots sources firstRefs firstIds firstState firstMeaning firstRun,
    ingestTable_meaning_eq limits secondSharing secondRoots sources secondRefs secondIds secondState secondMeaning secondRun]

/-- Extract the real ingestion/canonicalization operations and their own
statistics. The final depth guard remains part of the successful run. -/
theorem expand_ingested_parts {limits : Limits} {sharing roots : Array Ixon.Expr} {expanded : Expanded}
    (run : expand limits sharing roots true = .ok expanded) :
    ∃ resolved ids state,
      (ingestTable limits sharing roots true).run {} = .ok ((resolved, ids), state) ∧
      canonicalize state.interner.nodes ids = .ok (expanded.dag, expanded.roots) ∧
      expanded.visits = state.visits ∧ expanded.internedNodes = state.interner.nodes.size := by
  unfold expand at run
  obtain ⟨⟨⟨resolved, ids⟩, state⟩, ingested, run⟩ := bind_eq_ok run
  obtain ⟨⟨dag, out⟩, canonical, run⟩ := bind_eq_ok run
  dsimp only at run
  split at run
  · cases run
  · cases Except.ok.inj run
    exact ⟨resolved, ids, state, ingested, canonical, rfl, rfl⟩

/-- Equal ordered meanings force the actual canonical DAG and root IDs to
agree. Both expansions must succeed at the stated limits; statistics need
not agree and no budget-independence or totality claim is made. -/
theorem expand_same_meaning {limits : Limits} {sources : Array Ixon.Expr}
    {firstSharing firstRoots secondSharing secondRoots : Array Ixon.Expr}
    {first second : Expanded}
    (firstMeaning : SharingMeaning sources firstSharing firstRoots)
    (secondMeaning : SharingMeaning sources secondSharing secondRoots)
    (firstRun : expand limits firstSharing firstRoots true = .ok first)
    (secondRun : expand limits secondSharing secondRoots true = .ok second) :
    first.dag = second.dag ∧ first.roots = second.roots := by
  obtain ⟨firstRefs, firstIds, firstState, firstIngested, firstCanonical, _, _⟩ := expand_ingested_parts firstRun
  obtain ⟨secondRefs, secondIds, secondState, secondIngested, secondCanonical, _, _⟩ := expand_ingested_parts secondRun
  have same := canonicalize_shared_ingested limits sources firstSharing firstRoots secondSharing secondRoots
    firstRefs firstIds secondRefs secondIds firstState secondState firstMeaning secondMeaning firstIngested secondIngested
  rw [firstCanonical, secondCanonical] at same
  exact Prod.mk.inj (Except.ok.inj same)

/-- Explicit equality-of-meanings form, useful when the root interpretations
were obtained independently from the two actual shared inputs. -/
theorem expand_equal_roots {limits : Limits} {firstSources secondSources : Array Ixon.Expr}
    {firstSharing firstRoots secondSharing secondRoots : Array Ixon.Expr} {first second : Expanded}
    (firstMeaning : SharingMeaning firstSources firstSharing firstRoots)
    (secondMeaning : SharingMeaning secondSources secondSharing secondRoots)
    (same : firstSources = secondSources)
    (firstRun : expand limits firstSharing firstRoots true = .ok first)
    (secondRun : expand limits secondSharing secondRoots true = .ok second) :
    first.dag = second.dag ∧ first.roots = second.roots := by
  subst secondSources
  exact expand_same_meaning firstMeaning secondMeaning firstRun secondRun

/-- In particular, re-expanding an actual normalized output recovers the
input expansion's DAG and root IDs, provided that second expansion succeeds.
This is the expansion prerequisite for later encoding/idempotence proofs. -/
theorem normalizeFamily_expansion_eq {cfg : Config} {layout : ShareLayout} {limits : Limits}
    {input output : Ixon.Constant} {result : TieredSharingResult} {first second : Expanded}
    (normalized : normalizeFamily cfg layout input limits = .ok (output, result))
    (firstRun : expand limits input.sharing (constantInfoRoots input.info) true = .ok first)
    (secondRun : expand limits output.sharing (constantInfoRoots output.info) true = .ok second) :
    first.dag = second.dag ∧ first.roots = second.roots := by
  obtain ⟨sources, before, after⟩ := normalizeFamily_meaning normalized
  exact expand_same_meaning before after firstRun secondRun

/-- The first expansion witness is taken from the real normalizer, not
assumed by a caller. A successful second expansion is still explicit. -/
theorem normalizeFamily_reexpanded {cfg : Config} {layout : ShareLayout} {limits : Limits}
    {input output : Ixon.Constant} {result : TieredSharingResult} {second : Expanded}
    (normalized : normalizeFamily cfg layout input limits = .ok (output, result))
    (secondRun : expand limits output.sharing (constantInfoRoots output.info) true = .ok second) :
    ∃ first, expand limits input.sharing (constantInfoRoots input.info) true = .ok first ∧
      first.dag = second.dag ∧ first.roots = second.roots := by
  obtain ⟨first, _, firstRun, _, _, _⟩ := normalizeFamily_parts normalized
  exact ⟨first, firstRun, normalizeFamily_expansion_eq normalized firstRun secondRun⟩

end Ix.Sharing.FamilyPrototype

#guard_kernel_axioms Ix.Sharing.FamilyPrototype.substShares_congr_on [propext]
#guard_kernel_axioms Ix.Sharing.FamilyPrototype.backward_interpretation_unique [propext]
#guard_kernel_axioms Ix.Sharing.FamilyPrototype.sharingMeaning_unique [propext, Quot.sound]
#guard_kernel_axioms Ix.Sharing.FamilyPrototype.ingestTable_meaning_eq [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Sharing.FamilyPrototype.canonicalize_shared_ingested [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Sharing.FamilyPrototype.expand_ingested_parts [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Sharing.FamilyPrototype.expand_same_meaning [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Sharing.FamilyPrototype.expand_equal_roots [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Sharing.FamilyPrototype.normalizeFamily_expansion_eq [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Sharing.FamilyPrototype.normalizeFamily_reexpanded [propext, Classical.choice, Quot.sound]
