import Ix.Cert.RecursorIndexFacts
import Ix.CompileCert.ReaderIndexDiscovery

/-! # Coverage of each successfully analysed recursor payload

The index may change which payload is canonical, but each scanned, successfully analysed
payload has an entry in the canonical or twin map. This does not require unique motives.
-/

namespace IxVM.Refinement.Assembly

open Ix.Kernel Ix.Kernel.Reader
open Ix.CompileCert.ReaderIndex
open Ix.CompileCert.CanonUnivMeaning (StepHolds)

private def RefCovered (ref : ConstRef _root_.Address) (index : RecIndex) : Prop :=
  index.recs.contains ref = true ∨ index.twins.contains ref = true

private theorem candidate_preserves_ref (store : Store) (owner : _root_.Address)
    (constant : Ixon.Constant) (member : Nat × Ixon.Recursor) (before : BuildState)
    (ref : ConstRef _root_.Address) (covered : RefCovered ref before.1) :
    StepHolds (fun after => RefCovered ref after.1)
      (candidate store owner constant member before) := by
  obtain ⟨after, ran, step⟩ := candidate_step store owner constant member before
  rw [ran]
  change RefCovered ref after.1
  cases step with
  | keep => exact covered
  | twin entry =>
    rcases covered with canonical | twin
    · exact Or.inl canonical
    · apply Or.inr
      change (before.1.twins.insert (.member owner member.1) entry).contains ref = true
      rw [Std.HashMap.contains_insert, twin, Bool.or_true]
  | add motive carriers major block firstIndex blockRecord members slot first =>
    rcases covered with canonical | twin
    · apply Or.inl
      rw [Ix.CompileCert.ReaderIndexDiscovery.added_recs]
      rw [Std.HashMap.contains_insert, canonical, Bool.or_true]
    · apply Or.inr
      unfold added
      dsimp only
      split <;> exact twin

private theorem candidate_ref_covered (store : Store) (owner : _root_.Address)
    (constant : Ixon.Constant) (position : Nat) (recursor : Ixon.Recursor)
    {block : _root_.Address} {motive : Nat} {carriers : Array (ConstRef _root_.Address)}
    {major : ConstRef _root_.Address}
    (analysis : Ix.Cert.recursorAnalysis? store owner constant recursor =
      some (block, motive, carriers, major)) (before : BuildState) :
    StepHolds (fun after => RefCovered (.member owner position) after.1)
      (candidate store owner constant (position, recursor) before) := by
  obtain ⟨analysed, firstIndex, blockRecord, members, slot, first,
    carrier, stored, kind, firstFound, guarded⟩ := Ix.Cert.RecursorIndex.recursorAnalysis_spec.mp analysis
  rcases before with ⟨index, found⟩
  unfold candidate
  dsimp only
  split
  · rename_i canonical
    exact Or.inl canonical
  · simp only [analysed, carrier, stored, kind, firstFound, guarded, ↓reduceIte]
    split
    · split
      · rename_i twin
        exact Or.inr twin
      · exact Or.inr (by simp)
    · split <;> exact Or.inl (by simp)

private theorem record_preserves_ref (store : Store)
    (record : _root_.Address × Ixon.Constant) (before : BuildState)
    (ref : ConstRef _root_.Address) (covered : RefCovered ref before.1) :
    StepHolds (fun after => RefCovered ref after.1) (recordStep store record before) :=
  Ix.CompileCert.CanonUnivEmit.arrayLoop_preserves
    (fun state : BuildState => RefCovered ref state.1)
    (recursorMembers record.2) before (candidate store record.1 record.2) covered
    (fun member _ state good => candidate_preserves_ref store record.1 record.2 member state ref good)

private theorem record_ref_covered (store : Store) (owner : _root_.Address)
    (constant : Ixon.Constant) (position : Nat) (recursor : Ixon.Recursor)
    (member : (position, recursor) ∈ recursorMembers constant)
    {block : _root_.Address} {motive : Nat} {carriers : Array (ConstRef _root_.Address)}
    {major : ConstRef _root_.Address}
    (analysis : Ix.Cert.recursorAnalysis? store owner constant recursor =
      some (block, motive, carriers, major)) (before : BuildState) :
    StepHolds (fun after => RefCovered (.member owner position) after.1)
      (recordStep store (owner, constant) before) := by
  apply Ix.CompileCert.ReaderIndexDiscovery.array_hit (fun _ => True)
    (fun state : BuildState => RefCovered (.member owner position) state.1)
    (recursorMembers constant) (position, recursor) member
    (candidate store owner constant) before trivial
  intro item _ state _
  obtain ⟨after, ran, _⟩ := candidate_step store owner constant item state
  refine ⟨after, ran, trivial, ?_, ?_⟩
  · intro covered
    simpa only [ran, StepHolds] using
      candidate_preserves_ref store owner constant item state (.member owner position) covered
  · intro same
    subst item
    simpa only [ran, StepHolds] using
      candidate_ref_covered store owner constant position recursor analysis state

/-- Each scanned payload with a successful filing analysis is covered under its own reference,
even when another payload is selected as canonical for its motive. -/
theorem buildIndex_ref_covered (store : Store)
    (records : Array (_root_.Address × Ixon.Constant))
    {owner : _root_.Address} {constant : Ixon.Constant} {position : Nat} {recursor : Ixon.Recursor}
    (present : (owner, constant) ∈ records)
    (member : (position, recursor) ∈ recursorMembers constant)
    {block : _root_.Address} {motive : Nat} {carriers : Array (ConstRef _root_.Address)}
    {major : ConstRef _root_.Address}
    (analysis : Ix.Cert.recursorAnalysis? store owner constant recursor =
      some (block, motive, carriers, major)) :
    ∃ entry,
      (buildIndex store records).recs[ConstRef.member owner position]? = some entry ∨
        (buildIndex store records).twins[ConstRef.member owner position]? = some entry := by
  let collected := forIn (m := Id) records (({} : RecIndex), ({} : Found)) (recordStep store)
  have collectedCovered : RefCovered (.member owner position) collected.1 := by
    apply Ix.CompileCert.ReaderIndexDiscovery.array_hit (fun _ => True)
      (fun state : BuildState => RefCovered (.member owner position) state.1)
      records (owner, constant) present (recordStep store) ({}, {}) trivial
    intro record _ state _
    refine ⟨_, rfl, trivial, ?_, ?_⟩
    · exact record_preserves_ref store record state (.member owner position)
    · intro same
      subst record
      exact record_ref_covered store owner constant position recursor member analysis state
  have completed : RefCovered (.member owner position) (buildIndex store records) := by
    rw [← run_eq]
    exact Ix.CompileCert.CanonUnivMeaning.listLoop_preserves
      (RefCovered (.member owner position)) collected.2.toList collected.1 completeStep
      collectedCovered (fun _ _ _ good => good)
  rcases completed with canonical | twin
  · rw [Std.HashMap.contains_eq_isSome_getElem?] at canonical
    obtain ⟨entry, hit⟩ := Option.isSome_iff_exists.mp canonical
    exact ⟨entry, Or.inl hit⟩
  · rw [Std.HashMap.contains_eq_isSome_getElem?] at twin
    obtain ⟨entry, hit⟩ := Option.isSome_iff_exists.mp twin
    exact ⟨entry, Or.inr hit⟩

end IxVM.Refinement.Assembly
