import IxVMRefinement.Assembly.RecursorReadFrames
import Ix.CompileCert.ReaderIndexDiscovery

/-! # Actual readings of the canonical recursor entries

Every entry in the computed canonical map occurs in its completed block shape. Reading
that inductive block therefore runs the exact indexed recursor. This uses the builder's
actual collected pairs and does not require uniqueness of raw motives across records.
-/

namespace IxVM.Refinement.Assembly

open Ix.Kernel Ix.Kernel.Reader
open Ix.CompileCert.ReaderIndex (Found recordStep)
open Ix.CompileCert.ReaderIndexDiscovery (collect_backed complete_recs complete_covers GroupContains)
open Ix.CompileCert.Loop (except_bind_ok)
open Ix.Cert.ReaderUnits (ite_ok fail_bind)

theorem buildIndex_canonical_shape (store : Store) (records : Array (_root_.Address × Ixon.Constant))
    {ref : ConstRef _root_.Address} {entry : RecEntry}
    (indexed : (buildIndex store records).recs[ref]? = some entry) :
    ∃ shape, (buildIndex store records).blocks[entry.block]? = some shape ∧ ref ∈ shape.recs := by
  let collected := forIn (m := Id) records (({} : RecIndex), ({} : Found)) (recordStep store)
  have collectedEntry : collected.1.recs[ref]? = some entry := by
    rw [← Ix.CompileCert.ReaderIndex.run_eq] at indexed
    unfold Ix.CompileCert.ReaderIndex.run at indexed
    rw [complete_recs] at indexed
    exact indexed
  have present := collect_backed store records ref entry collectedEntry
  change (entry.motive, ref) ∈ collected.2.getD entry.block #[] at present
  have completed : GroupContains entry.block ref (Ix.CompileCert.ReaderIndex.run store records) := by
    rw [Std.HashMap.getD_eq_getD_getElem?] at present
    cases stored : collected.2[entry.block]? with
    | none => simp [stored] at present
    | some pairs =>
      simp only [stored, Option.getD_some] at present
      exact complete_covers collected.2 entry.block pairs stored (entry.motive, ref) present collected.1
  rwa [Ix.CompileCert.ReaderIndex.run_eq] at completed

private theorem paired_member {α β : Type} {relation : α → β → Prop}
    {left : List α} {right : List β} (paired : List.Forall₂ relation left right)
    {entry : α} (member : entry ∈ left) : ∃ row ∈ right, relation entry row := by
  induction paired with
  | nil => cases member
  | cons head rest ih =>
    rcases List.mem_cons.mp member with rfl | later
    · exact ⟨_, List.mem_cons_self, head⟩
    · obtain ⟨row, present, frame⟩ := ih later
      exact ⟨row, List.mem_cons_of_mem _ present, frame⟩

/-- A successful full family read runs each canonical payload assigned to that family,
with its own exact entry and the actual chosen level-parameter mapping. -/
theorem readInductive_canonical_read {md : Mode} {cx : Ctx md} {state : State md}
    {records : Array (_root_.Address × Ixon.Constant)}
    (indexBuilt : cx.index = buildIndex cx.store records)
    {owner : _root_.Address} {source : Ixon.Constant} {members : Array Ixon.MutConst}
    {result : Read md} (read : readInductive cx state owner source members = .ok result)
    {ref : ConstRef _root_.Address} {entry : RecEntry}
    (indexed : cx.index.recs[ref]? = some entry) (family : entry.block = owner) :
    ∃ blockLps row, readRecursor cx blockLps ref entry = .ok row := by
  have indexedBuilt := indexed
  rw [indexBuilt] at indexedBuilt
  obtain ⟨shape, shapeFound, inShape⟩ := buildIndex_canonical_shape cx.store records indexedBuilt
  rw [← indexBuilt, family] at shapeFound
  obtain ⟨_, _, actual, _, first, block, _, actualShape, _, _, _, frames⟩ := readInductive_rec_frames read
  have same : shape = actual := by
    rw [blockShapeOf, shapeFound] at actualShape
    exact Option.some.inj actualShape
  subst actual
  obtain ⟨row, _, chosen, chosenAt, rowRead⟩ :=
    paired_member frames (Array.mem_toList_iff.mpr inShape)
  have sameEntry : chosen = entry := Option.some.inj (chosenAt.symm.trans indexed)
  subst chosen
  exact ⟨List.range first.lvls.toNat, row, rowRead⟩

theorem readRecord_inductive_canonical_read {md : Mode} {cx : Ctx md} {state : State md}
    {records : Array (_root_.Address × Ixon.Constant)}
    (indexBuilt : cx.index = buildIndex cx.store records)
    {owner : _root_.Address} {source : Ixon.Constant} {members : Array Ixon.MutConst}
    {result : Read md} (read : readRecord cx state owner source = .ok result)
    (info : source.info = .muts members)
    (hasInductive : members.any (fun | .indc _ => true | _ => false) = true)
    {ref : ConstRef _root_.Address} {entry : RecEntry}
    (indexed : cx.index.recs[ref]? = some entry) (family : entry.block = owner) :
    ∃ blockLps row, readRecursor cx blockLps ref entry = .ok row := by
  simp only [readRecord, info] at read
  split at read
  · rcases ite_ok read with failed | read
    · exact (fail_bind failed).elim
    · obtain ⟨_, familyRead, _⟩ := except_bind_ok.mp read
      exact readInductive_canonical_read indexBuilt familyRead indexed family
  · rename_i absent
    exact (absent hasInductive).elim

end IxVM.Refinement.Assembly
