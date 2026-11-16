import IxVMRefinement.Assembly.RecIndexOrigins

/-! # Complete metadata of an actual recursor index entry

Canonical and twin entries retain the same payload analysis and the same level-count
comparison against the first stored inductive. Both are needed when replaying a recursor
read after rebuilding the index.
-/

namespace IxVM.Refinement.Assembly

open Ix.Kernel Ix.Kernel.Reader
open Ix.CompileCert.ReaderIndex

def RecEntryAt (store : Store) (owner : _root_.Address) (constant : Ixon.Constant)
    (recursor : Ixon.Recursor) (entry : RecEntry) : Prop :=
  ∃ carriers, Ix.Cert.recursorAnalysis? store owner constant recursor =
    some (entry.block, entry.motive, carriers, entry.major) ∧
    ∃ block members slot first,
      store entry.block = some block ∧ block.info = .muts members ∧
      (inductives members)[0]? = some (slot, first) ∧
      entry.large = (recursor.lvls.toNat == first.lvls.toNat + 1)

/-- Full entry metadata is determined by the actual stored payload and family. -/
theorem RecEntryAt.unique {store : Store} {owner : _root_.Address}
    {constant : Ixon.Constant} {recursor : Ixon.Recursor} {left right : RecEntry}
    (first : RecEntryAt store owner constant recursor left)
    (second : RecEntryAt store owner constant recursor right) : left = right := by
  rcases left with ⟨block, motive, major, large⟩
  rcases right with ⟨block', motive', major', large'⟩
  obtain ⟨carriers, analysed, record, members, slot, ind, stored, kind, found, largeEq⟩ := first
  obtain ⟨carriers', analysed', record', members', slot', ind', stored', kind', found', largeEq'⟩ := second
  have same := Option.some.inj (analysed.symm.trans analysed')
  simp only [Prod.mk.injEq] at same
  obtain ⟨rfl, rfl, rfl, rfl⟩ := same
  have sameRecord := Option.some.inj (stored.symm.trans stored')
  subst record'
  have sameMembers := Ixon.ConstantInfo.muts.inj (kind.symm.trans kind')
  subst members'
  have sameInd := congrArg Prod.snd (Option.some.inj (found.symm.trans found'))
  subst ind'
  have sameLarge := largeEq.trans largeEq'.symm
  subst large'
  rfl

/-- A computed canonical or twin hit at an actual input member determines its complete
entry, including the parent-dependent large-elimination flag. -/
theorem contextOf_member_entry {md : Mode} (table : RoleTable) (prelude : Prelude md)
    (records : Array (_root_.Address × Ixon.Constant)) (blobs : List (_root_.Address × ByteArray))
    (hint : ConstRef _root_.Address → Option ReducibilityHint)
    (reconstruct : Store → ConstRef _root_.Address → Option _root_.Address)
    (prepared : preludeFor table = .ok prelude) (keys : (records.toList.map Prod.fst).Nodup)
    {owner : _root_.Address} {constant : Ixon.Constant} {j : Nat} {recursor : Ixon.Recursor}
    (present : (owner, constant) ∈ records) (member : (j, recursor) ∈ recursorMembers constant)
    {entry : RecEntry}
    (found :
      let cx := contextOf (md := md) table records blobs (prelude.records ++ prelude.evidence)
        prelude.blobs hint reconstruct
      cx.index.recs[ConstRef.member owner j]? = some entry ∨
        cx.index.twins[ConstRef.member owner j]? = some entry) :
    let cx := contextOf (md := md) table records blobs (prelude.records ++ prelude.evidence)
      prelude.blobs hint reconstruct
    RecEntryAt cx.store owner constant recursor entry := by
  let cx := contextOf (md := md) table records blobs (prelude.records ++ prelude.evidence)
    prelude.blobs hint reconstruct
  have coherent := Ix.Cert.ReaderFallback.context_coherent table prelude records blobs hint
    reconstruct prepared keys
  change (buildIndex cx.store (indexedRecords cx.store records
    (prelude.records ++ prelude.evidence))).recs[ConstRef.member owner j]? = some entry ∨
    (buildIndex cx.store (indexedRecords cx.store records
      (prelude.records ++ prelude.evidence))).twins[ConstRef.member owner j]? = some entry at found
  obtain ⟨actualOwner, actual, position, payload, carriers, firstIndex, block,
    members, slot, ind, reference, scanned, payloadAt, analysis, carrier, stored,
    kind, firstInd, order, large⟩ := buildIndex_any_provenance cx.store _ found
  cases reference
  have storedActual := coherent owner actual (Ix.Cert.ReaderClosureKeys.mem_indexed_scanned scanned)
  have storedInput := Ix.Cert.ReaderClosureKeys.context_input (md := md) table records
    (prelude.records ++ prelude.evidence) blobs prelude.blobs hint reconstruct keys present
  have sameRecord := Option.some.inj (storedInput.symm.trans storedActual)
  subst actual
  have sameRecursor := member_unique constant j recursor payload member payloadAt
  subst payload
  exact ⟨carriers, Ix.Cert.RecursorIndex.recursorAnalysis_spec.mpr
    ⟨analysis, firstIndex, block, members, slot, ind, carrier, stored, kind, firstInd, order⟩,
    block, members, slot, ind, stored, kind, firstInd, large⟩

end IxVM.Refinement.Assembly
