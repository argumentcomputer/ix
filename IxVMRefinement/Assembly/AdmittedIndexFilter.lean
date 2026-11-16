import IxVMRefinement.Assembly.AdmittedRecSlots

/-! # The actual input filter of admitted recursor records

A hit for an input payload proves that its whole record passed the reader's input filter.
For a record outside the committed fallback, every analysed first carrier was therefore
an input family. This is kept distinct from stability of the analysis under pruning.
-/

namespace IxVM.Refinement.Assembly

open Ix.Kernel Ix.Kernel.Reader

private theorem input_known_iff (input : Array (_root_.Address × Ixon.Constant))
    (a : _root_.Address) :
    (input.foldl (fun known (key, _) => known.insert key) ({} : Std.HashSet _root_.Address)).contains a = true ↔
      a ∈ input.toList.map Prod.fst := by
  rw [← Array.foldl_toList]
  have walk : ∀ (xs : List (_root_.Address × Ixon.Constant)) (known : Std.HashSet _root_.Address),
      (xs.foldl (fun known row => known.insert row.1) known).contains a = true ↔
        known.contains a = true ∨ a ∈ xs.map Prod.fst := by
    intro xs
    induction xs with
    | nil => intro known; simp
    | cons row xs ih =>
      intro known
      rw [List.foldl_cons, ih, Std.HashSet.contains_insert, Bool.or_eq_true, beq_iff_eq]
      simp only [List.map_cons, List.mem_cons]
      constructor
      · rintro ((same | old) | later)
        · exact .inr (.inl same.symm)
        · exact .inl old
        · exact .inr (.inr later)
      · rintro (old | same | later)
        · exact .inl (.inr old)
        · exact .inl (.inl same.symm)
        · exact .inr later
  simpa using walk input.toList {}

/-- An actual hit at an input record proves that the whole record passed `inputIndexed`. -/
theorem contextOf_input_indexed {md : Mode} (table : RoleTable) (prelude : Prelude md)
    (records : Array (_root_.Address × Ixon.Constant)) (blobs : List (_root_.Address × ByteArray))
    (hint : ConstRef _root_.Address → Option ReducibilityHint)
    (reconstruct : Store → ConstRef _root_.Address → Option _root_.Address)
    (prepared : preludeFor table = .ok prelude) (keys : (records.toList.map Prod.fst).Nodup)
    {owner : _root_.Address} {constant : Ixon.Constant} {j : Nat} {entry : RecEntry}
    (present : (owner, constant) ∈ records)
    (found :
      let cx := contextOf (md := md) table records blobs (prelude.records ++ prelude.evidence)
        prelude.blobs hint reconstruct
      cx.index.recs[ConstRef.member owner j]? = some entry ∨
        cx.index.twins[ConstRef.member owner j]? = some entry) :
    let cx := contextOf (md := md) table records blobs (prelude.records ++ prelude.evidence)
      prelude.blobs hint reconstruct
    let known := records.foldl (fun known (key, _) => known.insert key) ({} : Std.HashSet _root_.Address)
    inputIndexed cx.store known (prelude.records ++ prelude.evidence) owner constant = true := by
  let cx := contextOf (md := md) table records blobs (prelude.records ++ prelude.evidence)
    prelude.blobs hint reconstruct
  have coherent := Ix.Cert.ReaderFallback.context_coherent table prelude records blobs hint
    reconstruct prepared keys
  change (buildIndex cx.store (indexedRecords cx.store records
    (prelude.records ++ prelude.evidence))).recs[ConstRef.member owner j]? = some entry ∨
    (buildIndex cx.store (indexedRecords cx.store records
      (prelude.records ++ prelude.evidence))).twins[ConstRef.member owner j]? = some entry at found
  obtain ⟨owner', constant', j', recursor, carriers, same, scanned, _, _⟩ :=
    Ix.Cert.RecursorIndex.analysis_of_from (buildIndex_any_provenance cx.store _ found)
  cases same
  have stored := coherent owner constant' (Ix.Cert.ReaderClosureKeys.mem_indexed_scanned scanned)
  have input := Ix.Cert.ReaderClosureKeys.context_input (md := md) table records
    (prelude.records ++ prelude.evidence) blobs prelude.blobs hint reconstruct keys present
  have equal := Option.some.inj (input.symm.trans stored)
  subst constant'
  simp only [indexedRecords, Array.mem_append, Array.mem_filter, Bool.and_eq_true] at scanned
  rcases scanned with ⟨_, admitted⟩ | ⟨_, absent, _⟩
  · exact admitted
  · have known := Ix.Cert.RecursorIndex.known_contains present
    rw [known] at absent
    cases absent

/-- A non-fallback input recursor can only be analysed into an input family. -/
theorem input_indexed_family {store : Store} {input fallback : Array (_root_.Address × Ixon.Constant)}
    {owner : _root_.Address} {constant : Ixon.Constant}
    (indexed : inputIndexed store
      (input.foldl (fun known (key, _) => known.insert key) ({} : Std.HashSet _root_.Address))
      fallback owner constant = true)
    (notFallback : fallback.contains (owner, constant) = false)
    {j : Nat} {recursor : Ixon.Recursor} (member : (j, recursor) ∈ recursorMembers constant)
    {motive : Nat} {carriers : Array (ConstRef _root_.Address)} {major : ConstRef _root_.Address}
    (analysis : analyseRecursor store owner constant recursor = some (motive, carriers, major))
    {family : _root_.Address} {first : Nat} (carrier : carriers[0]? = some (.member family first)) :
    ∃ familyRecord, (family, familyRecord) ∈ input := by
  rw [inputIndexed_eq] at indexed
  rcases Bool.or_eq_true_iff.mp indexed with all | fallback
  · have known := Array.all_eq_true_iff_forall_mem.mp all (j, recursor) member
    simp only [analysis, carrier] at known
    have present := (input_known_iff input family).mp known
    obtain ⟨⟨key, value⟩, row, same⟩ := List.mem_map.mp present
    dsimp only at same
    subst key
    exact ⟨value, Array.mem_toList_iff.mp row⟩
  · rw [notFallback] at fallback; cases fallback

/-- The selected admitted record really passed the whole-record input filter. -/
theorem admitted_input_indexed {V : IxVM.Refinement.View} {binding : Admission.Binding}
    (w : IxVM.Consistency.ReaderAdmissionWitness V binding)
    {owner : _root_.Address} {constant : Ixon.Constant}
    (selected : owner ∈ w.order) (record : Ix.Cert.recordAt w.env owner = some constant)
    {j : Nat} {recursor : Ixon.Recursor} (member : (j, recursor) ∈ recursorMembers constant) :
    let records := (Ix.Cert.Stream.decodedOf w.env w.order).toArray
    let cx := Admission.streamContext _root_.Address.admissionHash w.table w.prelude
      (Ix.Cert.Stream.decodedOf w.env w.order) (Ix.Cert.blobsOf w.env w.order)
      (Ix.Cert.hintsOf w.env)
    let known := records.foldl (fun known (key, _) => known.insert key) ({} : Std.HashSet _root_.Address)
    inputIndexed cx.store known (w.prelude.records ++ w.prelude.evidence) owner constant = true := by
  obtain ⟨entry, _, indexed, _⟩ := admitted_rec_analysis w selected record member
  apply contextOf_input_indexed w.table w.prelude _ _ _ _ w.preludeRead _ _ indexed
  · simpa only [List.toList_toArray] using
      (Ix.Cert.Stream.decodedOf_keys w.env w.order).nodup w.closure.nodup
  · exact Ix.Cert.RecursorIndex.mem_decoded.mpr ⟨selected, record⟩

end IxVM.Refinement.Assembly
