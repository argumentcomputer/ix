import IxVMRefinement.Assembly.AdmittedRecCoverage

/-! # Coverage of every recursor in an admitted record

Mixed inductive records use the reader's explicit coverage check. Standalone recursors
and recursor-only records already require each payload to be canonical or a twin.
-/

namespace IxVM.Refinement.Assembly

open Ix.Kernel Ix.Kernel.Reader
open Ix.CompileCert.Loop (except_bind_ok forIn_inv_array)
open Ix.Cert.ReaderUnits (ite_ok fail_bind throw_ok)

/-- Every actual recursor in a successfully read record is covered by its real index. -/
theorem readRecord_recursors_covered {md : Mode} {cx : Ctx md} {st : State md}
    {owner : _root_.Address} {c : Ixon.Constant} {r : Read md}
    (read : readRecord cx st owner c = .ok r)
    {j : Nat} {rc : Ixon.Recursor} (member : (j, rc) ∈ recursorMembers c) :
    cx.index.recs.contains (.member owner j) = true ∨
      cx.index.twins.contains (.member owner j) = true := by
  have source := Ix.CompileCert.ReaderIndex.member_source c j rc member
  cases info : c.info with
  | recr value =>
    simp only [info] at source
    obtain ⟨rfl, rfl⟩ := source
    simp only [readRecord, info] at read
    split at read
    · exact .inl (by assumption)
    · split at read
      · rename_i entry found
        exact .inr (by rw [Std.HashMap.contains_eq_isSome_getElem?, found]; rfl)
      · exact (throw_ok read).elim
  | muts ms =>
    simp only [info] at source
    by_cases hasInductive : ms.any (fun | .indc _ => true | _ => false) = true
    · exact readRecord_inductive_recursors_covered read info hasInductive source
    · simp only [readRecord, info] at read
      split at read
      · exact (hasInductive (by assumption)).elim
      · split at read
        · split at read
          · rename_i allCanonical
            exact .inl (List.all_eq_true.mp allCanonical j
              (List.mem_range.mpr (Array.getElem?_eq_some_iff.mp source).1))
          · obtain ⟨twins, loop, _⟩ := except_bind_ok.mp read
            have covered := forIn_inv_array
              (fun processed (_ : Array (ConstRef _root_.Address × RecEntry)) =>
                ∀ k ∈ processed, cx.index.recs.contains (.member owner k) = true ∨
                  cx.index.twins.contains (.member owner k) = true) _ _
              (fun processed k suffix acc result _ previous step => by
                have extend (current : cx.index.recs.contains (.member owner k) = true ∨
                    cx.index.twins.contains (.member owner k) = true) :
                    ∀ q ∈ processed ++ [k], cx.index.recs.contains (.member owner q) = true ∨
                      cx.index.twins.contains (.member owner q) = true := by
                  intro q hq
                  rcases List.mem_append.mp hq with old | fresh
                  · exact previous q old
                  · have same : q = k := by simpa using fresh
                    simpa only [same] using current
                split at step
                · rename_i entry found
                  simp only [pure, Except.pure, Except.ok.injEq] at step
                  subst result
                  exact ⟨_, rfl, extend (.inr (by
                    rw [Std.HashMap.contains_eq_isSome_getElem?, found]; rfl))⟩
                · split at step
                  · rename_i canonical
                    simp only [pure, Except.pure, Except.ok.injEq] at step
                    subst result
                    exact ⟨_, rfl, extend (.inl canonical)⟩
                  · exact (fail_bind step).elim)
              (by simp) loop
            exact covered j (by
              simp only [List.mem_range]
              exact (Array.getElem?_eq_some_iff.mp source).1)
        · split at read
          · rename_i allDefinitions
            have invalid := Array.all_eq_true_iff_forall_mem.mp allDefinitions (.recr rc)
              (Array.mem_of_getElem? source)
            cases invalid
          · exact (throw_ok read).elim
  | _ => simp [info] at source

/-- The complete payload coverage of a selected record follows from the actual admitted
stream, including standalone and recursor-only records. -/
theorem admitted_recursors_covered {V : IxVM.Refinement.View}
    {binding : Admission.Binding} (w : IxVM.Consistency.ReaderAdmissionWitness V binding)
    {owner : _root_.Address} {c : Ixon.Constant}
    (selected : owner ∈ w.order) (record : Ix.Cert.recordAt w.env owner = some c)
    {j : Nat} {rc : Ixon.Recursor} (member : (j, rc) ∈ recursorMembers c) :
    let cx := Admission.streamContext _root_.Address.admissionHash w.table w.prelude
      (Ix.Cert.Stream.decodedOf w.env w.order) (Ix.Cert.blobsOf w.env w.order)
      (Ix.Cert.hintsOf w.env)
    cx.index.recs.contains (.member owner j) = true ∨
      cx.index.twins.contains (.member owner j) = true := by
  have decoded : (owner, c) ∈ (Ix.Cert.Stream.decodedOf w.env w.order).toArray :=
    Ix.Cert.RecursorIndex.mem_decoded.mpr ⟨selected, record⟩
  obtain ⟨_, _, read, _⟩ := (readRecords_spec w.read).mem (Array.mem_toList_iff.mpr decoded)
  exact readRecord_recursors_covered read member

/-- Every selected recursor payload has a successful filing analysis in the admitted
stream's actual context, whether its entry is canonical or a twin. -/
theorem admitted_rec_analysis {V : IxVM.Refinement.View} {binding : Admission.Binding}
    (w : IxVM.Consistency.ReaderAdmissionWitness V binding)
    {owner : _root_.Address} {c : Ixon.Constant}
    (selected : owner ∈ w.order) (record : Ix.Cert.recordAt w.env owner = some c)
    {j : Nat} {rc : Ixon.Recursor} (member : (j, rc) ∈ recursorMembers c) :
    let cx := Admission.streamContext _root_.Address.admissionHash w.table w.prelude
      (Ix.Cert.Stream.decodedOf w.env w.order) (Ix.Cert.blobsOf w.env w.order)
      (Ix.Cert.hintsOf w.env)
    ∃ entry carriers,
      (cx.index.recs[ConstRef.member owner j]? = some entry ∨
        cx.index.twins[ConstRef.member owner j]? = some entry) ∧
      Ix.Cert.recursorAnalysis? cx.store owner c rc =
        some (entry.block, entry.motive, carriers, entry.major) := by
  let records := (Ix.Cert.Stream.decodedOf w.env w.order).toArray
  let cx := Admission.streamContext _root_.Address.admissionHash w.table w.prelude
    (Ix.Cert.Stream.decodedOf w.env w.order) (Ix.Cert.blobsOf w.env w.order)
    (Ix.Cert.hintsOf w.env)
  have covered := admitted_recursors_covered w selected record member
  change cx.index.recs.contains (.member owner j) = true ∨
    cx.index.twins.contains (.member owner j) = true at covered
  have indexed : ∃ entry,
      cx.index.recs[ConstRef.member owner j]? = some entry ∨
        cx.index.twins[ConstRef.member owner j]? = some entry := by
    rcases covered with canonical | twin
    · rw [Std.HashMap.contains_eq_isSome_getElem?] at canonical
      obtain ⟨entry, found⟩ := Option.isSome_iff_exists.mp canonical
      exact ⟨entry, Or.inl found⟩
    · rw [Std.HashMap.contains_eq_isSome_getElem?] at twin
      obtain ⟨entry, found⟩ := Option.isSome_iff_exists.mp twin
      exact ⟨entry, Or.inr found⟩
  obtain ⟨entry, found⟩ := indexed
  have present : (owner, c) ∈ records := Ix.Cert.RecursorIndex.mem_decoded.mpr ⟨selected, record⟩
  have keys : (records.toList.map Prod.fst).Nodup := by
    simpa only [records, List.toList_toArray] using
      (Ix.Cert.Stream.decodedOf_keys w.env w.order).nodup w.closure.nodup
  obtain ⟨carriers, analysis⟩ := contextOf_member_analysis w.table w.prelude records
    (Ix.Cert.blobsOf w.env w.order) (Ix.Cert.hintsOf w.env)
    (Admission.projectionAddress _root_.Address.admissionHash) w.preludeRead keys present member found
  exact ⟨entry, carriers, found, analysis⟩

end IxVM.Refinement.Assembly
