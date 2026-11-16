import IxVMRefinement.Assembly.AdmittedRecursorReads
import IxVMRefinement.Assembly.AdmittedRecSlots

/-! # Actual reading of every noncanonical recursor payload

Standalone and recursor-only records use the same twin reader as mixed inductive records.
The successful record loop retains every actual twin hit. Canonical entries are kept as
the separate family-reading case, without assuming disjoint maps for an arbitrary context.
-/

namespace IxVM.Refinement.Assembly

open Ix.Kernel Ix.Kernel.Reader
open Ix.CompileCert.Loop (except_bind_ok forIn_inv_array)
open Ix.Cert.ReaderUnits (fail_bind throw_ok)

theorem readRecord_twin_read {md : Mode} {cx : Ctx md} {state : State md}
    {owner : _root_.Address} {source : Ixon.Constant} {result : Read md}
    (read : readRecord cx state owner source = .ok result)
    {slot : Nat} {recursor : Ixon.Recursor} (member : (slot, recursor) ∈ recursorMembers source)
    (notCanonical : cx.index.recs.contains (.member owner slot) = false)
    {entry : RecEntry} (indexed : cx.index.twins[ConstRef.member owner slot]? = some entry) :
    ∃ blockLps row, readRecursor cx blockLps (.member owner slot) entry = .ok row := by
  have payload := Ix.CompileCert.ReaderIndex.member_source source slot recursor member
  cases info : source.info with
  | recr value =>
    simp only [info] at payload
    obtain ⟨rfl, rfl⟩ := payload
    simp only [readRecord, info, notCanonical, Bool.false_eq_true, ↓reduceIte, indexed] at read
    exact lowerTwin_rec_read (selected := (.member owner 0, entry)) read (by simp)
  | muts members =>
    simp only [info] at payload
    by_cases hasInductive : members.any (fun | .indc _ => true | _ => false) = true
    · exact readRecord_inductive_twin_read read info hasInductive payload indexed
    · simp only [readRecord, info] at read
      split at read
      · exact (hasInductive (by assumption)).elim
      · split at read
        · split at read
          · rename_i allCanonical
            have canonical := List.all_eq_true.mp allCanonical slot
              (List.mem_range.mpr (Array.getElem?_eq_some_iff.mp payload).1)
            rw [notCanonical] at canonical
            cases canonical
          · obtain ⟨twins, loop, twinsRead⟩ := except_bind_ok.mp read
            have retained := forIn_inv_array
              (fun processed (acc : Array (ConstRef _root_.Address × RecEntry)) =>
                ∀ k ∈ processed, ∀ value, cx.index.twins[ConstRef.member owner k]? = some value →
                  (ConstRef.member owner k, value) ∈ acc) _ _
              (fun processed k suffix acc out _ previous step => by
                split at step
                · rename_i value found
                  simp only [pure, Except.pure, Except.ok.injEq] at step
                  subst out
                  refine ⟨_, rfl, ?_⟩
                  intro query present chosen lookup
                  rcases List.mem_append.mp present with old | fresh
                  · exact Array.mem_push.mpr (.inl (previous query old chosen lookup))
                  · have same : query = k := List.mem_singleton.mp fresh
                    subst query
                    have valueEq : chosen = value := Option.some.inj (lookup.symm.trans found)
                    subst chosen
                    exact Array.mem_push.mpr (.inr rfl)
                · have absent : ∀ value, cx.index.twins[ConstRef.member owner k]? = some value → False := by
                    assumption
                  split at step
                  · simp only [pure, Except.pure, Except.ok.injEq] at step
                    subst out
                    refine ⟨_, rfl, ?_⟩
                    intro query present chosen lookup
                    rcases List.mem_append.mp present with old | fresh
                    · exact previous query old chosen lookup
                    · have same : query = k := List.mem_singleton.mp fresh
                      subst query
                      exact (absent chosen lookup).elim
                  · exact (fail_bind step).elim)
              (by simp) loop
            have inTwins := retained slot (by
              simp only [List.mem_range]
              exact (Array.getElem?_eq_some_iff.mp payload).1) entry indexed
            exact lowerTwins_rec_read twinsRead inTwins
        · split at read
          · rename_i allDefinitions
            have invalid := Array.all_eq_true_iff_forall_mem.mp allDefinitions (.recr recursor)
              (Array.mem_of_getElem? payload)
            cases invalid
          · exact (throw_ok read).elim
  | _ => simp [info] at payload

/-- An actual selected payload is either canonical, to be read by its family, or has its
own successful twin reading and complete input certificate. -/
theorem admitted_rec_payload_inputs {V : IxVM.Refinement.View} {binding : Admission.Binding}
    (witness : IxVM.Consistency.ReaderAdmissionWitness V binding)
    {owner : _root_.Address} {source : Ixon.Constant}
    (selected : owner ∈ witness.order) (record : Ix.Cert.recordAt witness.env owner = some source)
    {slot : Nat} {recursor : Ixon.Recursor} (member : (slot, recursor) ∈ recursorMembers source) :
    let cx := Admission.streamContext _root_.Address.admissionHash witness.table witness.prelude
      (Ix.Cert.Stream.decodedOf witness.env witness.order) (Ix.Cert.blobsOf witness.env witness.order)
      (Ix.Cert.hintsOf witness.env)
    (∃ entry, cx.index.recs[ConstRef.member owner slot]? = some entry) ∨
      ∃ entry blockLps row, cx.index.twins[ConstRef.member owner slot]? = some entry ∧
        readRecursor cx blockLps (.member owner slot) entry = .ok row ∧
        Nonempty (RecursorReadInputs cx blockLps (.member owner slot) entry row) := by
  let cx := Admission.streamContext _root_.Address.admissionHash witness.table witness.prelude
    (Ix.Cert.Stream.decodedOf witness.env witness.order) (Ix.Cert.blobsOf witness.env witness.order)
    (Ix.Cert.hintsOf witness.env)
  have decoded : (owner, source) ∈ (Ix.Cert.Stream.decodedOf witness.env witness.order).toArray :=
    Ix.Cert.RecursorIndex.mem_decoded.mpr ⟨selected, record⟩
  obtain ⟨_, _, read, _⟩ := (readRecords_spec witness.read).mem (Array.mem_toList_iff.mpr decoded)
  by_cases canonical : cx.index.recs.contains (.member owner slot) = true
  · left
    rw [Std.HashMap.contains_eq_isSome_getElem?] at canonical
    exact Option.isSome_iff_exists.mp canonical
  · have absent : cx.index.recs.contains (.member owner slot) = false := Bool.eq_false_iff.mpr canonical
    have covered := readRecord_recursors_covered read member
    rcases covered with found | found
    · exact (canonical found).elim
    · rw [Std.HashMap.contains_eq_isSome_getElem?] at found
      obtain ⟨entry, indexed⟩ := Option.isSome_iff_exists.mp found
      obtain ⟨blockLps, row, rowRead⟩ := readRecord_twin_read read member absent indexed
      exact .inr ⟨entry, blockLps, row, indexed, rowRead, readRecursor_inputs rowRead⟩

end IxVM.Refinement.Assembly
