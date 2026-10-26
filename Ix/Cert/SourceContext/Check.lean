import Ix.Cert.SourceContext.Stores

namespace Ix.Cert.SourceContext
open Ix.Kernel Ix.Kernel.Reader Ix.Kernel.Admission Ix.CompileCert.Loop

inductive Error where
  | bytes (error : ByteError)
  | changedRows | changedTables | missingFamily

/-- Data produced by the comparison; its correctness theorem requires the
actual check run. It is not a kernel/source-reading receipt. -/
structure Compared where
  oldConstants : Ingress.Constants
  newConstants : Ingress.Constants
  oldContext : Ctx .anon
  newContext : Ctx .anon

def requiredFamilies (pre : Prelude .anon) (old next : Ingress.Constants) : Array Address :=
  RecursorSupport.families (ReaderClosureKeys.scanned old.toArray (pre.records ++ pre.evidence)).toList ++
  RecursorSupport.families (ReaderClosureKeys.scanned next.toArray (pre.records ++ pre.evidence)).toList

/-- Fixed actual inputs and construction parameters, with no arbitrary value
comparator, sampled-key list, replacement context or new support records. -/
def check (hash : ByteArray → Address) (table : RoleTable) (pre : Prelude .anon) (limits : Limits)
    (before after : Records) (blobs : Ingress.Blobs)
    (hint : ConstRef Address → Option ReducibilityHint) : Except Error Compared := do
  let rows ← (Rows.check before after).mapError .bytes
  unless rows do throw .changedRows
  let old ← (decodeRecords limits before).mapError .bytes
  let next ← (decodeRecords limits after).mapError .bytes
  let a := streamContext hash table pre old blobs hint
  let b := streamContext hash table pre next blobs hint
  unless checkTables a b do throw .changedTables
  unless (requiredFamilies pre old next).all (RecursorSupport.familyEq a.index b.index) do throw .missingFamily
  pure ⟨old,next,a,b⟩

private theorem mapError_ok {ε ε' α : Type} {f : ε → ε'} {x : Except ε α} {v : α}
    (run : x.mapError f = .ok v) : x = .ok v := by
  cases x with
  | error e => cases run
  | ok a => cases run; rfl

/-- Complete actual context agreement, decoded/input permutations, and required
family presence follow from this run. No Source read or model is assumed. -/
theorem check_sound {hash table pre limits before after blobs hint result}
    (accepted : check hash table pre limits before after blobs hint = .ok result) :
    (before.map Prod.fst).Nodup ∧ (after.map Prod.fst).Nodup ∧ before.Perm after ∧
    decodeRecords limits before = .ok result.oldConstants ∧
    decodeRecords limits after = .ok result.newConstants ∧
    result.oldConstants.Perm result.newConstants ∧
    result.oldContext = streamContext hash table pre result.oldConstants blobs hint ∧
    result.newContext = streamContext hash table pre result.newConstants blobs hint ∧
    Agrees result.oldContext result.newContext ∧
    ∀ family ∈ requiredFamilies pre result.oldConstants result.newConstants,
      RecursorSupport.FamilyAgrees result.oldContext.index result.newContext.index family := by
  unfold check at accepted
  obtain ⟨rows,rowRun,rest⟩ := except_bind_ok.mp accepted
  cases rows with
  | false => cases rest
  | true =>
    dsimp only at rest
    obtain ⟨old,oldRun,rest⟩ := except_bind_ok.mp rest
    obtain ⟨next,nextRun,rest⟩ := except_bind_ok.mp rest
    have original := mapError_ok oldRun
    have reordered := mapError_ok nextRun
    obtain ⟨oldUnique,newUnique,permutation⟩ := Rows.check_sound (mapError_ok rowRun)
    have decodedPerm := Rows.decoded_permute permutation original reordered
    have unique : (old.map Prod.fst).Nodup := by
      rw [← ((decodeRecords_ok_iff ..).mp original).keys]
      exact oldUnique
    let a := streamContext hash table pre old blobs hint
    let b := streamContext hash table pre next blobs hint
    change (do
      unless checkTables a b do throw Error.changedTables
      unless (requiredFamilies pre old next).all (RecursorSupport.familyEq a.index b.index) do throw Error.missingFamily
      pure (⟨old,next,a,b⟩ : Compared) : Except Error Compared) = Except.ok result at rest
    generalize tables : checkTables a b = tableOk at rest
    cases tableOk with
    | false => cases rest
    | true =>
      simp only [↓reduceIte] at rest
      generalize families : (requiredFamilies pre old next).all (RecursorSupport.familyEq a.index b.index) = familyOk at rest
      cases familyOk with
      | false => cases rest
      | true =>
        simp only [↓reduceIte] at rest
        cases rest
        refine ⟨oldUnique,newUnique,permutation,original,reordered,decodedPerm,rfl,rfl,?_,?_⟩
        · exact stream_agrees hash table pre blobs hint unique decodedPerm (checkTables_sound tables)
        · intro family member
          exact (RecursorSupport.familyEq_iff ..).mp ((Array.all_eq_true'.mp families) family member)

theorem checked_operations {hash table pre limits before after blobs hint result}
    (accepted : check hash table pre limits before after blobs hint = .ok result) :
    (∀ address, result.oldContext.keyAt address = result.newContext.keyAt address) ∧
    (∀ ref, result.oldContext.addressOf ref = result.newContext.addressOf ref) ∧
    (∀ ref, result.oldContext.memberKey ref = result.newContext.memberKey ref) := by
  obtain ⟨_,_,_,_,_,_,_,_,same,_⟩ := check_sound accepted
  exact ⟨same.keyAt,same.addressOf,same.memberKey⟩

theorem checked_domains {hash table pre limits before after blobs hint result}
    (accepted : check hash table pre limits before after blobs hint = .ok result) :
    (∀ a, a ∈ storeDomain pre result.oldConstants ↔ ∃ c, result.oldContext.store a = some c) ∧
    (∀ a, a ∈ storeDomain pre result.newConstants ↔ ∃ c, result.newContext.store a = some c) ∧
    (∀ a, a ∈ blobDomain pre blobs ↔ ∃ bytes, result.oldContext.blob a = some bytes) ∧
    (∀ a, a ∈ blobDomain pre blobs ↔ ∃ bytes, result.newContext.blob a = some bytes) := by
  obtain ⟨_,_,_,_,_,_,oldFrame,newFrame,_,_⟩ := check_sound accepted
  rw [oldFrame,newFrame]
  exact ⟨store_domain_iff hash table pre blobs hint _,store_domain_iff hash table pre blobs hint _,
    blob_domain_iff hash table pre blobs hint _,blob_domain_iff hash table pre blobs hint _⟩

theorem checked_absence {hash table pre limits before after blobs hint result}
    (accepted : check hash table pre limits before after blobs hint = .ok result) :
    (∀ a, a ∉ storeDomain pre result.oldConstants → result.oldContext.store a = none ∧ result.newContext.store a = none) ∧
    (∀ a, a ∉ blobDomain pre blobs → result.oldContext.blob a = none ∧ result.newContext.blob a = none) := by
  obtain ⟨_,_,_,_,_,_,oldFrame,_,same,_⟩ := check_sound accepted
  constructor
  · intro address outside
    have left : result.oldContext.store address = none := by
      rw [oldFrame]; exact store_none_outside hash table pre blobs hint _ outside
    exact ⟨left,(congrFun same.store address).symm.trans left⟩
  · intro address outside
    have left : result.oldContext.blob address = none := by
      rw [oldFrame]; exact blob_none_outside hash table pre blobs hint _ outside
    exact ⟨left,(congrFun same.blob address).symm.trans left⟩

/-- info: 'Ix.Cert.SourceContext.check_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms check_sound
/-- info: 'Ix.Cert.SourceContext.checked_operations' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms checked_operations
/-- info: 'Ix.Cert.SourceContext.checked_domains' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms checked_domains
/-- info: 'Ix.Cert.SourceContext.checked_absence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms checked_absence

end Ix.Cert.SourceContext
