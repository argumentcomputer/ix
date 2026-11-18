import IxVMRefinement.Binding.FamilyWitness
import IxVMRefinement.Binding.FamilyReconStore

/-! # The selected records' reconstruction form across the fold's stores

The binding fold's stored families carry, for every selected family record, the record-level
form its family check leaves it in (`FamilyRecon.RFormS`): the record is the block's family over
the flattened family derived from the block, and each recursor is the block's reconstruction at
its position. These are the transports a field `StoredFamilies.form` needs, as
`storedFamiliesFlat_*` are for `StoredFamilies.flat`:

* `storedFamiliesForm_none`: the empty map;
* `storedFamiliesForm_grow`: to a store holding the records and blobs of the first (growth, a
  role unit, store congruence);
* `storedFamiliesForm_of_sub`: from the run's store to a used-closed sub-store holding the
  selected blocks and records and the run store's blobs (the closure's group);
* `storedFamiliesForm_join`: a map selecting from two maps (the closure's join). -/

namespace IxVM.Refinement.Binding

open IxVM.Consistency

theorem storedFamiliesForm_none {t : Ix.Kernel.RoleTable} {R : Ixon.Env} :
    StoredFamiliesRForm FamilyRecon.RFormS t R (fun _ => none) :=
  fun _ _ h => nomatch h

theorem storedFamiliesForm_grow {t : Ix.Kernel.RoleTable} {R R' : Ixon.Env}
    {famOf : _root_.Address → Option _root_.Address}
    (hle : ∀ a c, recordOf R a = some c → recordOf R' a = some c)
    (hblob : ∀ x b, R.blobs.get? x = some b → R'.blobs.get? x = some b)
    (h : StoredFamiliesRForm FamilyRecon.RFormS t R famOf) :
    StoredFamiliesRForm FamilyRecon.RFormS t R' famOf :=
  fun B rb hrb => FamilyRecon.RFormS.grow hle hblob (h B rb hrb)

theorem storedFamiliesForm_of_sub {t : Ix.Kernel.RoleTable} {E₀ R : Ixon.Env}
    {famOf : _root_.Address → Option _root_.Address}
    (checked : t.check = .ok ()) (hwf : t.wf = true)
    (hsub : ∀ y c, recordOf R y = some c → recordOf E₀ y = some c) (hcl : UsedClosed R)
    (hblob : ∀ y b, E₀.blobs.get? y = some b → R.blobs.get? y = some b)
    (hheld : ∀ B rb, famOf B = some rb →
      (recordOf R B).isSome = true ∧ (recordOf R rb).isSome = true)
    (h : StoredFamiliesRForm FamilyRecon.RFormS t E₀ famOf) :
    StoredFamiliesRForm FamilyRecon.RFormS t R famOf :=
  fun B rb hrb => FamilyRecon.RFormS.of_sub checked hwf hsub hcl hblob (hheld B rb hrb).1
    (hheld B rb hrb).2 (h B rb hrb)

theorem storedFamiliesForm_join {RFormS : StoredFormPred} {t : Ix.Kernel.RoleTable}
    {R : Ixon.Env} {famOf famOf₀ fam : _root_.Address → Option _root_.Address}
    (h : StoredFamiliesRForm RFormS t R famOf) (h₀ : StoredFamiliesRForm RFormS t R famOf₀)
    (hj : ∀ B rb, fam B = some rb → famOf B = some rb ∨ famOf₀ B = some rb) :
    StoredFamiliesRForm RFormS t R fam := by
  intro B rb hrb
  rcases hj B rb hrb with h1 | h1
  · exact h B rb h1
  · exact h₀ B rb h1

end IxVM.Refinement.Binding
