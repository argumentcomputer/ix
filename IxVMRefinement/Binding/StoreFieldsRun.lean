import IxVMRefinement.Binding.StoreClausesWalk
import IxVMRefinement.RoleVal.AxiomRecordLim
import IxVMRefinement.Claim.RefSafety
import IxVMRefinement.RoleVal.BoundRecordLoad
import IxVMRefinement.Binding.BasisAt
import IxVMRefinement.Assembly.TypingBasisInv

/-! # Facts of the store sequence's run, from the observed validations

Premises of the store sequence's clauses (`IxVMRefinement.Binding.RunStores`,
`IxVMRefinement.Binding.StoreClausesWalk`) proved of a run whose roles have their observed
validations, in the alternative without a collision.

* `axiomRoles_of_run`: the record the table binds a standard axiom to is a safe axiom record of
  the run (`AxiomRolesDeclared`): the validation of the role loads the record with
  `Ingress::get_ci`, and `KernelRoles::validate_standard_axiom` matches it as an axiom and
  asserts it safe.
* `basisRows_of_run`: the run's store holds the basis rows as the basis store does
  (`BasisRowsLoaded`), at a table that pins the prelude: every basis row is the record a basis
  role is bound to or the block a projection record of one names (`basisRows_bound_or_block`,
  decided), the validation of each role loaded both (`RoleVal.ValidateRoleIn.bound_loaded`),
  and the committed rows fix the bytes. `buildAllConsts_get?_mkLazy` is the form of the run
  store's entries this needs.
-/

set_option linter.unusedVariables false

namespace IxVM.Refinement.Binding

open IxVM.Consistency
open IxVM.Refinement.Typing
open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library
open IxVM (F)

section Run

variable {calls : List (Call F)} {bAddr : _root_.Address} {t : Ix.Kernel.RoleTable}
  {E₀ : Ixon.Env}

/-- **The record a standard axiom is bound to is a safe axiom record of the run.** -/
theorem axiomRoles_of_run (hC : CollisionFreeRun calls E₀)
    (hval : ∀ g, g < 77 → ∀ r ∈ roleGroup g, RoleValidationIn calls bAddr t g r) :
    AxiomRolesDeclared t E₀ := by
  intro r hr a had
  have hv := hval (Ix.SpecDigest.groupOf r) (RoleVal.groupOf_lt_77 r) r (role_mem_roleGroup r)
  obtain ⟨a', raw, c, ax, had', hsz, hh, hblk, hde, hdeE, hinfo, hsafe⟩ :=
    RoleVal.ValidateRoleIn.axiom_record
      (show RoleVal.ValidateRoleIn calls bAddr t _ r from hv)
      ((RoleVal.specKind_three_iff r).mpr hr)
  have e : a = a' := Option.some.inj (had.symm.trans had')
  subst e
  refine ⟨c, ax, ?_, hinfo, hsafe⟩
  rw [← hblk]
  exact Claim.recordOf_hashed hC.runStore hC.hashedStored hh hsz hde hdeE

/-! ## The basis rows in the run's store -/

/-- **Every entry of the run's hashed records is a record the run hashed, under its own
bytes.** -/
theorem buildAllConsts_get?_mkLazy (calls : List (Call F)) {a : _root_.Address}
    {lc : Ixon.LazyConstant} (h : (Claim.buildAllConsts calls).get? a = some lc) :
    ∃ (bytes : ByteArray) (c : Ixon.Constant), lc = Claim.mkLazy bytes c ∧
      Hashed calls bytes ∧ Address.blake3Pure bytes = a ∧ Claim.IsCanonicalConst bytes c := by
  induction calls with
  | nil =>
    simp only [Claim.buildAllConsts, Std.HashMap.get?_eq_getElem?,
      Std.HashMap.getElem?_empty] at h
    cases h
  | cons cl cls ih =>
    simp only [Claim.buildAllConsts] at h
    split at h
    · rename_i hex
      rw [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert] at h
      split at h
      · rename_i heq
        injection h with hlc
        subst hlc
        obtain ⟨hch, hcan⟩ := Classical.choose_spec (Classical.choose_spec hex)
        exact ⟨_, _, rfl, ⟨cl, List.mem_cons_self, hch⟩, beq_iff_eq.mp heq, hcan⟩
      · rw [← Std.HashMap.get?_eq_getElem?] at h
        obtain ⟨bytes, c, hlc, hh, ha, hcan⟩ := ih h
        exact ⟨bytes, c, hlc, Claim.hashed_mono (fun _ hm => List.mem_cons_of_mem _ hm) hh, ha,
          hcan⟩
    · obtain ⟨bytes, c, hlc, hh, ha, hcan⟩ := ih h
      exact ⟨bytes, c, hlc, Claim.hashed_mono (fun _ hm => List.mem_cons_of_mem _ hm) hh, ha,
        hcan⟩

set_option maxRecDepth 100000 in
/-- **Every basis row is the record a basis role is bound to under the default table, or the
block a projection record of such a role names** (decided). -/
theorem basisRows_bound_or_block :
    StoreInhabit.basisRows.all (fun e =>
      TableInhabit.basisRoleOrder.any (fun r => ctab.addressOf? r == some e.1) ||
      TableInhabit.basisRoleOrder.any (fun r => StoreInhabit.basisRows.any (fun e' =>
        ctab.addressOf? r == some e'.1 && RoleVal.projBlockOf? e'.2 == some e.1))) = true := by
  decide +kernel

/-- **The run's store holds the basis rows as the basis store does**: the validation of every
basis role loaded the record at its bound address, which the prelude pin fixes, and with it the
block a projection record names; every basis row is one of those, and the alternative without a
collision makes the bytes the run hashed there the committed ones. -/
theorem basisRows_of_run {b : Ix.Kernel.Admission.Binding}
    (hC : CollisionFreeRun calls (Claim.runEnv b (t := t) calls)) (hpin : PreludePinned t)
    (hval : ∀ g, g < 77 → ∀ r ∈ roleGroup g, RoleValidationIn calls bAddr t g r) :
    BasisRowsLoaded (Claim.runEnv b (t := t) calls) := by
  -- bytes the run hashed at a basis row's address are the row's, and decode to its record
  have hrow_eq : ∀ {a : _root_.Address} {c : Ixon.Constant}, (a, c) ∈ StoreInhabit.basisRows →
      ∀ {bytes : ByteArray} {c' : Ixon.Constant}, Hashed calls bytes →
      Address.blake3Pure bytes = a → Ixon.deConstantExact bytes = .ok c' →
      bytes = Ixon.serConstant c ∧ c' = c := by
    intro a c hrow bytes c' hh hbl hx
    obtain ⟨hcr, hdec⟩ :=
      ClosedFacts.committedPrelude_rows (a, c) (StoreInhabit.basisRows_sub (a, c) hrow)
    have hb : bytes = Ixon.serConstant c := hC.committed (a, Ixon.serConstant c) hcr bytes hh hbl
    refine ⟨hb, ?_⟩
    rw [hb, hdec] at hx
    exact (Except.ok.inj hx).symm
  -- the run hashed canonical bytes at the address of every basis row
  have hloaded : ∀ a c, (a, c) ∈ StoreInhabit.basisRows →
      ∃ (bytes : ByteArray) (c' : Ixon.Constant), Hashed calls bytes ∧
        Address.blake3Pure bytes = a ∧ Claim.IsCanonicalConst bytes c' := by
    intro a c hrow
    have hd := List.all_eq_true.mp basisRows_bound_or_block (a, c) hrow
    simp only [Bool.or_eq_true, List.any_eq_true, Bool.and_eq_true, beq_iff_eq] at hd
    rcases hd with ⟨r, hr, hra⟩ | ⟨r, hr, e', he', hra, hpb⟩
    · have hta : t.addressOf? r = some a := (addressOf_basis hpin hr).trans hra
      obtain ⟨a', raw, c', had, hsz, hh, hbl, hx, -⟩ :=
        RoleVal.ValidateRoleIn.bound_loaded (show RoleVal.ValidateRoleIn calls bAddr t _ r from
          hval _ (RoleVal.groupOf_lt_77 r) r (role_mem_roleGroup r))
      have e : a' = a := Option.some.inj (had.symm.trans hta)
      subst e
      exact ⟨raw, c', hh, hbl, hsz, Ingress.deConstant_of_deConstantExact hx, hx⟩
    · have hta : t.addressOf? r = some e'.1 := (addressOf_basis hpin hr).trans hra
      obtain ⟨a', raw, c', had, hsz, hh, hbl, hx, hproj⟩ :=
        RoleVal.ValidateRoleIn.bound_loaded (show RoleVal.ValidateRoleIn calls bAddr t _ r from
          hval _ (RoleVal.groupOf_lt_77 r) r (role_mem_roleGroup r))
      have e : a' = e'.1 := Option.some.inj (had.symm.trans hta)
      subst e
      obtain ⟨-, hc'⟩ := hrow_eq he' hh hbl hx
      subst hc'
      obtain ⟨cb, ms, bytesB, hszB, hhB, hblB, hxB, -⟩ := hproj a hpb
      exact ⟨bytesB, cb, hhB, hblB, hszB, Ingress.deConstant_of_deConstantExact hxB, hxB⟩
  intro a lc hget
  obtain ⟨c, hrow, rfl⟩ := StoreInhabit.store_get?_inv hget
  obtain ⟨bytes, c', hh, hbl, hcan⟩ := hloaded a c hrow
  have hcont := Claim.buildAllConsts_contains_of_hashed calls hh hcan
  rw [hbl, Std.HashMap.contains_eq_isSome_getElem?] at hcont
  obtain ⟨lc', hlc'⟩ := Option.isSome_iff_exists.mp hcont
  rw [← Std.HashMap.get?_eq_getElem?] at hlc'
  obtain ⟨b0, c0, rfl, hh0, hbl0, -, -, hx0⟩ := buildAllConsts_get?_mkLazy calls hlc'
  obtain ⟨rfl, rfl⟩ := hrow_eq hrow hh0 hbl0 hx0
  exact hlc'

end Run

end IxVM.Refinement.Binding
