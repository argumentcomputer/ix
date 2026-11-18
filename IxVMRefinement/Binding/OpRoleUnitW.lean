import IxVMRefinement.Binding.RoleUnitW
import IxVMRefinement.Binding.OpEquationObs

/-! # The operations' role unit with the family form

The step of a group whose one role is an operation, in the family form (`RoleUnitStepOverW`):
the operation's install step (`OpInstall.roleOp_step`) at `RoleOps.installed env₁ (.role r) ty
val hint`, with the walked records kept stored (`walkedStored_roleUnit`) and the stored family
map kept (`storedFamilies_roleUnit`): the record at the operation's address is a definition,
neither a block nor a projection, and the install stores the operation's key and nothing else.

* `operationRoleUnitW_of_validation`: from the operations' validation facts with the closure's
  coverage (`OpValidationFactsW`).
* `operationRoleUnitW_of_certs`: **at the link the composed fold carries**, from the
  certificates' half of the operations' validation (`OpCertFacts`), the recurrences' half being
  proved (`opEquationFacts_struct`).
-/

universe u

set_option linter.unusedVariables false

namespace IxVM.Refinement.Binding

open IxVM.Consistency
open IxVM.Refinement.Typing
open IxVM.Refinement.Typing.TwinFamily (FamilyInstalled)
open Aiur.Generic.SourceSemantics (Call)
open IxVM (F)
open Ix.Kernel.Semantics (NativeFam)

/-- **The operations' role unit with the family form, from the validation facts with the
closure's coverage.** -/
theorem operationRoleUnitW_of_validation
    {L : Ix.Kernel.Env .anon → NativeFam .anon → Prop} (hL : LinkLaws L)
    {calls : List (Call F)} (hv : OpValidationFactsW.{u} L calls) :
    AtGroups (BindingRun calls) (RoleUnitStepOverW.{u} (· ∈ RoleOps.opRoles) L) := by
  intro t ρ Rs hrun hall ht g h6 h77 r a R R₁ R' env₁ famOf₁ hgrp hop ha hadm hreads hb hadds
    hle hW hsf
  have htwf : t.wf = true := wf_of_check ht
  have hkeya : keyOf t a = Ix.Kernel.Key.role r := Core.keyOf_of_addressOf htwf ha
  have hkey_role : ∀ x, keyOf t x = Ix.Kernel.Key.role r → x = a := by
    intro x hx
    have h1 := Core.addressOf_of_keyOf htwf hx
    rw [ha] at h1
    exact (Option.some.inj h1).symm
  obtain ⟨ty₀, val₀, ty, val, tyD, valD, hint, hc, hty, hval, hrd, hsolo, hsize, hreload⟩ :=
    hv t ρ Rs hrun hrun.stepStores hall ht g r a R R₁ R' env₁ h6 h77 hgrp hop ha hadm hreads hb
      hadds hle hW
  have hB := OpInstall.roleOp_step hL hall hgrp hop ha hadm hb hadds hc hty hval hrd hsolo hsize
    hreload
  obtain ⟨cA, dA, hcA, hdA⟩ := hsolo
  have hform : ∀ c, recordOf R' a = some c → (∀ ms, c.info ≠ .muts ms) ∧ ¬ IsProj c := by
    intro c hc'
    have e : cA = c := Option.some.inj (hcA.symm.trans hc')
    rw [← e]
    refine ⟨fun ms hm => ?_, fun hp => ?_⟩
    · rw [hdA] at hm
      cases hm
    · rcases hp with ⟨_, h'⟩ | ⟨_, h'⟩ | ⟨_, h'⟩ | ⟨_, h'⟩ <;> (rw [hdA] at h'; cases h')
  have hext : ∀ ci ∈ env₁.consts, ci ∈ (RoleOps.installed env₁ (.role r) ty val hint).consts :=
    fun ci hci => List.mem_cons_of_mem _ hci
  have hnd : ((RoleOps.installed env₁ (.role r) ty val hint).consts.map (·.name)).Nodup :=
    hB.shape.reading.nodup
  have hself : (RoleOps.installed env₁ (.role r) ty val hint).find? (Ix.Kernel.Key.role r) =
      some (.defnInfo ⟨.role r, [], ty⟩ val hint) :=
    RoleOps.installed_find_self env₁ (.role r) ty val hint
  refine ⟨RoleOps.installed env₁ (.role r) ty val hint, hext, hB, ?_, ?_⟩
  · refine walkedStored_roleUnit hgrp ha hadds hW (fun k hk => ?_) ?_
    · obtain ⟨ci, hci⟩ := Option.isSome_iff_exists.mp hk
      exact Option.isSome_iff_exists.mpr ⟨ci, find_of_ext hext hnd hci⟩
    · exact Option.isSome_iff_exists.mpr ⟨_, by rw [hkeya]; exact hself⟩
  · refine storedFamilies_roleUnit hadds hb.shape.usedClosed hadm.usedClosed hform
      (fun x hx => ?_) (fun x hx => ?_) (fun rb crb hi => familyInstalled_mono hext hnd hi) hsf
    · obtain ⟨ci, hci, hn⟩ := hx
      exact ⟨ci, hext ci hci, hn⟩
    · obtain ⟨ci, hci, hn⟩ := hx
      rcases List.mem_cons.mp hci with hnew | hold
      · right
        apply hkey_role x
        rw [← hn, hnew]
        rfl
      · exact Or.inl ⟨ci, hold, hn⟩

/-- **The operations' role unit with the family form at the link the composed fold carries**,
from the certificates' half of the operations' validation. -/
theorem operationRoleUnitW_of_certs
    (hcert : ∀ calls : List (Call F), OpCertFacts.{u} calls) :
    ∀ calls : List (Call F), AtGroups (BindingRun calls)
      (RoleUnitStepOverW.{u} (· ∈ RoleOps.opRoles) Typing.FormerOpenTraceAt) :=
  fun calls => operationRoleUnitW_of_validation linkLaws_formerOpenTrace
    (opValidationFactsW_of_certs Typing.FormerOpenTraceAt (hcert calls))

end IxVM.Refinement.Binding
