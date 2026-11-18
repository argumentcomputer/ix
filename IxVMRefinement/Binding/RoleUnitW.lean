import IxVMRefinement.Binding.FoldFamily
import IxVMRefinement.Binding.AxiomValidation

/-! # The role units with the family form

A role unit (an operation or a standard axiom) installs one record, at the role's address `a`,
after the group's closure: the store grows from the closure's `R₁` to `R'` by that record
(`AddsAt R₁ R' a`) and the environment from `env₁` to `env'` by the role's constant. The family
form asks the step to keep the walked records stored and the stored family map
(`RoleUnitStepOverW`). Both follow from the step's own facts:

* `walkedStored_roleUnit`: the walked records stored on the groups up to `g`, at `R'` and `env'`,
  if `env'` keeps every successful lookup of `env₁` and stores the key of `a`. The new record is
  at `a`; the other records are those of `R₁`; the only walked role of `g` is the unit's own.
* `storedFamilies_roleUnit`: the same family map stored at `R'` and `env'`, if the record at `a`
  is neither a block nor a projection, and `env'` stores what `env₁` does and nothing else but
  the key of `a`. A block the grown store routes as modeled is not at `a`, its record and route
  are those of `R₁` (the closure's store is closed under what its records use, so every address
  the route reads is held by `R₁`, with the same record in `R'`), and its constant addresses are
  not `a` (they are projection records).
* `standardAxiomRoleUnitW_of_validation`, `standardAxiomRoleUnitW_closed`: **the standard axioms'
  role unit with the family form**, from the axiom's observed validation
  (`AxiomInstall.AxiomValidationFacts`, proved by `axiomValidationFacts`), with no premise. The
  record at `a` is an axiom record; the environment is the closure's with the axiom stored at its
  role key, or the closure's itself where it already stores that key.

The operations' role unit with the family form is the same two lemmas over the operation's
install (`RoleOps.installed env₁ (.role r) ty val hint`, the record a definition), from the
operation's validation facts with the closure's coverage handed (`OpValidationFactsW`).
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

/-! ## The two facts after a role unit -/

/-- **The walked records stored after a role unit** (module docstring). -/
theorem walkedStored_roleUnit {ρ : BRun} {t : Ix.Kernel.RoleTable} {g : Nat}
    {r : Ix.Kernel.Role} {a : _root_.Address} {R₁ R' : Ixon.Env}
    {env₁ env' : Ix.Kernel.Env .anon} (hgrp : roleGroup g = [r]) (ha : t.addressOf? r = some a)
    (hadds : AddsAt R₁ R' a) (hW : WalkedStored ρ t (· < g) R₁ env₁)
    (hsome : ∀ k, (env₁.find? k).isSome = true → (env'.find? k).isSome = true)
    (hself : (env'.find? (keyOf t a)).isSome = true) :
    WalkedStored ρ t (· < g + 1) R' env' := by
  refine ⟨fun x c n hx hnb hlog hlogB hchk => ?_, fun r' x hw hgr ha' => ?_⟩
  · by_cases hxa : x = a
    · rw [hxa]
      exact hself
    · rw [OpInstall.recordOf_ne hadds hxa] at hx
      exact hsome _ (hW.1 x c n hx hnb hlog
        (fun cb hcb => hlogB cb (OpInstall.recordOf_up hadds hcb)) hchk)
  · by_cases hlt : Ix.SpecDigest.groupOf r' < g
    · exact hsome _ (hW.2 r' x hw hlt ha')
    · have hgr' : Ix.SpecDigest.groupOf r' < g + 1 := hgr
      have e : Ix.SpecDigest.groupOf r' = g := by omega
      have hr' : r' ∈ roleGroup g := by
        rw [← e]
        exact role_mem_roleGroup r'
      rw [hgrp, List.mem_singleton] at hr'
      rw [hr', ha] at ha'
      rw [← Option.some.inj ha']
      exact hself

/-- **The stored family map after a role unit** (module docstring). -/
theorem storedFamilies_roleUnit {t : Ix.Kernel.RoleTable} {a : _root_.Address}
    {R₁ R' : Ixon.Env} {env₁ env' : Ix.Kernel.Env .anon}
    {famOf : _root_.Address → Option _root_.Address}
    (hadds : AddsAt R₁ R' a) (hc₁ : UsedClosed R₁) (hc' : UsedClosed R')
    (hform : ∀ c, recordOf R' a = some c → (∀ ms, c.info ≠ .muts ms) ∧ ¬ IsProj c)
    (hst : ∀ x, StoredAt t env₁ x → StoredAt t env' x)
    (hback : ∀ x, StoredAt t env' x → StoredAt t env₁ x ∨ x = a)
    (hinst : ∀ rb crb, FamilyInstalled t env₁ rb crb → FamilyInstalled t env' rb crb)
    (h : StoredFamilies t R₁ env₁ famOf) : StoredFamilies t R' env' famOf := by
  refine storedFamilies_grow (fun x c hx => OpInstall.recordOf_up hadds hx)
    (fun x b hx => (hadds.2.2 x b).mpr hx) hc' (fun B cb hB hroute hstored => ?_) hst hinst h
  have hmuts : ∃ ms, cb.info = .muts ms := by
    by_contra hn
    have hnm : ∀ ms, cb.info ≠ .muts ms := fun ms e => hn ⟨ms, e⟩
    have hroute' : Route.recordRoute R' B cb = some true := by
      unfold Route.blockRoute at hroute
      rw [hB] at hroute
      exact hroute
    rw [Route.recordRoute_of_not_muts hnm] at hroute'
    exact absurd hroute' (by simp)
  have hBa : B ≠ a := by
    intro e
    rw [e] at hB
    obtain ⟨ms, hms⟩ := hmuts
    exact (hform cb hB).1 ms hms
  have hB₁ : recordOf R₁ B = some cb := by
    rw [← OpInstall.recordOf_ne hadds hBa]
    exact hB
  refine ⟨hB₁, ?_, fun x hx => ?_⟩
  · rw [← hroute]
    refine blockRoute_congr hB hB₁ (fun y hy => ?_)
    have hy₁ : (recordOf R₁ y).isSome = true := by
      rcases hy with ⟨i, hi, hxy⟩ | ⟨ms, i, m, hms, hm, hxy⟩
      · exact (hc₁.1 B cb hB₁).2 i hi y hxy
      · rw [hxy]
        exact Option.isSome_iff_exists.mpr ⟨_, (hc₁.2 B cb ms hB₁ hms i m hm).1⟩
    obtain ⟨cy, hcy⟩ := Option.isSome_iff_exists.mp hy₁
    unfold Route.isIndAt
    rw [hcy, OpInstall.recordOf_up hadds hcy]
  · rcases hback x (hstored x hx) with hs | hxa
    · exact hs
    · exfalso
      rw [hxa] at hx
      rcases constAddr_record hc' hB hx with ⟨he, -⟩ | ⟨-, P, hP, hPp, -⟩
      · exact hBa he.symm
      · exact (hform P hP).2 hPp

/-! ## The standard axioms -/

/-- **The standard axioms' role unit with the family form, from the validation facts.** -/
theorem standardAxiomRoleUnitW_of_validation
    {L : Ix.Kernel.Env .anon → NativeFam .anon → Prop} (hL : LinkLaws L)
    {calls : List (Call F)} (hv : AxiomInstall.AxiomValidationFacts.{u} L calls) :
    AtGroups (BindingRun calls) (RoleUnitStepOverW.{u} (· ∈ standardAxioms) L) := by
  intro t ρ Rs hrun hall ht g h6 h77 r a R R₁ R' env₁ famOf₁ hgrp hstd ha hadm hreads hb hadds
    hle hW hsf
  have htwf : t.wf = true := wf_of_check ht
  have hkeya : keyOf t a = Ix.Kernel.Key.role r := Core.keyOf_of_addressOf htwf ha
  have hkey_role : ∀ x, keyOf t x = Ix.Kernel.Key.role r → x = a := by
    intro x hx
    have h1 := Core.addressOf_of_keyOf htwf hx
    rw [ha] at h1
    exact (Option.some.inj h1).symm
  obtain ⟨hsolo, hfresh⟩ :=
    hv t ρ Rs hrun hrun.stepStores hall ht g r a R R₁ R' env₁ h6 h77 hgrp hstd ha hadm hreads
      hb hadds
  obtain ⟨cA, axA, hcA, hdA⟩ := hsolo
  have hform : ∀ c, recordOf R' a = some c → (∀ ms, c.info ≠ .muts ms) ∧ ¬ IsProj c := by
    intro c hc
    have e : cA = c := Option.some.inj (hcA.symm.trans hc)
    rw [← e]
    refine ⟨fun ms hm => ?_, fun hp => ?_⟩
    · rw [hdA] at hm
      cases hm
    · rcases hp with ⟨_, h'⟩ | ⟨_, h'⟩ | ⟨_, h'⟩ | ⟨_, h'⟩ <;> (rw [hdA] at h'; cases h')
  cases hf : env₁.find? (Ix.Kernel.Key.role r) with
  | none =>
    obtain ⟨lps, tyD, ty, hcv, hpin, hnaux, hty, hrd, hsize, hreload⟩ := hfresh hf
    have hB := AxiomInstall.roleAxiom_step hL hall hgrp hstd ha hadm hb hadds hf hcv hpin hnaux
      hty hrd ⟨cA, axA, hcA, hdA⟩ hsize hreload
    have hext : ∀ ci ∈ env₁.consts, ci ∈ (AxiomInstall.axInstalled env₁ r lps ty).consts :=
      fun ci hci => List.mem_cons_of_mem _ hci
    have hnd : ((AxiomInstall.axInstalled env₁ r lps ty).consts.map (·.name)).Nodup :=
      hB.shape.reading.nodup
    have hself : (AxiomInstall.axInstalled env₁ r lps ty).find? (Ix.Kernel.Key.role r) =
        some (.axiomInfo ⟨.role r, lps, ty⟩) := by
      show (⟨(Ix.Kernel.ConstantInfo.axiomInfo ⟨.role r, lps, ty⟩) :: env₁.consts⟩ :
        Ix.Kernel.Env .anon).find? _ = _
      rw [Ix.Kernel.Env.find?_cons]
      exact ite_eq_left rfl
    refine ⟨AxiomInstall.axInstalled env₁ r lps ty, hext, hB, ?_, ?_⟩
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
  | some ci =>
    have hB := AxiomInstall.roleAxiom_stored hall hgrp hstd ha hadm hb hadds
      ⟨cA, axA, hcA, hdA⟩ hf
    refine ⟨env₁, fun _ h => h, hB, ?_, ?_⟩
    · exact walkedStored_roleUnit hgrp ha hadds hW (fun _ h => h)
        (Option.isSome_iff_exists.mpr ⟨ci, by rw [hkeya]; exact hf⟩)
    · exact storedFamilies_roleUnit hadds hb.shape.usedClosed hadm.usedClosed hform
        (fun _ h => h) (fun _ h => Or.inl h) (fun _ _ h => h) hsf

/-- **The standard axioms' role unit with the family form, with no premise**, at the link the
composed fold carries. -/
theorem standardAxiomRoleUnitW_closed :
    ∀ calls : List (Call F), AtGroups (BindingRun calls)
      (RoleUnitStepOverW.{u} (· ∈ standardAxioms) Typing.FormerOpenTraceAt) :=
  fun calls => standardAxiomRoleUnitW_of_validation linkLaws_formerOpenTrace
    (axiomValidationFacts Typing.FormerOpenTraceAt calls)

end IxVM.Refinement.Binding
