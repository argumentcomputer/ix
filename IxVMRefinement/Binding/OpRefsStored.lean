import IxVMRefinement.Binding.AxiomInstall

/-! # The references an operation's record uses are stored by the closure's environment

The operations' validation facts (`OpValidationFactsW`) check the operation's definition at the
closure's environment `env₁`, under the keying of the prefix, which resolves an address only
where `env₁` stores its key. So every reference the record uses has to be stored there
(`Decl.UsedRefsStored`). This file reduces that to what the run's walk of the record gives.

* `opRecord_new`: **the operation's record is new in the group's admission.** The closure's
  store `R₁` cannot hold it: its reading would be stored at the operation's key
  (`ReadingOf.stored`), and the invariant below `g` stores an operation only once its group is
  admitted (`BoundaryFacts.opsAdmitted`). With `StoreLe R R₁`, `R` does not hold it either.
* `usedRefsStored_of_walkedStored`: **the references the record uses are stored**: a used
  reference is not the record's own address (`Admits.unitsLast`, the record being new), so the
  closure's store holds its record, and the closure's coverage (`WalkedStored`) stores it,
  given what the walk says of each reference: a checked record in Lean's logic that is no block,
  or the address of a walked role of an earlier group.
-/

universe u

set_option linter.unusedVariables false

namespace IxVM.Refinement.Binding

open IxVM.Consistency
open IxVM.Refinement.Typing
open Ix.Kernel.Semantics (NativeFam)

/-- **The operation's record is new in the group's admission** (module docstring). The reading
of the record over the closure's store, where that store holds it, is the premise `hread`. -/
theorem opRecord_new {L : Ix.Kernel.Env .anon → NativeFam .anon → Prop}
    {ρ : BRun} {t : Ix.Kernel.RoleTable} {g : Nat} {R R₁ R' : Ixon.Env}
    {env₁ : Ix.Kernel.Env .anon} {r : Ix.Kernel.Role} {a : _root_.Address}
    (htwf : t.wf = true) (hrg : r ∈ roleGroup g) (hop : r ∈ RoleOps.opRoles)
    (ha : t.addressOf? r = some a) (hb : BndOver.{u} L t (· < g) R₁ env₁)
    (hle : StoreLe R R₁) {c : Ixon.Constant} (hcR' : recordOf R' a = some c)
    (hread : (recordOf R₁ a).isSome = true → ∃ ci₀, Reads t R₁ a ci₀) :
    recordOf R₁ a = none ∧ New R R' a := by
  have hgr : Ix.SpecDigest.groupOf r = g := OpInstall.groupOf_of_mem_roleGroup hrg
  have hkeya : keyOf t a = Ix.Kernel.Key.role r := Core.keyOf_of_addressOf htwf ha
  have h₁ : recordOf R₁ a = none := by
    cases h : recordOf R₁ a with
    | none => rfl
    | some c₁ =>
      exfalso
      obtain ⟨ci, hci, -⟩ := hb.shape.reading.stored a (hread (by rw [h]; rfl))
      rw [hkeya] at hci
      have hlt := hb.facts.opsAdmitted r hop (by rw [hci]; rfl)
      have hlt' : Ix.SpecDigest.groupOf r < g := hlt
      omega
  have hnone : recordOf R a = none := by
    cases h : recordOf R a with
    | none => rfl
    | some c₀ =>
      exfalso
      have hup : recordOf R₁ a = some c₀ := by
        unfold recordOf at h ⊢
        cases hg : R.consts.get? a with
        | none => rw [hg] at h; cases h
        | some lc => rw [hg] at h; rw [hle.1 a lc hg]; exact h
      rw [h₁] at hup
      cases hup
  exact ⟨h₁, (⟨by rw [hcR']; rfl, hnone⟩ : (recordOf R' a).isSome = true ∧ recordOf R a = none)⟩

/-- **The references the operation's record uses are stored by the closure's environment**
(module docstring). `hrefs` is what the walk of the record gives at each used reference. -/
theorem usedRefsStored_of_walkedStored
    {ρ : BRun} {t : Ix.Kernel.RoleTable} {g : Nat} {R R₁ R' : Ixon.Env}
    {env₁ : Ix.Kernel.Env .anon} {a : _root_.Address} {c : Ixon.Constant}
    (hadm : Admits ρ t g R R') (hadds : AddsAt R₁ R' a)
    (hws : WalkedStored ρ t (· < g) R₁ env₁) (hnew : New R R' a) (hunit : RoleUnitAt t g a)
    (hc : recordOf R' a = some c)
    (hrefs : ∀ x, UsedRef R' a x →
      (∃ (cx : Ixon.Constant) (n : Nat), recordOf R' x = some cx ∧
        (∀ ms, cx.info ≠ .muts ms) ∧ InLogic cx ∧
        (∀ cb, recordOf R' (Ix.Cert.ownerOf x cx) = some cb → InLogic cb) ∧ ρ.checked x n) ∨
      (∃ r', walkedRole r' = true ∧ Ix.SpecDigest.groupOf r' < g ∧ t.addressOf? r' = some x)) :
    Decl.UsedRefsStored t env₁ c := by
  intro i hi x hx
  have hx' : c.refs[i]? = some x := by rw [← Array.getElem?_toList]; exact hx
  have hu : UsedRef R' a x := ⟨c, i, hc, hi, hx'⟩
  have hxa : x ≠ a := fun e => hadm.unitsLast a x hnew hu (by rw [e]; exact hunit)
  rcases hrefs x hu with ⟨cx, n, hcx, hnb, hlog, hown, hchk⟩ | ⟨r', hw, hlt, hr'⟩
  · have hcx₁ : recordOf R₁ x = some cx := (OpInstall.recordOf_ne hadds hxa).symm.trans hcx
    have hown₁ : ∀ cb, recordOf R₁ (Ix.Cert.ownerOf x cx) = some cb → InLogic cb :=
      fun cb hcb => hown cb (OpInstall.recordOf_up hadds hcb)
    exact Option.isSome_iff_exists.mp (hws.1 x cx n hcx₁ hnb hlog hown₁ hchk)
  · exact Option.isSome_iff_exists.mp (hws.2 r' x hw hlt hr')

end IxVM.Refinement.Binding
