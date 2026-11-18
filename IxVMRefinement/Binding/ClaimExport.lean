import IxVMRefinement.Binding.RunPredicate
import IxVMRefinement.RoleVal.BindingSpine
import IxVMRefinement.Claim.TopWalk

/-! # The binding claim's export, from the run's observations and four named parts

`BindingClaimExportObs (BindingRun calls) calls d` is what the binding fold asks of an accepted
`binding` claim. This file proves it from the run's own observations as far as they are
specified, and names what is left.

Proved from the observed `KernelRoles::validate_binding` call (`RoleVal.validate_binding_spine`):

* the table binds every role (`AllBound`), from the loop `assert_all_roles_bound`;
* every role of every validation group has its observed `validate_role` call under the role
  context at its group's validation limit (`RoleValidationIn`), from the loop
  `admit_all_groups` and each `group_admit`: the clause `Admits.validated` of every group;
* the run's records are one store that holds every record the run hashed
  (`Claim.runEnv`, `LoadedReads.RunStore`, `LoadedReads.HashedRecordsStored`), in the
  alternative where the run hashed no collision.

Left as named parts, each a closed statement about observed runs:

* `BindingClaimDecodes calls d`: an accepted `binding spec a` claim's run holds the observed
  `validate_binding` call on `a`, or hashed a collision. It is arm 10 of
  `KernelClaim::run_claim`, which has no generated observation; the typing arms were inverted by
  hand (`Claim.verify_claim_decode_typing_spec`).
* `LoadedTableAdmits`: the value `load_role_table` returns in a binding run represents the
  table that bytes the run hashed admit at the binding address. `Claim.load_role_table_spec` is
  this for a table given in advance; here the table has to come from the parse, and its
  evidence clauses from the roles' validations.
* `LoadedTablePinsPrelude`: a loaded table that binds every role pins the prelude (the loop
  `assert_basis_pinned`; `RoleVal.basis_pin_prelude` is one lookup of it).
* `GroupStoresOfRun calls`: for the admitted table and the observed validations there are a
  rank and a sequence of stores over the run's records, starting at the committed basis rows,
  with every clause of each group's admission but the validation of its roles, and its reading
  clause; or the run hashed a collision.
-/

set_option linter.unusedVariables false

namespace IxVM.Refinement.Binding

open IxVM.Consistency
open IxVM.Refinement.Typing
open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library
open IxVM (F)
open IxVM.Refinement.StoreInhabit (basisStore)

/-- The roles of a group, in the two spellings of the schedule. -/
theorem groupRoles_eq_roleGroup (g : Nat) : RoleVal.groupRoles g = roleGroup g := by
  unfold RoleVal.groupRoles roleGroup
  rw [List.getD_eq_getElem?_getD]

/-- The observed validation of a role, in the fold's spelling. -/
theorem roleValidationIn_of_observed {calls : List (Call F)} {bAddr : _root_.Address}
    {t : Ix.Kernel.RoleTable} {g : Nat} {r : Ix.Kernel.Role}
    (h : RoleVal.ValidateRoleIn calls bAddr t g r) : RoleValidationIn calls bAddr t g r :=
  h

/-! ## The run record without the roles' validations -/

/-- **The observed run record with the validation of a role left trivial**: what the store
clauses of a group's admission read (the run's records, a rank, the observed checks). -/
def checkedRun (calls : List (Call F)) (bAddr : _root_.Address) (t : Ix.Kernel.RoleTable)
    (E₀ : Ixon.Env) (rank : Nat → _root_.Address → Nat) : BRun where
  E₀ := E₀
  rank := rank
  checked := fun a n => UnitCheckedAt calls bAddr t E₀ a (some n)
  validated := fun _ _ => True

/-- **A group's admission for the observed run record**, from its admission with the validations
left trivial and the observed validation of each of its roles. -/
theorem admits_observed_of_checked {calls : List (Call F)} {bAddr : _root_.Address}
    {t : Ix.Kernel.RoleTable} {E₀ : Ixon.Env} {rank : Nat → _root_.Address → Nat} {g : Nat}
    {R R' : Ixon.Env} (h : Admits (checkedRun calls bAddr t E₀ rank) t g R R')
    (hv : ∀ r ∈ roleGroup g, RoleValidationIn calls bAddr t g r) :
    Admits (observedRun calls bAddr t E₀ rank) t g R R' where
  mono := h.mono
  monoBlobs := h.monoBlobs
  loaded := h.loaded
  loadedBlobs := h.loadedBlobs
  hashed := h.hashed
  usedClosed := h.usedClosed
  committed := h.committed
  zeroFree := h.zeroFree
  rankUsed := h.rankUsed
  rankOwner := h.rankOwner
  projMember := h.projMember
  standing := h.standing
  logic := h.logic
  checked := h.checked
  validated := hv
  kept := h.kept
  opsOwn := h.opsOwn
  unitsLast := h.unitsLast

/-- The reading clause reads the run's records only. -/
theorem admitsReads_observed_of_checked {calls : List (Call F)} {bAddr : _root_.Address}
    {t : Ix.Kernel.RoleTable} {E₀ : Ixon.Env} {rank : Nat → _root_.Address → Nat}
    {R R' : Ixon.Env} (h : AdmitsReads (checkedRun calls bAddr t E₀ rank) t R R') :
    AdmitsReads (observedRun calls bAddr t E₀ rank) t R R' where
  blobs := h.blobs
  reads := h.reads

/-! ## The named parts -/

/-- **The decode of an accepted binding claim**: the run hashed a collision with the claim's
bytes or the committed footprint, or it holds the observed `KernelRoles::validate_binding` call
on the claim's binding address. -/
def BindingClaimDecodes (calls : List (Call F)) (d : Digest) : Prop :=
  ∀ (bytes : ByteArray) (spec a : _root_.Address), Ix.Claim.de bytes = .ok (.binding spec a) →
    packDigest (Address.blake3Pure bytes) = d → ∀ V : View,
      V.HashedCollision (bytes :: committedFootprint) calls ∨ RoleVal.ValidateBindingIn calls a

/-- **The table a binding run loads is the admitted table of bytes the run hashed**: for the
three calls of `KernelRoles::validate_binding` on the address `a`, there are bytes the load
hashed that admit at `a` as a table the loaded value represents. -/
def LoadedTableAdmits : Prop :=
  ∀ (a : _root_.Address) (x_a x_tbl v r : SourceValue F) (h h₁ h₂ h' : Heap F)
    (cs₁ cs₂ cs₃ : List (Call F)),
    Core.S0.addr h x_a a →
    ObsFn Core.W "KernelRoles::load_role_table" [x_a] h x_tbl h₁ cs₁ →
    ObsFn Core.W "KernelRoles::assert_all_roles_bound" [x_tbl, .field 0] h₁ v h₂ cs₂ →
    ObsFn Core.W "KernelRoles::admit_all_groups" [x_tbl, .field 0] h₂ r h' cs₃ →
    ∃ (tb : ByteArray) (t : Ix.Kernel.RoleTable), Hashed cs₁ tb ∧
      Ix.Kernel.Admission.admitBinding Address.admissionHash ⟨a, tb⟩ = .ok t ∧
      Claim.TableFullRep t a h₁ x_tbl

/-- **A loaded table that binds every role pins the prelude.** -/
def LoadedTablePinsPrelude : Prop :=
  ∀ (a : _root_.Address) (x_a x_tbl : SourceValue F) (h h₁ : Heap F) (cs₁ : List (Call F))
    (t : Ix.Kernel.RoleTable),
    ObsFn Core.W "KernelRoles::load_role_table" [x_a] h x_tbl h₁ cs₁ →
    Claim.TableFullRep t a h₁ x_tbl → AllBound t → PreludePinned t

/-- **The stores of a binding run**: for the admitted table, its roles all bound, the prelude
pinned and every role's validation observed, the run hashed a collision, or there are a rank and
a sequence of stores over the run's records that starts at the committed basis rows and has, at
each group from 6 to 76, every clause of the group's admission but the validation of its roles
(`checkedRun`), and the reading clause. -/
def GroupStoresOfRun (calls : List (Call F)) : Prop :=
  ∀ (V : View) (extra : List ByteArray), (∀ x ∈ committedFootprint, x ∈ extra) →
    ∀ (a : _root_.Address) (tb : ByteArray) (t : Ix.Kernel.RoleTable), Hashed calls tb →
      Ix.Kernel.Admission.admitBinding Address.admissionHash ⟨a, tb⟩ = .ok t →
      AllBound t → PreludePinned t →
      (∀ g, g < 77 → ∀ r ∈ roleGroup g, RoleValidationIn calls a t g r) →
      V.HashedCollision extra calls ∨
        ∃ (rank : Nat → _root_.Address → Nat) (Rs : Nat → Ixon.Env),
          (∀ x, (Rs 6).consts.get? x = basisStore.consts.get? x) ∧
          (∀ x, (Rs 6).blobs.get? x = basisStore.blobs.get? x) ∧
          ∀ g, 6 ≤ g → g < 77 →
            Admits (checkedRun calls a t (Claim.runEnv ⟨a, tb⟩ (t := t) calls) rank) t g
              (Rs g) (Rs (g + 1)) ∧
            AdmitsReads (checkedRun calls a t (Claim.runEnv ⟨a, tb⟩ (t := t) calls) rank) t
              (Rs g) (Rs (g + 1))

/-! ## What the observed validation of a binding gives -/

/-- **From the observed validation of a binding and the loaded table's admission**: bytes the
run hashed admit at the binding address as a table that binds every role, whose loaded value
is the one the run's `load_role_table` returned, and every role of each of the 77 groups has its
observed validation under the role context at its group's validation limit. -/
theorem validated_of_validateBinding {calls : List (Call F)} {a : _root_.Address}
    (tableAdmits : LoadedTableAdmits) (hrun : RoleVal.ValidateBindingIn calls a) :
    ∃ (tb : ByteArray) (t : Ix.Kernel.RoleTable) (x_a x_tbl : SourceValue F) (h h₁ : Heap F)
      (cs₁ : List (Call F)),
      Hashed calls tb ∧
      Ix.Kernel.Admission.admitBinding Address.admissionHash ⟨a, tb⟩ = .ok t ∧
      ObsFn Core.W "KernelRoles::load_role_table" [x_a] h x_tbl h₁ cs₁ ∧
      Claim.TableFullRep t a h₁ x_tbl ∧
      AllBound t ∧
      ∀ g, g < 77 → ∀ r ∈ roleGroup g, RoleValidationIn calls a t g r := by
  obtain ⟨h, h', x_a, res, cs, ha, ev, hsub⟩ := hrun
  obtain ⟨x_tbl, v, h₁, h₂, cs₁, cs₂, cs₃, ev_load, ev_bound, ev_admit, hsub₁, hspine⟩ :=
    RoleVal.validate_binding_spine ev
  obtain ⟨tb, t, htb, hadm, htbl⟩ :=
    tableAdmits a x_a x_tbl v res h h₁ h₂ h' cs₁ cs₂ cs₃ ha ev_load ev_bound ev_admit
  obtain ⟨hall, hval⟩ := hspine t a htbl
  refine ⟨tb, t, x_a, x_tbl, h, h₁, cs₁,
    Claim.hashed_mono (fun c hc => hsub c (hsub₁ c hc)) htb, hadm, ev_load, htbl, hall,
    fun g hg r hr => ?_⟩
  rw [← groupRoles_eq_roleGroup] at hr
  exact roleValidationIn_of_observed ((hval g hg r hr).mono hsub)

/-! ## The export -/

/-- **The binding claim's export from its four named parts** (module docstring). -/
theorem bindingClaimExportObs_of_parts {calls : List (Call F)} {d : Digest}
    (hb : Bounded calls)
    (claimDecode : BindingClaimDecodes calls d)
    (tableAdmits : LoadedTableAdmits)
    (preludePins : LoadedTablePinsPrelude)
    (groupStores : GroupStoresOfRun calls) :
    BindingClaimExportObs (BindingRun calls) calls d := by
  intro bytes spec a hde hdig V
  rcases claimDecode bytes spec a hde hdig V with hcol | hrun
  · exact Or.inl hcol
  obtain ⟨tb, t, x_a, x_tbl, h, h₁, cs₁, htb, hadm, ev_load, htbl, hall, hval⟩ :=
    validated_of_validateBinding tableAdmits hrun
  have hpin : PreludePinned t := preludePins a x_a x_tbl h h₁ cs₁ t ev_load htbl hall
  rcases Claim.noColl_or_hashedCollision V (bytes :: committedFootprint) calls with
    hcol | hnoColl
  · exact Or.inl hcol
  rcases groupStores V (bytes :: committedFootprint) (fun x hx => List.mem_cons_of_mem _ hx)
    a tb t htb hadm hall hpin hval with hcol | ⟨rank, Rs, hbc, hbb, hgs⟩
  · exact Or.inl hcol
  have hw0 : Claim.WalkedL6 calls t (Claim.runEnv ⟨a, tb⟩ (t := t) calls) [] :=
    Claim.walkedL6_envOfRecs (seeds := []) hnoColl [] hadm (by simp)
      (by intro r hr; cases hr)
  have hload : LoadedBy calls (Claim.runEnv ⟨a, tb⟩ (t := t) calls) :=
    Claim.envOfRecs_loadedBy (t := t) ⟨a, tb⟩ calls []
  refine Or.inr ⟨tb, t, htb, hadm, hall, Claim.runEnv ⟨a, tb⟩ (t := t) calls, rank, Rs,
    hload, ?_⟩
  exact
    { bounded := hb
      observed := ⟨a, tb, htb, hadm, rfl⟩
      runStore := LoadedReads.RunStore.of_walkedL6 hload hw0
      hashedStored := LoadedReads.hashedRecordsStored_of_walkedL6 hw0
      preludePinned := hpin
      basisConsts := hbc
      basisBlobs := hbb
      admits := fun g hg6 hg =>
        admits_observed_of_checked (hgs g hg6 hg).1 (hval g hg)
      reads := fun g hg6 hg => admitsReads_observed_of_checked (hgs g hg6 hg).2 }

/-- **The claim export of the residual theorem, from the four named parts for every bounded
run**: the decode of the claim is taken from the observed `verify_claim` derivation. -/
theorem bindingClaimExport_of_parts
    (claimDecode : ∀ (d : Digest) (value : SourceValue F) (heap : Heap F)
      (calls : List (Call F)),
      ObsFn Core.W verifyClaim [digestValue d] [] value heap calls →
        BindingClaimDecodes calls d)
    (tableAdmits : LoadedTableAdmits)
    (preludePins : LoadedTablePinsPrelude)
    (groupStores : ∀ calls, GroupStoresOfRun calls) :
    SourceSoundBounded fun calls d => BindingClaimExportObs (BindingRun calls) calls d :=
  fun d value heap calls ev hb =>
    bindingClaimExportObs_of_parts hb (claimDecode d value heap calls ev) tableAdmits
      preludePins (groupStores calls)

end IxVM.Refinement.Binding
