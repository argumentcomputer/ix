import IxVMRefinement.Binding.Fold
import IxVMRefinement.Claim.TopBase

/-! # A binding run, read from its observed calls

`BRun` leaves two predicates free: whether the unit at an address was checked at a limit, and
whether a role was validated in a group's validation. With free predicates the admission of a
group (`Admits`) can be discharged without a run. This file fixes both to observations of the
run's own calls.

* `UnitCheckedAt calls bAddr t E₀ a lim`: the walk loaded the record at `a` and ran
  `KernelCheck::check_const` on it under the role context at `lim` (`Claim.CheckedLimAt`), or,
  for a block record, did so for every member of the block (`Claim.MemberCheckedLimAt`). The
  limit is named, and is an `Option Nat`: a group's validation checks at `some` of the group's
  validation limit.
* `RoleValidationIn calls bAddr t g r`: among the run's calls there is an observed call of
  `KernelRoles::validate_role` on the role `r`, under the role context at the validation limit
  of the group `g` and the table `t`. It is the observation itself, so nothing a role's
  validation asserts (a type pin, a constructor count, an equation or certificate comparison) is
  lost: each is a consequence of this call.
* `observedRun calls bAddr t E₀ rank`: the run record whose two predicates are these.
* `RoleValidationIn.walks`: what the observed validation gives today, from the specification of
  `validate_role`: the structural facts `RoleVal.RoleValidatedAt` and a closed list of walked and
  checked records holding the role's record (for a role whose record is walked) and the walked
  part of its evidence.
* `BindingClaimExportObs`: the claim export in which the run record is the observed one, and
  `BindingClaimExportObs.toExport`: it is an export in the earlier sense.
-/

set_option linter.unusedVariables false

namespace IxVM.Refinement.Binding

open IxVM.Consistency
open IxVM.Refinement.Typing
open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library
open IxVM (F)

/-- **The run checked the unit at `a` under the role context at `lim`**: the record itself, or
every member of the block record the run's store holds there. -/
def UnitCheckedAt (calls : List (Call F)) (bAddr : _root_.Address) (t : Ix.Kernel.RoleTable)
    (E₀ : Ixon.Env) (a : _root_.Address) (lim : Option Nat) : Prop :=
  Claim.CheckedLimAt calls bAddr t a lim ∨
    ∃ (c : Ixon.Constant) (ms : Array Ixon.MutConst), recordOf E₀ a = some c ∧
      c.info = .muts ms ∧ ∀ k, k < ms.size → Claim.MemberCheckedLimAt calls bAddr t a ms k lim

/-- **The run validated the role `r` in the validation of group `g`**: an observed call of
`KernelRoles::validate_role` on `r` under the role context at the group's validation limit,
among the run's calls. -/
def RoleValidationIn (calls : List (Call F)) (bAddr : _root_.Address)
    (t : Ix.Kernel.RoleTable) (g : Nat) (r : Ix.Kernel.Role) : Prop :=
  ∃ (h h' : Heap F) (x_rc x_tbl res : SourceValue F) (cs : List (Call F)),
    Claim.RCFullRep t bAddr (RoleVal.groupValLimit g) h x_rc ∧
    Claim.TableFullRep t bAddr h x_tbl ∧
    ObsFn Core.W "KernelRoles::validate_role" [x_rc, x_tbl, .field (Core.roleNum r)] h res h'
      cs ∧
    ∀ cl ∈ cs, cl ∈ calls

/-- **The run record of an observed binding run**: the records it loaded, a rank, and the two
predicates read off the run's calls. -/
def observedRun (calls : List (Call F)) (bAddr : _root_.Address) (t : Ix.Kernel.RoleTable)
    (E₀ : Ixon.Env) (rank : Nat → _root_.Address → Nat) : BRun where
  E₀ := E₀
  rank := rank
  checked := fun a n => UnitCheckedAt calls bAddr t E₀ a (some n)
  validated := fun g r => RoleValidationIn calls bAddr t g r

/-- **What the observed validation of a role gives**, from the specification of
`KernelRoles::validate_role`: its structural facts, and a closed list of records the run walked
and checked that holds the role's record when the role's record is walked, and the walked part
of each proof in its evidence. -/
theorem RoleValidationIn.walks {calls : List (Call F)} {bAddr : _root_.Address}
    {t : Ix.Kernel.RoleTable} {g : Nat} {r : Ix.Kernel.Role}
    (hv : RoleValidationIn calls bAddr t g r) :
    RoleVal.RoleValidatedAt t calls g r ∧
      ∃ recs : List (Claim.WalkedRec calls bAddr t),
        Claim.RecsClosed recs ∧
        (∀ a, RoleVal.roleWalksBound r = true → t.addressOf? r = some a →
          a ∈ recs.map (·.addr)) ∧
        (∀ (arr : Array (Ix.Kernel.Evidence _root_.Address)) (thm : _root_.Address),
          (r, arr) ∈ t.evidence.toList → Ix.Kernel.Evidence.proof thm ∈ arr.toList →
          RoleVal.EvidenceWalked t r thm (recs.map (·.addr))) := by
  obtain ⟨h, h', x_rc, x_tbl, res, cs, hrc, htbl, ev, hsub⟩ := hv
  obtain ⟨-, hval, recs, hcl, ha, hev⟩ := RoleVal.validate_role_full_walks hrc htbl ev
  refine ⟨hval.mono hsub, recs.map (Claim.WalkedRec.mono hsub), hcl.mono hsub, ?_, ?_⟩
  · intro a hw had
    rw [Claim.map_addr_walkedRec_mono]
    exact ha a hw had
  · intro arr thm hm hp
    rw [Claim.map_addr_walkedRec_mono]
    exact hev arr thm hm hp

/-- The observed validation of a role is kept when the run's calls grow. -/
theorem RoleValidationIn.mono {cs₁ cs₂ : List (Call F)} {bAddr : _root_.Address}
    {t : Ix.Kernel.RoleTable} {g : Nat} {r : Ix.Kernel.Role}
    (hsub : ∀ cl ∈ cs₁, cl ∈ cs₂) (hv : RoleValidationIn cs₁ bAddr t g r) :
    RoleValidationIn cs₂ bAddr t g r := by
  obtain ⟨h, h', x_rc, x_tbl, res, cs, hrc, htbl, ev, hs⟩ := hv
  exact ⟨h, h', x_rc, x_tbl, res, cs, hrc, htbl, ev, fun cl hm => hsub cl (hs cl hm)⟩

/-- The observed check of a unit is kept when the run's calls grow. -/
theorem UnitCheckedAt.mono {cs₁ cs₂ : List (Call F)} {bAddr : _root_.Address}
    {t : Ix.Kernel.RoleTable} {E₀ : Ixon.Env} {a : _root_.Address} {lim : Option Nat}
    (hsub : ∀ cl ∈ cs₁, cl ∈ cs₂) (hc : UnitCheckedAt cs₁ bAddr t E₀ a lim) :
    UnitCheckedAt cs₂ bAddr t E₀ a lim := by
  rcases hc with hc | ⟨c, ms, hrec, hms, hk⟩
  · exact Or.inl (hc.mono hsub)
  · exact Or.inr ⟨c, ms, hrec, hms, fun k hlt => (hk k hlt).mono hsub⟩

/-- **The binding claim's export with the run record read from the run's calls**: as
`BindingClaimExport`, with the run view the observed one at the claim's binding address. -/
def BindingClaimExportObs (Run : Ix.Kernel.RoleTable → BRun → (Nat → Ixon.Env) → Prop)
    (calls : List (Call F)) (d : Digest) : Prop :=
  ∀ (bytes : ByteArray) (spec a : _root_.Address), Ix.Claim.de bytes = .ok (.binding spec a) →
    packDigest (Address.blake3Pure bytes) = d → ∀ V : View,
      V.HashedCollision (bytes :: committedFootprint) calls ∨
        ∃ (tb : ByteArray) (t : Ix.Kernel.RoleTable),
          Hashed calls tb ∧
          Ix.Kernel.Admission.admitBinding Address.admissionHash ⟨a, tb⟩ = .ok t ∧
          AllBound t ∧
          ∃ (E₀ : Ixon.Env) (rank : Nat → _root_.Address → Nat) (Rs : Nat → Ixon.Env),
            LoadedBy calls E₀ ∧ Run t (observedRun calls a t E₀ rank) Rs

/-- An export with the observed run record is an export. -/
theorem BindingClaimExportObs.toExport
    {Run : Ix.Kernel.RoleTable → BRun → (Nat → Ixon.Env) → Prop} {calls : List (Call F)}
    {d : Digest} (h : BindingClaimExportObs Run calls d) : BindingClaimExport Run calls d := by
  intro bytes spec a hde hdig V
  rcases h bytes spec a hde hdig V with hcol | ⟨tb, t, htb, hadm, hall, E₀, rank, Rs, hl, hrun⟩
  · exact Or.inl hcol
  · exact Or.inr ⟨tb, t, htb, hadm, hall, observedRun calls a t E₀ rank, Rs, hl, hrun⟩

end IxVM.Refinement.Binding
