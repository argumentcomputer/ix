import IxVMRefinement.Binding.StoreStanding
import IxVMRefinement.Binding.OpValidation
import IxVMRefinement.RoleVal.GroupWalkOrder
import IxVMRefinement.RoleVal.OpOrderScan

/-! # The operation order of a group's new records

The clauses `Admits.opsOwn` and `Admits.unitsLast` for the store sequence `groupStore t E₀ Pay`:
no record new in group `g`'s admission is bound to another group's operation, and none uses the
record of a role unit of `g` (an operation or a standard axiom of `g`).

Below the well-founded block (groups 6 to 32) a walk at limit `g` asserts, at every used reference
bound to an operation, that the operation's group is below `g`
(`KernelRoles::assert_op_reached_in_order` in `walk_ctx`; `Claim.TopRecsOrdered`). From limit 41 on
every operation is in force, so a reference bound to one is covered and not followed. Inside the
block (groups 33 to 40, validated at limit 33) that assertion is off and the circuit's scan
`KernelRoles::op_order_scan` stands in for it; what the clauses need of it is stated, not proved
(`WalkStepsOrdered` at those groups).

* `OpEarlier t g y`: an operation bound at `y` is of a group below `g`.
* `WalkStepsOrdered t E₀ g`: every reference the walk of group `g` follows (a used reference of a
  reached record, or of a proof in the evidence of a role of the group, that is not covered) is
  `OpEarlier`.
* `GroupReach.orderedListed`: an address a group's admission reaches is a record of a closed walk
  whose records' references are all ordered or covered (`Claim.TopRecsOrdered`).
* `walkStepsOrdered_of_run`: `WalkStepsOrdered` at every group below 33 or from 41 on;
  `axiomSteps_ordered`: the same for the references of the group's standard axiom, at every group.
* `GroupReach.root_or_earlier`: a reached address is the bound record of a role of the group,
  `OpEarlier`, or the block of a reached projection record.
* `stdAxiom_unreached`, `stdAxiom_not_storedBelow`: a standard axiom's record is reached by no
  group up to its own, and held by no store before its group.
* `groupStore_opsOwn`, `groupStore_unitsLast`: the two clauses at a group, from `WalkStepsOrdered`
  at the group and, for the records the group's payload reaches, `OpEarlier` of each.
-/

set_option linter.unusedVariables false

namespace IxVM.Refinement.Binding

open IxVM.Consistency
open IxVM.Refinement.Typing
open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library
open IxVM (F)
open IxVM.Refinement.StoreInhabit (basisStore)

/-! ## Decided facts -/

set_option maxRecDepth 100000 in
/-- The standard axioms are of groups below the well-founded block (decided). -/
theorem stdAxiom_group_lt : ∀ r ∈ standardAxioms, Ix.SpecDigest.groupOf r < 33 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- No standard axiom is inert (decided). -/
theorem stdAxiom_not_inert : ∀ r ∈ standardAxioms, r.inert = false := by
  decide +kernel

/-- An operation is of a group from 7 to 40. -/
theorem op_group_bounds {r : Ix.Kernel.Role} (hop : r ∈ RoleOps.opRoles) :
    7 ≤ Ix.SpecDigest.groupOf r ∧ Ix.SpecDigest.groupOf r ≤ 40 := by
  rcases RoleVal.operation_group r ((specKind_two_iff r).mpr hop) with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
    exact ⟨by omega, by omega⟩

/-- An operation's record is walked by its validation. -/
theorem op_walksBound {r : Ix.Kernel.Role} (hop : r ∈ RoleOps.opRoles) :
    RoleVal.roleWalksBound r = true := by
  rw [← Claim.walkedRole_eq_roleWalksBound]
  exact (op_facts_all r hop).1

theorem valLimit_of_lt {g : Nat} (h : g < 33) : valLimit g = g := by
  show RoleVal.groupValLimit g = g
  unfold RoleVal.groupValLimit
  simp [h]

theorem valLimit_ge_of_ge {g : Nat} (h : 41 ≤ g) : 41 ≤ valLimit g := by
  show 41 ≤ RoleVal.groupValLimit g
  unfold RoleVal.groupValLimit
  split
  · omega
  · split
    · omega
    · split <;> omega

set_option maxRecDepth 100000 in
/-- **A basis row that is an axiom record is the record a basis role is bound to** under the
default table (decided over the rows; it is `Quot.sound`'s). -/
theorem basisRows_axiom_bound :
    StoreInhabit.basisRows.all (fun e => match e.2.info with
      | .axio _ => TableInhabit.basisRoleOrder.any (fun r => ctab.addressOf? r == some e.1)
      | _ => true) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- No standard axiom is a basis role (decided). -/
theorem stdAxiom_not_basisRole : ∀ r ∈ standardAxioms, r ∉ TableInhabit.basisRoleOrder := by
  decide +kernel

/-- **At most one role is bound at an address**, under a well-formed table. -/
theorem addressOf_role_inj {t : Ix.Kernel.RoleTable} (hwf : t.wf = true) {r₁ r₂ : Ix.Kernel.Role}
    {a : _root_.Address} (h₁ : t.addressOf? r₁ = some a) (h₂ : t.addressOf? r₂ = some a) :
    r₁ = r₂ := by
  have hk := (Core.keyOf_of_addressOf hwf h₁).symm.trans (Core.keyOf_of_addressOf hwf h₂)
  injection hk

/-! ## The order of the references a walk follows -/

/-- **An operation bound at `y` is of a group below `g`.** -/
def OpEarlier (t : Ix.Kernel.RoleTable) (g : Nat) (y : _root_.Address) : Prop :=
  ∀ ro : Ix.Kernel.Role, t.addressOf? ro = some y → ro ∈ RoleOps.opRoles →
    Ix.SpecDigest.groupOf ro < g

/-- **The references the walk of group `g` follows are ordered**: a used reference of a record
the group's admission reaches, or of a proof in the evidence of a role of the group other than
the role's own address, that is not covered at the group's validation limit (so the walk follows
it) is bound to no operation of the group or of a later one. -/
structure WalkStepsOrdered (t : Ix.Kernel.RoleTable) (E₀ : Ixon.Env) (g : Nat) : Prop where
  refs : ∀ x y, GroupReach t E₀ g x → UsedRef E₀ x y →
    ¬ Claim.CoveredAt t (some (valLimit g)) y → OpEarlier t g y
  evidence : ∀ r ∈ roleGroup g, ∀ (arr : Array (Ix.Kernel.Evidence _root_.Address))
    (thm y : _root_.Address), (r, arr) ∈ t.evidence.toList →
    Ix.Kernel.Evidence.proof thm ∈ arr.toList → UsedRef E₀ thm y → t.addressOf? r ≠ some y →
    ¬ Claim.CoveredAt t (some (valLimit g)) y → OpEarlier t g y

/-- **An ordered reference below the well-founded block is `OpEarlier`.** -/
theorem opEarlier_of_ordered {t : Ix.Kernel.RoleTable} {g : Nat} (hg : g < 33)
    {y : _root_.Address} (h : Claim.OpOrderedAt t (some (valLimit g)) y) : OpEarlier t g y := by
  intro ro had hop
  have h' := h ro had ((specKind_two_iff ro).mpr hop) (valLimit g) rfl
    (by rw [valLimit_of_lt hg]; exact hg)
  rwa [valLimit_of_lt hg] at h'

/-- **From limit 41 on a reference the walk follows is bound to no operation**: every operation
is in force there, so a reference bound to one is covered. -/
theorem opEarlier_of_late {t : Ix.Kernel.RoleTable} {g : Nat} (hg : 41 ≤ g)
    {y : _root_.Address} (hnc : ¬ Claim.CoveredAt t (some (valLimit g)) y) :
    OpEarlier t g y := by
  intro ro had hop
  exfalso
  apply hnc
  refine ⟨ro, had, Or.inl ⟨(op_facts_all ro hop).1, fun n hn => ?_⟩⟩
  obtain rfl := Option.some.inj hn
  have h1 := (op_group_bounds hop).2
  have h2 := valLimit_ge_of_ge hg
  omega

/-- **An operation of an earlier group is stored before the group**: its own group walked its
bound record. -/
theorem storedBelow_of_op {t : Ix.Kernel.RoleTable} {E₀ : Ixon.Env} {Pay : PayloadRel}
    {r : Ix.Kernel.Role} (hop : r ∈ RoleOps.opRoles) {a : _root_.Address}
    (had : t.addressOf? r = some a) {g : Nat} (hlt : Ix.SpecDigest.groupOf r < g) :
    StoredBelow t E₀ Pay g a :=
  Or.inr ⟨Ix.SpecDigest.groupOf r, by have := (op_group_bounds hop).1; omega, hlt,
    GroupAdds.reach (GroupReach.root (role_mem_roleGroup r) (Or.inl (op_walksBound hop)) had)⟩

section Run

variable {calls : List (Call F)} {bAddr : _root_.Address} {t : Ix.Kernel.RoleTable}
  {E₀ : Ixon.Env} {Pay : PayloadRel}

/-- **An address a group's admission reaches is a record of a closed, ordered walk** at the
group's validation limit: every used reference of a record of the walk is ordered or covered. -/
theorem GroupReach.orderedListed (hC : CollisionFreeRun calls E₀) {g : Nat}
    (hval : ∀ r ∈ roleGroup g, RoleValidationIn calls bAddr t g r) {a : _root_.Address}
    (h : GroupReach t E₀ g a) :
    ∃ recs : List (Claim.TopRec calls bAddr t (some (valLimit g))),
      Claim.TopRecsClosed recs ∧ Claim.TopRecsOrdered recs ∧ ∃ y ∈ recs, y.addr = a := by
  induction h with
  | @root r a hr hwk had =>
    obtain ⟨a₁, recs, had₁, hcl, hord, hmem⟩ :=
      RoleVal.ValidateRoleIn.lim_walks_ordered
        (show RoleVal.ValidateRoleIn calls bAddr t g r from hval r hr) hwk
    have e : a₁ = a := Option.some.inj (had₁.symm.trans had)
    rw [e] at hmem
    obtain ⟨y, hy, hya⟩ := List.mem_map.mp hmem
    exact ⟨recs, hcl, hord, y, hy, hya⟩
  | @axiomRef r a' x hr hs had hu hns =>
    have hnc := AlreadyStoredRole.not_covered hns
    obtain ⟨a₁, rawBytes, c, recs, had₁, hsz, hh, hblk, hde, hdeE, hcl, hord, hrefs⟩ :=
      RoleVal.ValidateRoleIn.axiom_refs_ordered
        (show RoleVal.ValidateRoleIn calls bAddr t g r from hval r hr)
        ((RoleVal.specKind_three_iff r).mpr hs)
    have e : a' = a₁ := Option.some.inj (had.symm.trans had₁)
    have hrec : recordOf E₀ a' = some c := by
      rw [e, ← hblk]
      exact Claim.recordOf_hashed hC.runStore hC.hashedStored hh hsz hde hdeE
    obtain ⟨c', i, hc', hi, hx⟩ := hu
    have ec : c' = c := Option.some.inj (hc'.symm.trans hrec)
    rw [ec] at hi hx
    obtain ⟨hlt, hxe⟩ := Array.getElem?_eq_some_iff.mp hx
    have hlt' : i < c.refs.toList.length := by simpa using hlt
    have hxl : c.refs.toList[i]'hlt' = x := by simpa using hxe
    obtain ⟨-, hin⟩ := hrefs i hlt' (by rw [Assembly.usedRefIdxs_eq]; exact hi)
    rw [hxl] at hin
    rcases hin with hin | hcov
    · obtain ⟨y, hy, hya⟩ := List.mem_map.mp hin
      exact ⟨recs, hcl, hord, y, hy, hya⟩
    · exact absurd hcov hnc
  | @ref a' x _ hu hns ih =>
    have hnc := AlreadyStoredRole.not_covered hns
    obtain ⟨recs, hcl, hord, y, hy, hya⟩ := ih
    obtain ⟨c, i, hc, hi, hx⟩ := hu
    have hrec := topRec_recordOf hC.hashedStored y
    rw [hya] at hrec
    have ec : c = y.c := Option.some.inj (hc.symm.trans hrec)
    rw [ec] at hi hx
    obtain ⟨-, hrest⟩ := (hcl y hy).2 i (by rw [Assembly.usedRefIdxs_eq]; exact hi) x hx
    rcases hrest with ⟨-, r', hr', e, -⟩ | hcov
    · exact ⟨recs, hcl, hord, r', hr', e⟩
    · exact absurd hcov hnc
  | @owner a' c _ hc hp ih =>
    obtain ⟨recs, hcl, hord, y, hy, hya⟩ := ih
    have hrec := topRec_recordOf hC.hashedStored y
    rw [hya] at hrec
    have ec : c = y.c := Option.some.inj (hc.symm.trans hrec)
    rw [ec] at hp ⊢
    obtain ⟨r', hr', e, -⟩ := (hcl y hy).1 hp
    rw [hya] at e
    exact ⟨recs, hcl, hord, r', hr', e⟩
  | @evidenceRef r arr thm x hr hm hthm hu hne hns =>
    have hnc := AlreadyStoredRole.not_covered hns
    have hv := hval r hr
    have hv' : RoleVal.ValidateRoleIn calls bAddr t g r := hv
    rcases evidence_specKind hv.wf hm with h2 | h5
    · obtain ⟨a₀, had, -⟩ := (RoleValidationIn.walks hv).1
      obtain ⟨rawBytes, c, hsz, hh, hbl, hde, hwk⟩ :=
        RoleVal.ValidateRoleIn.op_certificate_walks_ordered hv' h2 had hm hthm
      have hrec : recordOf E₀ thm = some c := by
        rw [← hbl]
        exact Claim.recordOf_hashed hC.runStore hC.hashedStored hh hsz
          (Ingress.deConstant_of_deConstantExact hde) hde
      obtain ⟨c', i, hc', hi, hx⟩ := hu
      have ec : c' = c := Option.some.inj (hc'.symm.trans hrec)
      rw [ec] at hi hx
      obtain ⟨hlt, hxe⟩ := Array.getElem?_eq_some_iff.mp hx
      have hlt' : i < c.refs.toList.length := by simpa using hlt
      have hxl : c.refs.toList[i]'hlt' = x := by simpa using hxe
      have hne' : c.refs.toList[i]'hlt' ≠ a₀ := by
        rw [hxl]
        intro e
        exact hne (by rw [e]; exact had)
      obtain ⟨-, hrest⟩ := hwk i hlt' (by rw [Assembly.usedRefIdxs_eq]; exact hi) hne'
      rw [hxl] at hrest
      rcases hrest with hcov | ⟨recs, hcl, hord, hmem⟩
      · exact absurd hcov hnc
      · obtain ⟨y, hy, hya⟩ := List.mem_map.mp hmem
        exact ⟨recs, hcl, hord, y, hy, hya⟩
    · obtain ⟨recs, hcl, hord, hmem⟩ :=
        RoleVal.ValidateRoleIn.eqns_evidence_walks_ordered hv' h5 hm hthm
      obtain ⟨y, hy, hya⟩ := List.mem_map.mp hmem
      obtain ⟨c, i, hc, hi, hx⟩ := hu
      have hrec := topRec_recordOf hC.hashedStored y
      rw [hya] at hrec
      have ec : c = y.c := Option.some.inj (hc.symm.trans hrec)
      rw [ec] at hi hx
      obtain ⟨-, hrest⟩ := (hcl y hy).2 i (by rw [Assembly.usedRefIdxs_eq]; exact hi) x hx
      rcases hrest with ⟨-, r', hr', e, -⟩ | hcov
      · exact ⟨recs, hcl, hord, r', hr', e⟩
      · exact absurd hcov hnc
  | @eqnsProof r arr thm hr h5 hm hthm =>
    obtain ⟨recs, hcl, hord, hmem⟩ :=
      RoleVal.ValidateRoleIn.eqns_evidence_walks_ordered
        (show RoleVal.ValidateRoleIn calls bAddr t g r from hval r hr) h5 hm hthm
    obtain ⟨y, hy, hya⟩ := List.mem_map.mp hmem
    exact ⟨recs, hcl, hord, y, hy, hya⟩
  | @eqnsAnchor r ar a hr h5 har had =>
    obtain ⟨a₁, recs, had₁, hcl, hord, hmem⟩ :=
      RoleVal.ValidateRoleIn.eqns_anchors_walks_ordered
        (show RoleVal.ValidateRoleIn calls bAddr t g r from hval r hr) h5 har
    have e : a₁ = a := Option.some.inj (had₁.symm.trans had)
    rw [e] at hmem
    obtain ⟨y, hy, hya⟩ := List.mem_map.mp hmem
    exact ⟨recs, hcl, hord, y, hy, hya⟩

/-- **The references the walk follows are ordered, below the well-founded block and from limit 41
on**: below 33 by `walk_ctx`'s assertion on every walked record and every certificate reference;
from 41 on because every operation is in force. -/
theorem walkStepsOrdered_of_run (hC : CollisionFreeRun calls E₀) {g : Nat}
    (hval : ∀ r ∈ roleGroup g, RoleValidationIn calls bAddr t g r) (hg : g < 33 ∨ 41 ≤ g) :
    WalkStepsOrdered t E₀ g := by
  rcases hg with hg | hg
  swap
  · exact ⟨fun _ _ _ _ hnc => opEarlier_of_late hg hnc,
      fun _ _ _ _ _ _ _ _ _ hnc => opEarlier_of_late hg hnc⟩
  refine ⟨fun x y hx hu hnc => ?_, fun r hr arr thm y hm hthm hu hne hnc => ?_⟩
  · obtain ⟨recs, -, hord, z, hz, hza⟩ := hx.orderedListed hC hval
    obtain ⟨c, i, hc, hi, hy⟩ := hu
    have hrec := topRec_recordOf hC.hashedStored z
    rw [hza] at hrec
    have ec : c = z.c := Option.some.inj (hc.symm.trans hrec)
    rw [ec] at hi hy
    rcases hord z hz i (by rw [Assembly.usedRefIdxs_eq]; exact hi) y hy with h | h
    · exact opEarlier_of_ordered hg h
    · exact absurd h hnc
  · have hv := hval r hr
    have hv' : RoleVal.ValidateRoleIn calls bAddr t g r := hv
    rcases evidence_specKind hv.wf hm with h2 | h5
    · obtain ⟨a₀, had, -⟩ := (RoleValidationIn.walks hv).1
      obtain ⟨rawBytes, c, hsz, hh, hbl, hde, hwk⟩ :=
        RoleVal.ValidateRoleIn.op_certificate_walks_ordered hv' h2 had hm hthm
      have hrec : recordOf E₀ thm = some c := by
        rw [← hbl]
        exact Claim.recordOf_hashed hC.runStore hC.hashedStored hh hsz
          (Ingress.deConstant_of_deConstantExact hde) hde
      obtain ⟨c', i, hc', hi, hx⟩ := hu
      have ec : c' = c := Option.some.inj (hc'.symm.trans hrec)
      rw [ec] at hi hx
      obtain ⟨hlt, hxe⟩ := Array.getElem?_eq_some_iff.mp hx
      have hlt' : i < c.refs.toList.length := by simpa using hlt
      have hxl : c.refs.toList[i]'hlt' = y := by simpa using hxe
      have hne' : c.refs.toList[i]'hlt' ≠ a₀ := by
        rw [hxl]
        intro e
        exact hne (by rw [e]; exact had)
      obtain ⟨hor, -⟩ := hwk i hlt' (by rw [Assembly.usedRefIdxs_eq]; exact hi) hne'
      rw [hxl] at hor
      exact opEarlier_of_ordered hg hor
    · obtain ⟨recs, -, hord, hmem⟩ :=
        RoleVal.ValidateRoleIn.eqns_evidence_walks_ordered hv' h5 hm hthm
      obtain ⟨z, hz, hza⟩ := List.mem_map.mp hmem
      obtain ⟨c, i, hc, hi, hy⟩ := hu
      have hrec := topRec_recordOf hC.hashedStored z
      rw [hza] at hrec
      have ec : c = z.c := Option.some.inj (hc.symm.trans hrec)
      rw [ec] at hi hy
      rcases hord z hz i (by rw [Assembly.usedRefIdxs_eq]; exact hi) y hy with h | h
      · exact opEarlier_of_ordered hg h
      · exact absurd h hnc

/-- **The references of a group's standard axiom that the walk follows are ordered**, at every
group (the standard axioms are below the well-founded block). -/
theorem axiomSteps_ordered (hC : CollisionFreeRun calls E₀) {g : Nat}
    (hval : ∀ r ∈ roleGroup g, RoleValidationIn calls bAddr t g r) :
    ∀ r ∈ roleGroup g, r ∈ standardAxioms → ∀ a, t.addressOf? r = some a → ∀ y,
      UsedRef E₀ a y → ¬ Claim.CoveredAt t (some (valLimit g)) y → OpEarlier t g y := by
  intro r hr hs a had y hu hnc
  have hg : g < 33 := by
    rw [← groupOf_of_mem_roleGroup hr]
    exact stdAxiom_group_lt r hs
  obtain ⟨a₁, rawBytes, c, recs, had₁, hsz, hh, hblk, hde, hdeE, -, -, hrefs⟩ :=
    RoleVal.ValidateRoleIn.axiom_refs_ordered
      (show RoleVal.ValidateRoleIn calls bAddr t g r from hval r hr)
      ((RoleVal.specKind_three_iff r).mpr hs)
  have e : a = a₁ := Option.some.inj (had.symm.trans had₁)
  have hrec : recordOf E₀ a = some c := by
    rw [e, ← hblk]
    exact Claim.recordOf_hashed hC.runStore hC.hashedStored hh hsz hde hdeE
  obtain ⟨c', i, hc', hi, hx⟩ := hu
  have ec : c' = c := Option.some.inj (hc'.symm.trans hrec)
  rw [ec] at hi hx
  obtain ⟨hlt, hxe⟩ := Array.getElem?_eq_some_iff.mp hx
  have hlt' : i < c.refs.toList.length := by simpa using hlt
  have hxl : c.refs.toList[i]'hlt' = y := by simpa using hxe
  obtain ⟨hor, -⟩ := hrefs i hlt' (by rw [Assembly.usedRefIdxs_eq]; exact hi)
  rw [hxl] at hor
  rcases hor with h | h
  · exact opEarlier_of_ordered hg h
  · exact absurd h hnc

/-- **How a reached address was reached**, given the order of the references the walk follows:
it is the bound record of a role of the group, `OpEarlier`, or the block of a reached projection
record. -/
theorem GroupReach.root_or_earlier {g : Nat} (hsteps : WalkStepsOrdered t E₀ g)
    (haxs : ∀ r ∈ roleGroup g, r ∈ standardAxioms → ∀ a, t.addressOf? r = some a → ∀ y,
      UsedRef E₀ a y → ¬ Claim.CoveredAt t (some (valLimit g)) y → OpEarlier t g y)
    {a : _root_.Address} (h : GroupReach t E₀ g a) :
    (∃ r ∈ roleGroup g, t.addressOf? r = some a) ∨ OpEarlier t g a ∨
      ∃ x c, GroupReach t E₀ g x ∧ recordOf E₀ x = some c ∧ IsProj c ∧
        Ix.Cert.ownerOf x c = a := by
  cases h with
  | root hr _ had => exact Or.inl ⟨_, hr, had⟩
  | axiomRef hr hs had hu hns =>
    exact Or.inr (Or.inl (haxs _ hr hs _ had _ hu (AlreadyStoredRole.not_covered hns)))
  | ref hx hu hns =>
    exact Or.inr (Or.inl (hsteps.refs _ _ hx hu (AlreadyStoredRole.not_covered hns)))
  | owner hx hc hp => exact Or.inr (Or.inr ⟨_, _, hx, hc, hp, rfl⟩)
  | evidenceRef hr hm hthm hu hne hns =>
    exact Or.inr (Or.inl (hsteps.evidence _ hr _ _ _ hm hthm hu hne
      (AlreadyStoredRole.not_covered hns)))
  | eqnsProof hr h5 _ _ =>
    refine Or.inr (Or.inl fun r' _ hop => ?_)
    have hgr := groupOf_of_mem_roleGroup hr
    have h46 := specKind5_group_ge_46 _ h5
    have h40 := (op_group_bounds hop).2
    omega
  | eqnsAnchor hr h5 _ _ =>
    refine Or.inr (Or.inl fun r' _ hop => ?_)
    have hgr := groupOf_of_mem_roleGroup hr
    have h46 := specKind5_group_ge_46 _ h5
    have h40 := (op_group_bounds hop).2
    omega

/-- **The block of a reached projection record holds a block record.** -/
theorem GroupReach.owner_block (hC : CollisionFreeRun calls E₀) {g : Nat}
    {recs : List (Claim.TopRec calls bAddr t (some (valLimit g)))}
    (hw : GroupWalked calls bAddr t E₀ g recs) {x : _root_.Address} {c : Ixon.Constant}
    (hx : GroupReach t E₀ g x) (hc : recordOf E₀ x = some c) (hp : IsProj c) :
    ∃ cb, recordOf E₀ (Ix.Cert.ownerOf x c) = some cb ∧ IsBlock cb := by
  obtain ⟨y, hy, hya⟩ := hx.listed hC.hashedStored hw
  have hyc : y.c = c := by
    have h1 := topRec_recordOf hC.hashedStored y
    rw [hya, hc] at h1
    exact (Option.some.inj h1).symm
  obtain ⟨cb₀, hcb₀, hca⟩ := topRec_proj_member hC.runStore hC.hashedStored y (hyc ▸ hp)
  rw [hya, hyc] at hcb₀ hca
  rcases hca with ⟨hx', hst⟩ | ⟨ms, i, m, hms, -, -⟩
  · exfalso
    rw [← hx', hc] at hcb₀
    have e : c = cb₀ := Option.some.inj hcb₀
    rw [e] at hp
    exact standalone_not_proj hst hp
  · exact ⟨cb₀, hcb₀, ms, hms⟩

/-- **No group up to a standard axiom's own reaches it**: a reached record is checked at the
group's validation limit, and the check of an axiom record finds its role in force there. -/
theorem stdAxiom_unreached (hC : CollisionFreeRun calls E₀) (hax : AxiomRolesDeclared t E₀)
    {g : Nat} {recs : List (Claim.TopRec calls bAddr t (some (valLimit g)))}
    (hw : GroupWalked calls bAddr t E₀ g recs) (hwf : t.wf = true) {r : Ix.Kernel.Role}
    (hle : g ≤ Ix.SpecDigest.groupOf r) (hs : r ∈ standardAxioms) {a : _root_.Address}
    (had : t.addressOf? r = some a) (h : GroupReach t E₀ g a) : False := by
  obtain ⟨y, hy, hya⟩ := h.listed hC.hashedStored hw
  obtain ⟨c, ax, hc, hi, hsafe⟩ := hax r hs a had
  have hyc : y.c = c := by
    have h1 := topRec_recordOf hC.hashedStored y
    rw [hya, hc] at h1
    exact (Option.some.inj h1).symm
  have hchk : Claim.CheckedLimAt calls bAddr t a (some (valLimit g)) := by
    rcases y.hchecked with ⟨ms, hms, -⟩ | hck
    · rw [hyc, hi] at hms
      cases hms
    · rw [hya] at hck
      exact hck
  have hl : InLogic c := by simpa only [InLogic, hi] using hsafe
  have hin : ¬ InertAt t a := by
    rintro ⟨r', hin', had'⟩
    rw [addressOf_role_inj hwf had' had, stdAxiom_not_inert r hs] at hin'
    cases hin'
  obtain ⟨ro, -, hb', hforce⟩ :=
    Claim.checkedLimAt_standing_inForce hC.runStore hc hl hin (Or.inl ⟨ax, hi⟩) hchk
  have e : ro = r := addressOf_role_inj hwf hb' had
  subst e
  have hlt := hforce ⟨ax, hi⟩ (valLimit g) rfl
  have := valLimit_le g
  omega

/-- **A standard axiom's record is held by no store before its group**: a basis row that is an
axiom record is the record of a basis role (`basisRows_axiom_bound`, at a table pinning the
prelude), no standard axiom; and the first group from 6 that would add it does not: its walk does
not reach it (`stdAxiom_unreached`), a projection record or another group's standard axiom is not
it, and its payload would reach it new there (`PayloadFacts.notAxiomLike`). -/
theorem stdAxiom_not_storedBelow (hC : CollisionFreeRun calls E₀) (hb : BasisRowsLoaded E₀)
    (hax : AxiomRolesDeclared t E₀) (hP : PayloadFacts t E₀ Pay) (hpin : PreludePinned t)
    (hws : ∀ k, ∃ recs, GroupWalked calls bAddr t E₀ k recs) (hwf : t.wf = true)
    {r : Ix.Kernel.Role} (hs : r ∈ standardAxioms) {a : _root_.Address}
    (had : t.addressOf? r = some a) {g : Nat} (hg : g ≤ Ix.SpecDigest.groupOf r) :
    ¬ StoredBelow t E₀ Pay g a := by
  obtain ⟨c, ax, hc, hi, -⟩ := hax r hs a had
  have hbasis : ¬ (basisStore.consts.get? a).isSome = true := by
    intro hbas
    obtain ⟨lc, hlc⟩ := Option.isSome_iff_exists.mp hbas
    obtain ⟨c₀, hmem, -⟩ := StoreInhabit.store_get?_inv hlc
    have h6 : recordOf (groupStore t E₀ Pay 6) a = some c₀ := by
      rw [groupStore_six]
      exact StoreInhabit.store_record_of_mem hmem
    have hE₀ := ((groupStore_recordOf hb (Nat.le_refl 6)).mp h6).2
    have e : c₀ = c := Option.some.inj (hE₀.symm.trans hc)
    have hall := List.all_eq_true.mp basisRows_axiom_bound (a, c₀) hmem
    rw [e] at hall
    simp only [hi, List.any_eq_true, beq_iff_eq] at hall
    obtain ⟨r', hr', hb'⟩ := hall
    have had' : t.addressOf? r' = some a := by
      rw [addressOf_basis hpin hr']
      exact hb'
    have e' : r = r' := addressOf_role_inj hwf had had'
    rw [← e'] at hr'
    exact stdAxiom_not_basisRole r hs hr'
  have key : ∀ k, 6 ≤ k → k < Ix.SpecDigest.groupOf r → ¬ GroupAdds t E₀ Pay k a := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro hk6 hkr hadd
      obtain ⟨recs, hw⟩ := hws k
      rcases groupAdds_cases hC hax hw hadd with ⟨hra, -⟩ | ⟨y, -, -, -, p, hp, hproj, -⟩ |
          ⟨ro, hro, -, hadx, -⟩ | hpay
      · exact stdAxiom_unreached hC hax hw hwf (Nat.le_of_lt hkr) hs had hra
      · have e : p = c := Option.some.inj (hp.symm.trans hc)
        rw [e] at hproj
        exact proj_not_axiom hproj hi
      · have e : ro = r := addressOf_role_inj hwf hadx had
        rw [e] at hro
        rw [groupOf_of_mem_roleGroup hro] at hkr
        exact Nat.lt_irrefl k hkr
      · rcases payAdds_cases hP hpay with ⟨hpr, -⟩ | ⟨-, -, -, -, -, p, hp, hproj, -⟩
        · have hnot : ¬ StoredBelow t E₀ Pay k a := by
            rintro (hbas | ⟨j, hj6, hjk, hj⟩)
            · exact hbasis hbas
            · exact ih j hjk hj6 (by omega) hj
          have hnew : New (groupStore t E₀ Pay k) (groupStore t E₀ Pay (k + 1)) a := by
            refine ⟨?_, ?_⟩
            · rw [(groupStore_recordOf hb (Nat.le_succ_of_le hk6)).mpr
                ⟨storedBelow_of_adds hk6 hadd, hc⟩]
              rfl
            · cases h : recordOf (groupStore t E₀ Pay k) a with
              | none => rfl
              | some c' => exact absurd ((groupStore_recordOf hb hk6).mp h).1 hnot
          exact hP.notAxiomLike k a c hpr hnew hc (Or.inl ⟨ax, hi⟩)
        · have e : p = c := Option.some.inj (hp.symm.trans hc)
          rw [e] at hproj
          exact proj_not_axiom hproj hi
  rintro (hbas | ⟨k, hk6, hkg, hadd⟩)
  · exact hbasis hbas
  · exact key k hk6 (by omega) hadd

/-! ## The clauses -/

/-- **`Admits.opsOwn`**: a record new in group `g`'s admission that is bound to an operation is
bound to an operation of the group, given the order of the references the group's walk follows
and of the records its payload reaches. An operation's record is a standalone definition
(`validate_role_op_obs`), so it is neither a projection record nor the block of one; a reached
record that is no root of the group is `OpEarlier`, hence stored before the group. -/
theorem groupStore_opsOwn (hC : CollisionFreeRun calls E₀) (hb : BasisRowsLoaded E₀)
    (hax : AxiomRolesDeclared t E₀) (hP : PayloadFacts t E₀ Pay) (hcheck : t.check = .ok ())
    (hvalAll : ∀ k, ∀ r ∈ roleGroup k, RoleValidationIn calls bAddr t k r) {g : Nat}
    (hg : 6 ≤ g) {recs : List (Claim.TopRec calls bAddr t (some (valLimit g)))}
    (hw : GroupWalked calls bAddr t E₀ g recs) (hsteps : WalkStepsOrdered t E₀ g)
    (hpay : ∀ x, PayReach t E₀ Pay g x → OpEarlier t g x) :
    ∀ a r, New (groupStore t E₀ Pay g) (groupStore t E₀ Pay (g + 1)) a →
      t.addressOf? r = some a → r ∈ RoleOps.opRoles → r ∈ roleGroup g := by
  intro a r hnew had hop
  obtain ⟨c, hE, -, hadd, hnot⟩ := new_groupStore hb hg hnew
  have hvr := hvalAll _ r (role_mem_roleGroup r)
  have hwf : t.wf = true := hvr.wf
  obtain ⟨a₁, c₁, d, had₁, hc₁, hd, -⟩ :=
    validate_role_op_obs hcheck hC.runStore hC.hashedStored
      (show RoleVal.ValidateRoleIn calls bAddr t _ r from hvr) hop
  have ea : a₁ = a := Option.some.inj (had₁.symm.trans had)
  rw [ea, hE] at hc₁
  have hcd : c.info = .defn d := by
    rw [Option.some.inj hc₁]
    exact hd
  have hearly : Ix.SpecDigest.groupOf r < g → False := fun hlt =>
    hnot (storedBelow_of_op hop had hlt)
  rcases groupAdds_cases hC hax hw hadd with ⟨hra, -⟩ | ⟨y, -, -, -, p, hp, hproj, -⟩ |
      ⟨ro, hro, hs, hadx, c₂, ax, hc₂, hi, -⟩ | hpay'
  · rcases hra.root_or_earlier hsteps (axiomSteps_ordered hC (hvalAll g)) with
      ⟨r', hr', had'⟩ | hE' | ⟨x, cx, hx, hcx, hpx, hown⟩
    · rw [addressOf_role_inj hwf had had']
      exact hr'
    · exact (hearly (hE' r had hop)).elim
    · exfalso
      obtain ⟨cb, hcb, ms, hms⟩ := hx.owner_block hC hw hcx hpx
      rw [hown, hE] at hcb
      rw [← Option.some.inj hcb, hcd] at hms
      cases hms
  · exfalso
    have e : p = c := Option.some.inj (hp.symm.trans hE)
    rw [e] at hproj
    exact standalone_not_proj (Or.inl ⟨d, hcd⟩) hproj
  · exfalso
    have e : c₂ = c := Option.some.inj (hc₂.symm.trans hE)
    rw [e, hcd] at hi
    cases hi
  · rcases payAdds_cases hP hpay' with ⟨hpr, -⟩ | ⟨-, -, -, -, -, p, hp, hproj, -⟩
    · exact (hearly (hpay a hpr r had hop)).elim
    · exfalso
      have e : p = c := Option.some.inj (hp.symm.trans hE)
      rw [e] at hproj
      exact standalone_not_proj (Or.inl ⟨d, hcd⟩) hproj

/-- **`Admits.unitsLast`**: no record new in group `g`'s admission uses the record of a role unit of
the group. A role unit's address is not covered at the group's limit, so the walk (or the payload)
would follow the reference: to the group's operation, which is not `OpEarlier`; to its standard
axiom, which the group's admission does not reach (`stdAxiom_unreached`), and which the payload
does not reach: it is new in the group (`stdAxiom_not_storedBelow`), and no record new in the group
the payload reaches is an axiom record (`PayloadFacts.notAxiomLike`). -/
theorem groupStore_unitsLast (hC : CollisionFreeRun calls E₀) (hb : BasisRowsLoaded E₀)
    (hax : AxiomRolesDeclared t E₀) (hP : PayloadFacts t E₀ Pay) (hpin : PreludePinned t)
    (hws : ∀ k, ∃ recs, GroupWalked calls bAddr t E₀ k recs) {g : Nat} (hg : 6 ≤ g)
    (hval : ∀ r ∈ roleGroup g, RoleValidationIn calls bAddr t g r)
    {recs : List (Claim.TopRec calls bAddr t (some (valLimit g)))}
    (hw : GroupWalked calls bAddr t E₀ g recs) (hsteps : WalkStepsOrdered t E₀ g)
    (hpay : ∀ x, PayReach t E₀ Pay g x → OpEarlier t g x) :
    ∀ x a, New (groupStore t E₀ Pay g) (groupStore t E₀ Pay (g + 1)) x →
      UsedRef (groupStore t E₀ Pay (g + 1)) x a → ¬ RoleUnitAt t g a := by
  rintro x a hnew hused ⟨r, hr, had, hkind⟩
  have h6 : 6 ≤ g + 1 := Nat.le_succ_of_le hg
  obtain ⟨c, hE, -, hadd, -⟩ := new_groupStore hb hg hnew
  have huE : UsedRef E₀ x a := by
    obtain ⟨c', i, hc', hi, hx⟩ := hused
    exact ⟨c', i, ((groupStore_recordOf hb h6).mp hc').2, hi, hx⟩
  have hwf : t.wf = true := (hval r hr).wf
  have hgr : Ix.SpecDigest.groupOf r = g := groupOf_of_mem_roleGroup hr
  have hns : ¬ AlreadyStoredRole t g a := by
    rintro (⟨r', had', ⟨-, hlt⟩ | ⟨hnone, -⟩⟩ | ⟨r', had', hlt, -⟩ | ⟨r', had', -, hlt⟩)
    · have e : r' = r := addressOf_role_inj hwf had' had
      subst e
      have h1 := hlt (valLimit g) rfl
      have h2 := valLimit_le g
      omega
    · cases hnone
    · have e : r' = r := addressOf_role_inj hwf had' had
      subst e
      have h2 := valLimit_le g
      omega
    · have e : r' = r := addressOf_role_inj hwf had' had
      subst e
      omega
  have hnc : ¬ Claim.CoveredAt t (some (valLimit g)) a := AlreadyStoredRole.not_covered hns
  have hnotE : OpEarlier t g a → r ∈ RoleOps.opRoles → False := fun h hop => by
    have h1 := h r had hop
    omega
  have hnotP : r ∈ standardAxioms → PayReach t E₀ Pay g a → False := fun hs hpr => by
    obtain ⟨c', ax, hc', hi, -⟩ := hax r hs a had
    have hnot := stdAxiom_not_storedBelow hC hb hax hP hpin hws hwf hs had (Nat.le_of_eq hgr.symm)
    have hnew : New (groupStore t E₀ Pay g) (groupStore t E₀ Pay (g + 1)) a := by
      refine ⟨?_, ?_⟩
      · rw [(groupStore_recordOf hb h6).mpr
          ⟨storedBelow_of_adds hg (GroupAdds.stdAxiom hr hs had), hc'⟩]
        rfl
      · cases h : recordOf (groupStore t E₀ Pay g) a with
        | none => rfl
        | some c₀ => exact absurd ((groupStore_recordOf hb hg).mp h).1 hnot
    exact hP.notAxiomLike g a c' hpr hnew hc' (Or.inl ⟨ax, hi⟩)
  rcases groupAdds_cases hC hax hw hadd with ⟨hra, -⟩ | ⟨y, -, -, -, p, hp, -, -, hrefs, -⟩ |
      ⟨ro, hro, hs, hadx, -⟩ | hpay'
  · rcases hkind with hop | hs
    · exact hnotE (hsteps.refs x a hra huE hnc) hop
    · exact stdAxiom_unreached hC hax hw hwf (Nat.le_of_eq hgr.symm) hs had
        (GroupReach.ref hra huE hns)
  · obtain ⟨c', i, hc', hi, hx⟩ := huE
    have e : c' = p := Option.some.inj (hc'.symm.trans hp)
    rw [e, hrefs] at hx
    simp at hx
  · rcases hkind with hop | hs'
    · exact hnotE (axiomSteps_ordered hC hval ro hro hs x hadx a huE hnc) hop
    · exact stdAxiom_unreached hC hax hw hwf (Nat.le_of_eq hgr.symm) hs' had
        (GroupReach.axiomRef hro hs hadx huE hns)
  · rcases payAdds_cases hP hpay' with ⟨hpr, -⟩ | ⟨-, -, -, -, -, p, hp, -, -, hrefs, -⟩
    · have hpa : PayReach t E₀ Pay g a := PayReach.ref hpr huE hns
      rcases hkind with hop | hs
      · exact hnotE (hpay a hpa) hop
      · exact hnotP hs hpa
    · obtain ⟨c', i, hc', hi, hx⟩ := huE
      have e : c' = p := Option.some.inj (hc'.symm.trans hp)
      rw [e, hrefs] at hx
      simp at hx

/-! ## Every group -/

/-- **The order of the references every group's walk follows**, from the run below 33 and from 41
on, and from `hblock` in the well-founded block. -/
theorem walkStepsOrdered_all (hC : CollisionFreeRun calls E₀)
    (hvalAll : ∀ k, ∀ r ∈ roleGroup k, RoleValidationIn calls bAddr t k r)
    (hblock : ∀ g, 33 ≤ g → g ≤ 40 → WalkStepsOrdered t E₀ g) (g : Nat) :
    WalkStepsOrdered t E₀ g := by
  by_cases h : g < 33 ∨ 41 ≤ g
  · exact walkStepsOrdered_of_run hC (hvalAll g) h
  · simp only [not_or, Nat.not_lt] at h
    exact hblock g (by omega) (by omega)

/-- **The order of the records every group's payload reaches**, from `hpay` below 41: from 41 on
every operation is of an earlier group. -/
theorem payloadOpEarlier_all
    (hpay : ∀ g, 6 ≤ g → g < 41 → ∀ x, PayReach t E₀ Pay g x → OpEarlier t g x) :
    ∀ g, 6 ≤ g → ∀ x, PayReach t E₀ Pay g x → OpEarlier t g x := by
  intro g hg x hx
  by_cases h : g < 41
  · exact hpay g hg h x hx
  · intro ro _ hop
    have := (op_group_bounds hop).2
    omega

end Run

end IxVM.Refinement.Binding
