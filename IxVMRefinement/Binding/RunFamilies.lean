import IxVMRefinement.Binding.GroupRank
import IxVMRefinement.Binding.ClosureFold
import IxVMRefinement.Binding.StoreOpOrder

/-! # The family checks of a binding run, group by group

The run's payload and family selection, and what of the family form's clauses is left.

* `runPayload calls bAddr t`: the payload of the run's family checks: at group `g`, the family
  check of the block at `B` under the context at `valLimit g` names `a` as its family record, an
  advice record or a container recursor.
* `runFamOf`, `runAdv`, `runCont`: the family selection of group `g`: a block new in the group,
  routed as modeled, with a family check at the group's limit, selects the family record of one
  such check; the advice and container recursors of a block are those of its checks.
  `runFamOf_famCall`: the clause `GroupFamilyChecks.famCall` of that selection.
* `RemainingFamilyClauses calls bAddr t E₀`: what is not proved of the run's family checks, at
  the store sequence with the run's payload. Each field names the source it comes from.
* `families_of_remaining`: the family form's clauses at a group (`ClosureFam` and
  `FamilyAdmits`), for any rank of the group's new records (`GroupRanked`). -/

set_option linter.unusedVariables false

namespace IxVM.Refinement.Binding

open IxVM.Consistency
open IxVM.Refinement.Typing
open IxVM.Refinement.Typing.FamilyAlias (FamilyCallAtLim)
open IxVM.Refinement.Binding.FamilyOf (FamilyOfBlock)
open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library
open IxVM (F)

/-- **The payload of a run's family checks** (module docstring). -/
def runPayload (calls : List (Call F)) (bAddr : _root_.Address) (t : Ix.Kernel.RoleTable) :
    PayloadRel := fun g B a =>
  ∃ rb cs, FamilyCallAtLim calls bAddr t B rb (some (valLimit g)) cs ∧
    (a = rb ∨ AdviceIn cs a ∨ ContainerRecIn cs a)

/-- **A family check of the block at `B` with the record at `rb` at group `g`'s limit.** -/
def FamCallAt (calls : List (Call F)) (bAddr : _root_.Address) (t : Ix.Kernel.RoleTable)
    (g : Nat) (B rb : _root_.Address) : Prop :=
  ∃ cs, FamilyCallAtLim calls bAddr t B rb (some (valLimit g)) cs

open Classical in
/-- **The family selection of group `g`** (module docstring). -/
noncomputable def runFamOf (calls : List (Call F)) (bAddr : _root_.Address)
    (t : Ix.Kernel.RoleTable) (E₀ : Ixon.Env) (g : Nat) (B : _root_.Address) :
    Option _root_.Address :=
  if h : New (groupStore t E₀ (runPayload calls bAddr t) g)
      (groupStore t E₀ (runPayload calls bAddr t) (g + 1)) B ∧ ModeledRouteAt calls B ∧
      ∃ rb, FamCallAt calls bAddr t g B rb then
    some (Classical.choose h.2.2)
  else none

/-- **The advice of a block's family checks at group `g`.** -/
def runAdv (calls : List (Call F)) (bAddr : _root_.Address) (t : Ix.Kernel.RoleTable)
    (g : Nat) (B a : _root_.Address) : Prop :=
  ∃ rb cs, FamilyCallAtLim calls bAddr t B rb (some (valLimit g)) cs ∧ AdviceIn cs a

/-- **The container recursors of a block's family checks at group `g`.** -/
def runCont (calls : List (Call F)) (bAddr : _root_.Address) (t : Ix.Kernel.RoleTable)
    (g : Nat) (B x : _root_.Address) : Prop :=
  ∃ rb cs, FamilyCallAtLim calls bAddr t B rb (some (valLimit g)) cs ∧ ContainerRecIn cs x

section Run

variable {calls : List (Call F)} {bAddr : _root_.Address} {t : Ix.Kernel.RoleTable}
  {E₀ : Ixon.Env}

theorem runFamOf_spec {g : Nat} {B rb : _root_.Address}
    (h : runFamOf calls bAddr t E₀ g B = some rb) :
    New (groupStore t E₀ (runPayload calls bAddr t) g)
        (groupStore t E₀ (runPayload calls bAddr t) (g + 1)) B ∧
      ModeledRouteAt calls B ∧ FamCallAt calls bAddr t g B rb := by
  unfold runFamOf at h
  split at h
  · rename_i hc
    have e := Option.some.inj h
    subst e
    exact ⟨hc.1, hc.2.1, Classical.choose_spec hc.2.2⟩
  · cases h

/-- The selected record is in the group's payload. -/
theorem runFamOf_payload {g : Nat} {B rb : _root_.Address}
    (h : runFamOf calls bAddr t E₀ g B = some rb) : runPayload calls bAddr t g B rb := by
  obtain ⟨-, -, cs, hcs⟩ := runFamOf_spec h
  exact ⟨rb, cs, hcs, Or.inl rfl⟩

/-- **`GroupFamilyChecks.famCall` of the run's selection.** -/
theorem runFamOf_famCall {g : Nat} :
    ∀ B rb, runFamOf calls bAddr t E₀ g B = some rb →
      New (groupStore t E₀ (runPayload calls bAddr t) g)
          (groupStore t E₀ (runPayload calls bAddr t) (g + 1)) B ∧ ModeledRouteAt calls B ∧
      ∃ cs, FamilyCallAtLim calls bAddr t B rb (some (valLimit g)) cs ∧
        (∀ a, AdviceIn cs a → runAdv calls bAddr t g B a) ∧
        (∀ x, ContainerRecIn cs x → runCont calls bAddr t g B x) := by
  intro B rb h
  obtain ⟨hn, hm, cs, hcs⟩ := runFamOf_spec h
  exact ⟨hn, hm, cs, hcs, fun a ha => ⟨rb, cs, hcs, ha⟩, fun x hx => ⟨rb, cs, hcs, hx⟩⟩

end Run

/-- **What is left of `ClosureRunFacts`** at a group: its fields but `famRefs` (the rank's,
`GroupRanked.famRefs`), `advNotUnit` (`advNotUnit_of_run`) and `roleUnitForm`
(`roleUnitForm_of_run`), which are proved. Each field's source:
* `oldNeeds`: today's circuit, not specified: an address a new unit's step reads that is held
  before the group was checked at the limit of the group that added it (the walk's
  `KernelClaim::run_check` at that group; for a payload record, its family check), or is a
  walked role's record; the step's reading set (`ClosureNeeds`) is wider than what the walk of
  the unit reads, through the family record's and the advice's references.
* `famNonempty`: today's circuit: `KernelModeled::check_family` loads the block's members and
  `check_recs` compares the record entry by entry against the flattened block; not specified.
* `noPinned`: unknown; it is a statement about the basis pins and the keys of the new records
  (`PinnedBasis`), for which no reading of the circuit is written.
* `keptRoles`: today's circuit: the record is held (`groupStore_kept`), in Lean's logic with its
  block (`RootsSafe.bound`), and checked at the group's limit (the root's walked record,
  `unitCheckedAt_of_topRec`); not exported is that the bound record is no block record:
  `get_ci`'s head at the bound address (`Claim.GetCIHead`, no arm for a block), which
  `RoleVal.ValidateRoleIn.bound_loaded` drops.
* `routeNew`: today's circuit: the modeled arm of `KernelCheck::check_const` reaches
  `KernelModeled::check_modeled_block` and `check_family`; a block's route over the closure's
  store against the route the circuit read; not specified.
* `readsDown`: today's circuit with the run's store (`LoadedReads.RunStore`): a reading of a held
  address reads held records (`readsIn_of_agree`); not assembled for the closure's store. -/
structure RunFactsLeft (ρ : BRun) (t : Ix.Kernel.RoleTable) (g : Nat) (R R' : Ixon.Env)
    (famOf : _root_.Address → Option _root_.Address)
    (adv : _root_.Address → _root_.Address → Prop) : Prop where
  oldNeeds : ∀ A x, New R R' A → ClosureNeeds ρ.E₀ famOf adv A x →
    (recordOf R x).isSome = true →
    (∃ c n, recordOf R x = some c ∧ (∀ ms, c.info ≠ .muts ms) ∧ InLogic c ∧
      (∀ cb, recordOf R (Ix.Cert.ownerOf x c) = some cb → InLogic cb) ∧ ρ.checked x n) ∨
    ∃ r, walkedRole r = true ∧ Ix.SpecDigest.groupOf r < g ∧ t.addressOf? r = some x
  famNonempty : ∀ B rb, famOf B = some rb → ∃ cb ms, recordOf ρ.E₀ B = some cb ∧
    cb.info = .muts ms ∧ 0 < ms.size
  noPinned : ∀ A c x ci, New R R' A → recordOf R' A = some c → ConstAddrOf A c x →
    PinnedBasis ci → ci.name ≠ keyOf t x
  keptRoles : ∀ r ∈ roleGroup g, (keptRole r ∨ r ∈ preludeRoles) →
    ¬ (r ∈ RoleOps.opRoles ∨ r ∈ standardAxioms) → ∀ a, t.addressOf? r = some a →
    ∃ c, recordOf R' a = some c ∧ (∀ ms, c.info ≠ .muts ms) ∧ InLogic c ∧
      (∀ cb, recordOf R' (Ix.Cert.ownerOf a c) = some cb → InLogic cb) ∧
      ((recordOf R a).isSome = true → ∃ n, ρ.checked a n)
  routeNew : ∀ R₁ B, ClosureStore t g R R' R₁ → New R R' B →
    Route.blockRoute R₁ B = some true → ∃ rb, famOf B = some rb
  readsDown : ∀ R₁ x ci₀, ClosureStore t g R R' R₁ → (recordOf R x).isSome = true →
    IxVM.Consistency.Reads t R₁ x ci₀ → IxVM.Consistency.Reads t R x ci₀

/-- **What is left of the run's family checks**, at the store sequence with the run's payload
(`Rs g` below is `groupStore t E₀ (runPayload calls bAddr t) g`). Status: premises; nothing
proves them of any run. Each field is tagged with its source: today's circuit (not yet specified),
a named change of the circuit source, or unknown.
* `payloadFacts`: the facts the store's clauses need of the payload's records (`PayloadFacts`:
  `KernelModeled::check_family`, `check_advice_record`, `advice_refs_ok`, `check_witness`,
  `check_container_rec`, `container_refs_ok`, `check_recs`). Source: per field, in
  `PayloadFacts`.
* `payloadRanked`: at a group with a payload, a rank of its new records (`GroupRanked`): the
  order has no cycle among them (content addressing, with `check_advice_record`'s refusal of a
  modeled block, of a projection of the modeled block and of a recursor projection,
  `advice_refs_ok`'s earlier advice and witnesses, and `walk_from_block`'s paths in the block's
  dependency closure). Source: today's circuit, with the change of
  `KernelModeled::check_container_rec` that refuses a container recursor naming itself among its
  container block's used references.
* `modeled`, `family`, `claimed`: the fields of `GroupFamilyChecks` but `famCall`
  (`runFamOf_famCall`): the modeled arm of `KernelCheck::check_const` reaches
  `KernelModeled::check_modeled_block` and `check_family` (`modeled`); `check_family` and
  `check_recs` check the record position by position against the flattened block (`family`,
  with a change of `check_recs` that refuses an empty record under a group's validation); a new
  block of recursors is a selected record or a second family record checked by `check_family`
  (`claimed`). Source: `modeled` today's circuit; `family` the change of `check_family` and
  `check_recs` that takes the family record as the reconstruction of the block's recursors, and
  the change that compares nested pins in `check_recs`; `claimed` the first of these changes.
* `runFacts`: what is left of `ClosureRunFacts` at the group (`RunFactsLeft`, which names each
  field's source); `famRefs` is the rank's, `advNotUnit` and `roleUnitForm` are proved
  (`families_of_remaining`).
* `famNew`: the selected record of a new block is new in the group. Source: unknown (no reading
  of the circuit excludes a family record an earlier group stored).
* `payloadChecked`: a new unit reached through the payload is checked at the group's limit by a
  check of a unit (`KernelClaim::run_check` in `check_advice_record`, `check_container_rec`;
  `KernelClaim::check_muts_all` for an advice block), or is a selected family record of a new
  block (checked by `check_recs`). Source: today's circuit, with the walk's assertions on inner
  references (`assert_safe_used_refs`, `assert_not_block_ref`) added to the advice, container
  and witnessed-reference checks, for what the payload's records reference. -/
structure RemainingFamilyClauses (calls : List (Call F)) (bAddr : _root_.Address)
    (t : Ix.Kernel.RoleTable) (E₀ : Ixon.Env) : Prop where
  payloadFacts : PayloadFacts t E₀ (runPayload calls bAddr t)
  payloadRanked : ∀ g, 6 ≤ g → g < 77 → (∃ B a, runPayload calls bAddr t g B a) →
    ∃ rank, GroupRanked t E₀ (runPayload calls bAddr t) g (runFamOf calls bAddr t E₀ g)
      (runAdv calls bAddr t g) (runCont calls bAddr t g) rank
  modeled : ∀ g, 6 ≤ g → g < 77 → ∀ B cb (ms : Array Ixon.MutConst),
    New (groupStore t E₀ (runPayload calls bAddr t) g)
      (groupStore t E₀ (runPayload calls bAddr t) (g + 1)) B →
    recordOf E₀ B = some cb → InLogic cb → cb.info = .muts ms →
    (∀ m ∈ ms.toList, ∃ ind, m = Ixon.MutConst.indc ind) → ModeledRouteAt calls B →
    (∃ k, k < ms.size ∧ Claim.MemberCheckedLimAt calls bAddr t B ms k (some (valLimit g))) →
    ∃ rb, runFamOf calls bAddr t E₀ g B = some rb
  family : ∀ g, 6 ≤ g → g < 77 → ∀ B rb, runFamOf calls bAddr t E₀ g B = some rb →
    ∃ cb ms crb rs flat, FamilyOfBlock E₀ B cb ms rb crb rs flat
  claimed : ∀ g, 6 ≤ g → g < 77 → ∀ (A : _root_.Address) (c : Ixon.Constant)
    (rs' : Array Ixon.MutConst),
    New (groupStore t E₀ (runPayload calls bAddr t) g)
      (groupStore t E₀ (runPayload calls bAddr t) (g + 1)) A →
    recordOf E₀ A = some c → c.info = .muts rs' → 0 < rs'.size →
    (∀ m ∈ rs'.toList, ∃ r, m = Ixon.MutConst.recr r) →
    (∃ B, runFamOf calls bAddr t E₀ g B = some A) ∨
      ∃ B cs, FamilyCallAtLim calls bAddr t B A (some (valLimit g)) cs
  runFacts : ∀ g, 6 ≤ g → g < 77 → ∀ rk : Nat → _root_.Address → Nat,
    RunFactsLeft (observedRun calls bAddr t E₀ rk) t g
      (groupStore t E₀ (runPayload calls bAddr t) g)
      (groupStore t E₀ (runPayload calls bAddr t) (g + 1)) (runFamOf calls bAddr t E₀ g)
      (runAdv calls bAddr t g)
  famNew : ∀ g, 6 ≤ g → g < 77 → ∀ B rb, runFamOf calls bAddr t E₀ g B = some rb →
    New (groupStore t E₀ (runPayload calls bAddr t) g)
      (groupStore t E₀ (runPayload calls bAddr t) (g + 1)) rb
  payloadChecked : ∀ g, 6 ≤ g → g < 77 → ∀ a c,
    PayReach t E₀ (runPayload calls bAddr t) g a →
    New (groupStore t E₀ (runPayload calls bAddr t) g)
      (groupStore t E₀ (runPayload calls bAddr t) (g + 1)) a →
    recordOf (groupStore t E₀ (runPayload calls bAddr t) (g + 1)) a = some c → UnitKind c →
    UnitCheckedAt calls bAddr t E₀ a (some (valLimit g)) ∨
      ∃ B, runFamOf calls bAddr t E₀ g B = some a ∧
        New (groupStore t E₀ (runPayload calls bAddr t) g)
          (groupStore t E₀ (runPayload calls bAddr t) (g + 1)) B

section Families

variable {calls : List (Call F)} {bAddr : _root_.Address} {t : Ix.Kernel.RoleTable}
  {E₀ : Ixon.Env}

/-- **An address the family check of a selected block names is reached through the payload**: the
selected block is a block record (`FamilyOfBlock.block`), so the group reaches it by its walk or
through its payload. -/
theorem runPayload_reach (hC : CollisionFreeRun calls E₀) (hb : BasisRowsLoaded E₀)
    (hax : AxiomRolesDeclared t E₀) (hR : RemainingFamilyClauses calls bAddr t E₀) {g : Nat}
    (hg6 : 6 ≤ g) (hg : g < 77)
    {recs : List (Claim.TopRec calls bAddr t (some (valLimit g)))}
    (hw : GroupWalked calls bAddr t E₀ g recs) {B rb a : _root_.Address}
    (hfam : runFamOf calls bAddr t E₀ g B = some rb)
    (hpay : runPayload calls bAddr t g B a) :
    PayReach t E₀ (runPayload calls bAddr t) g a := by
  have hP := hR.payloadFacts
  obtain ⟨hnew, -, -⟩ := runFamOf_spec hfam
  obtain ⟨-, -, -, hadd, -⟩ := new_groupStore hb hg6 hnew
  obtain ⟨cb, ms, crb, rs, flat, hF⟩ := hR.family g hg6 hg B rb hfam
  have hB := hF.block
  rcases groupAdds_cases hC hax hw hadd with ⟨hra, -⟩ | ⟨-, -, -, -, p, hp, hproj, -⟩ |
      ⟨-, -, -, -, c₂, ax, hc₂, hinfo, -⟩ | hpa
  · exact PayReach.payload hra hpay
  · have e : p = cb := Option.some.inj (hp.symm.trans hB.record)
    rw [e] at hproj
    exact (proj_not_block hproj ⟨ms, hB.muts⟩).elim
  · have e : c₂ = cb := Option.some.inj (hc₂.symm.trans hB.record)
    rw [e, hB.muts] at hinfo
    cases hinfo
  · rcases payAdds_cases hP hpa with ⟨hrB, -⟩ | ⟨-, -, -, -, -, p, hp, hproj, -⟩
    · exact PayReach.payloadOf hrB hpay
    · have e : p = cb := Option.some.inj (hp.symm.trans hB.record)
      rw [e] at hproj
      exact (proj_not_block hproj ⟨ms, hB.muts⟩).elim

/-- **An address the family check of a selected block names is held after the group**
(`runPayload_reach`). -/
theorem runPayload_held (hC : CollisionFreeRun calls E₀) (hb : BasisRowsLoaded E₀)
    (hax : AxiomRolesDeclared t E₀) (hR : RemainingFamilyClauses calls bAddr t E₀) {g : Nat}
    (hg6 : 6 ≤ g) (hg : g < 77)
    {recs : List (Claim.TopRec calls bAddr t (some (valLimit g)))}
    (hw : GroupWalked calls bAddr t E₀ g recs) {B rb a : _root_.Address}
    (hfam : runFamOf calls bAddr t E₀ g B = some rb)
    (hpay : runPayload calls bAddr t g B a) :
    (recordOf (groupStore t E₀ (runPayload calls bAddr t) (g + 1)) a).isSome = true := by
  have hreach := runPayload_reach hC hb hax hR hg6 hg hw hfam hpay
  obtain ⟨c, hc⟩ := hR.payloadFacts.record g a hreach
  rw [(groupStore_recordOf hb (Nat.le_succ_of_le hg6)).mpr
    ⟨storedBelow_of_adds hg6 (GroupAdds.payReach hreach), hc⟩]
  rfl

/-- **`ClosureRunFacts.roleUnitForm` of every run**: the record of an operation is a definition
(`validate_role_op_obs`: `validate_op` asserts a standalone definition), and the record of a
standard axiom an axiom record (`AxiomRolesDeclared`). -/
theorem roleUnitForm_of_run (hC : CollisionFreeRun calls E₀) (hb : BasisRowsLoaded E₀)
    (hax : AxiomRolesDeclared t E₀) (hcheck : t.check = .ok ()) {Pay : PayloadRel} {g : Nat}
    (hg6 : 6 ≤ g) (hval : ∀ r ∈ roleGroup g, RoleValidationIn calls bAddr t g r) :
    ∀ a c, RoleUnitAt t g a → New (groupStore t E₀ Pay g) (groupStore t E₀ Pay (g + 1)) a →
      recordOf (groupStore t E₀ Pay (g + 1)) a = some c →
      (∃ d, c.info = .defn d) ∨ ∃ ax, c.info = .axio ax := by
  rintro a c ⟨r, hr, had, hk⟩ - hc
  have hE : recordOf E₀ a = some c := ((groupStore_recordOf hb (Nat.le_succ_of_le hg6)).mp hc).2
  rcases hk with hop | hs
  · obtain ⟨a₁, c₁, d, had₁, hc₁, hd, -⟩ :=
      validate_role_op_obs hcheck hC.runStore hC.hashedStored
        (show RoleVal.ValidateRoleIn calls bAddr t g r from hval r hr) hop
    have ea : a₁ = a := Option.some.inj (had₁.symm.trans had)
    rw [ea, hE] at hc₁
    left
    refine ⟨d, ?_⟩
    rw [Option.some.inj hc₁]
    exact hd
  · obtain ⟨c₂, ax, hc₂, hi, -⟩ := hax r hs a had
    right
    refine ⟨ax, ?_⟩
    rw [Option.some.inj (hE.symm.trans hc₂)]
    exact hi

/-- **`ClosureRunFacts.advNotUnit` of every run**, given the order of the records the payload
reaches: an advice record of a selected block's family check is reached through the payload
(`runPayload_reach`), so it is no operation of the group (`OpEarlier`) and no axiom record
(`PayloadFacts.notAxiomLike`). -/
theorem advNotUnit_of_run (hC : CollisionFreeRun calls E₀) (hb : BasisRowsLoaded E₀)
    (hax : AxiomRolesDeclared t E₀) (hR : RemainingFamilyClauses calls bAddr t E₀) {g : Nat}
    (hg6 : 6 ≤ g) (hg : g < 77)
    {recs : List (Claim.TopRec calls bAddr t (some (valLimit g)))}
    (hw : GroupWalked calls bAddr t E₀ g recs)
    (hpay : ∀ x, PayReach t E₀ (runPayload calls bAddr t) g x → OpEarlier t g x) :
    ∀ B rb a, runFamOf calls bAddr t E₀ g B = some rb → runAdv calls bAddr t g B a →
      ¬ (RoleUnitAt t g a ∧ New (groupStore t E₀ (runPayload calls bAddr t) g)
        (groupStore t E₀ (runPayload calls bAddr t) (g + 1)) a) := by
  rintro B rb a hfam ⟨rb', cs, hcs, hin⟩ ⟨⟨r, hr, had, hk⟩, -⟩
  have hreach := runPayload_reach hC hb hax hR hg6 hg hw hfam ⟨rb', cs, hcs, Or.inr (Or.inl hin)⟩
  rcases hk with hop | hs
  · have h1 := hpay a hreach r had hop
    rw [groupOf_of_mem_roleGroup hr] at h1
    exact Nat.lt_irrefl g h1
  · obtain ⟨c, ax, hc, hi, -⟩ := hax r hs a had
    exact hR.payloadFacts.notAxiomLike g a c hreach hc (Or.inl ⟨ax, hi⟩)

/-- **The family form's clauses at a group**, for a rank of its new records: `ClosureRunFacts`
from what is left of it (`RemainingFamilyClauses.runFacts`), the rank's `famRefs`, and
`advNotUnit`, `roleUnitForm` proved of the run. -/
theorem families_of_remaining (hC : CollisionFreeRun calls E₀) (hb : BasisRowsLoaded E₀)
    (hax : AxiomRolesDeclared t E₀) (hR : RemainingFamilyClauses calls bAddr t E₀)
    (hcheck : t.check = .ok ())
    {rk : Nat → _root_.Address → Nat} {g : Nat} (hg6 : 6 ≤ g) (hg : g < 77)
    (hval : ∀ r ∈ roleGroup g, RoleValidationIn calls bAddr t g r)
    {recs : List (Claim.TopRec calls bAddr t (some (valLimit g)))}
    (hw : GroupWalked calls bAddr t E₀ g recs)
    (hrank : GroupRanked t E₀ (runPayload calls bAddr t) g (runFamOf calls bAddr t E₀ g)
      (runAdv calls bAddr t g) (runCont calls bAddr t g) (rk g))
    (hpay : ∀ x, PayReach t E₀ (runPayload calls bAddr t) g x → OpEarlier t g x) :
    ClosureFam calls (observedRun calls bAddr t E₀ rk) t g
        (groupStore t E₀ (runPayload calls bAddr t) g)
        (groupStore t E₀ (runPayload calls bAddr t) (g + 1)) (runFamOf calls bAddr t E₀ g)
        (runAdv calls bAddr t g) (runCont calls bAddr t g) ∧
      FamilyAdmits (observedRun calls bAddr t E₀ rk) t g
        (groupStore t E₀ (runPayload calls bAddr t) g)
        (groupStore t E₀ (runPayload calls bAddr t) (g + 1)) (runFamOf calls bAddr t E₀ g)
        (runAdv calls bAddr t g) (runCont calls bAddr t g) := by
  have hL := hR.runFacts g hg6 hg rk
  refine ⟨⟨⟨bAddr, ?_⟩, ?_⟩, ?_⟩
  · exact
      { modeled := hR.modeled g hg6 hg
        famCall := runFamOf_famCall
        family := hR.family g hg6 hg
        claimed := hR.claimed g hg6 hg }
  · exact
      { oldNeeds := hL.oldNeeds
        famRefs := hrank.famRefs
        famNonempty := hL.famNonempty
        advNotUnit := advNotUnit_of_run hC hb hax hR hg6 hg hw hpay
        noPinned := hL.noPinned
        roleUnitForm := roleUnitForm_of_run hC hb hax hcheck hg6 hval
        keptRoles := hL.keptRoles
        routeNew := hL.routeNew
        readsDown := hL.readsDown }
  · exact
      { famNew := fun B rb h hB => ⟨hR.famNew g hg6 hg B rb h, hrank.fam B rb h hB⟩
        advice := fun B rb a h hB ha => by
          obtain ⟨rb', cs, hcs, hin⟩ := ha
          exact ⟨runPayload_held hC hb hax hR hg6 hg hw h ⟨rb', cs, hcs, Or.inr (Or.inl hin)⟩,
            fun hn => hrank.advice B rb a h hB ⟨rb', cs, hcs, hin⟩ hn⟩
        container := fun B rb x h hB hx => by
          obtain ⟨rb', cs, hcs, hin⟩ := hx
          exact ⟨runPayload_held hC hb hax hR hg6 hg hw h ⟨rb', cs, hcs, Or.inr (Or.inr hin)⟩,
            fun hn => hrank.container B rb x h hB ⟨rb', cs, hcs, hin⟩ hn⟩
        checked := fun a c hn hc hu => by
          rcases groupStore_checked hC hb hax hR.payloadFacts hg6 hw a c hn hc hu with h | h
          · exact Or.inl h
          · exact hR.payloadChecked g hg6 hg a c h hn hc hu }

end Families

end IxVM.Refinement.Binding
