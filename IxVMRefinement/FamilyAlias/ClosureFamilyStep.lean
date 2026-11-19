import IxVMRefinement.FamilyAlias.BlockRowCheck
import IxVMRefinement.FamilyAlias.TysCanon
import IxVMRefinement.Binding.ClosureUnitDispatch
import IxVMRefinement.Binding.ReadsAgree

/-! # The closure's step of a new block with its family record, at the binding fold's clause

`closureFamilySteps_of_check`: the binding fold's step of a new block of a group's closure with
its selected family record (`Binding.ClosureFamilySteps`), at every group of every binding run,
from what the family check of the block gives at the closure (`ClosureFamilyCheck`, the binding
fold's form of `FamilyBlockCheck`):

* `seam`: the family as read, the facts of its check, the selected annotated types and
  right-hand sides as the circuit loads them (`FamilyTysCanon`), and the companion facts of each
  recursor at its selected type at every record store for the closure's store
  (`FamRecsCompanion`), at the prefix, over a record store for the closure's store that the run's
  calls are good for;
* `recRefs`: each reference the family record uses is covered at the group's validation limit,
  or is one a step needs stored.

The step is taken once, over a store `Ec` the run is good for (`BindingRun.stepStores`) at the
group's validation limit; the new constants (`famStepConclusion_installed`: the members as the
record installs them from the selected `tys` and `rhsss`) do not depend on the store. The seam of
the loads (`FamilyMembersCanon`) holds at that installation (`familyMembersCanon_of_tys`). The
fold's clause is then kept with the same registry at every record store for the closure's store
and every carried limit within the groups (`famStepKeeps_with`): the block is modeled at each of
them (its route over the closure's store, which is closed under what its records use,
`blockRoute_recordsFor`), the load facts hold there (`famLoadCtx_at`), and so do the companion
facts of each new recursor (`recCompanionFacts_of_tys`, with the store invariant after the step).
What the step reads of the run beside the two facts:

* the check of the block at the group's validation limit (`FamilyAdmits.checked`, the block being
  claimed by no block) and its first member's dispatch, on the modeled route of the block's family
  check (`GroupFamilyChecks.famCall`): the route at the step's store (`blockRoute_of_modeledRoute`),
  the constructors' shapes and a field in the constructor of a unit-like block (`famCtorTrees_at`,
  `famUnitFree_at`);
* the run's facts at the group: the block's references are no inert axiom's (handed to the seam)
  and are references a step needs stored (`ClosureRunFacts.famNotInert`, `.famNeedOk`);
* key freedom of the two records' constant addresses (`Binding.plain_keyFree`);
* the pinned equality, from the invariant's table shape (`eqPin_of_shape`).

The family record is installed after the step (`familyInstalled_of_step`): each of its constant
addresses holds the reading of a recursor projection, a recursor with a model companion. -/

universe u

namespace IxVM.Refinement.Typing.FamilyAlias

open IxVM.Consistency
open Aiur.Generic.SourceSemantics (Call)
open IxVM (F)
open Ix.Kernel (ConstantInfo ConstantVal)
open Ix.Kernel.Semantics (NativeFam DeclIndRenRunJ)
open IxVM.Refinement.Typing.TwinFamily (FamilyInstalled)
open IxVM.Refinement.Decl.FamilyAlias (AliasGroup famJ FamilyAdvice FamilyCheckFacts isRecursor
  auxKey_ne_of_isBaseKey find?_append_none)

set_option linter.unusedVariables false

/-! ## The route of the block -/

/-- **A block the store routes as modeled is modeled at the store**: a bounded run of the
dispatch hashing no collision with the store answers the store's route. -/
theorem modeledAt_of_blockRoute {E : Ixon.Env} {B : _root_.Address}
    (h : Route.blockRoute E B = some true) : ModeledAt E B := by
  rintro ⟨bq, h₁, h₁', cs, bb, ev, hnc, hbd, hrep, rfl⟩
  have hv := (Route.block_is_modeled_agrees hnc hbd hrep ev).value true h
  exact Bool.false_ne_true (Route.bit_eq_one ((Route.bit_false.trans hv).trans Route.bit_true))

/-- **The route at a store the run is good for, of a block on the modeled route whose first
member the run checked**: the check observed the dispatch on the block, which answers the store's
route, known under the run's coverage, and the modeled route excludes the answer `0`. -/
theorem blockRoute_of_modeledRoute {calls : List (Call F)} {t : Ix.Kernel.RoleTable}
    {E₀ E : Ixon.Env} (hS : LoadedReads.RunStore calls E₀) (hst : StepStore calls t E₀ E)
    (hcanon : L1.CanonicalHashCoverage E calls) {bAddr A : _root_.Address}
    {ms : Array Ixon.MutConst} {lim : Option Nat}
    (hall : ∀ m ∈ ms.toList, ∃ ind, m = Ixon.MutConst.indc ind)
    (hm0 : Claim.MemberCheckedLimAt calls bAddr t A ms 0 lim)
    (hroute : ModeledRouteAt calls A) : Route.blockRoute E A = some true := by
  obtain ⟨bp, r, h, h', cs, b, ev, hsub, hb, hbA⟩ :=
    Claim.MemberCheckedLimAt.dispatch hS hall hm0
  have g : Core.Good ⟨E, Ix.Kernel.Env.empty, t, none⟩ cs :=
    (hst.good Ix.Kernel.Env.empty none).sub hsub
  have hag := Route.block_is_modeled_agrees (E := E) g.1 g.2 hb ev
  obtain ⟨v, hv⟩ := hag.known (canonicalHashCoverage_sub hsub hcanon)
  have hr := hag.value v hv
  have hne := hroute bp r h h' cs b ev hsub hb hbA
  rw [← hbA]
  cases v with
  | false => exact absurd (hr.trans Route.bit_false) hne
  | true => exact hv

/-- **The route of a block over a record store for a store closed under what its records use**
is its route over that store: the route reads the records at the block's references and members,
which the closed store holds. -/
theorem blockRoute_recordsFor {S E : Ixon.Env} (hS : UsedClosed S) (hE : RecordsFor S E)
    {B : _root_.Address} {cb : Ixon.Constant} (hB : recordOf S B = some cb) :
    Route.blockRoute E B = Route.blockRoute S B := by
  refine Binding.blockRoute_congr hB (Binding.recordOf_of_recordsFor hE hB) (fun a ha => ?_)
  have hRa : (recordOf S a).isSome = true := by
    rcases ha with ⟨i, hi, hx⟩ | ⟨ms', i, m, hms', hm, hx⟩
    · exact (hS.1 B cb hB).2 i hi a hx
    · rw [hx]
      exact Option.isSome_iff_exists.mpr ⟨_, (hS.2 B cb ms' hB hms' i m hm).1⟩
  obtain ⟨ca, hca⟩ := Option.isSome_iff_exists.mp hRa
  unfold Route.isIndAt
  rw [Binding.recordOf_of_recordsFor hE hca, hca]

/-! ## The walk's facts at the block, over a store the run is good for -/

/-- **A block of one inductive on the modeled route whose member has no index and one
constructor has a field in that constructor**, from the check of its member over a store the run
is good for (`famUnitFree_of_run` at a step store). -/
theorem famUnitFree_at {calls : List (Call F)} {t : Ix.Kernel.RoleTable} {E₀ E : Ixon.Env}
    (hst : StepStore calls t E₀ E) {bAddr A : _root_.Address} {c : Ixon.Constant}
    {ms : Array Ixon.MutConst} {lim : Option Nat} (hB : FamBlockRecord E₀ A c ms)
    (hR : Route.blockRoute E A = some true)
    (hmem : ∀ k, k < ms.size → Claim.MemberCheckedLimAt calls bAddr t A ms k lim) :
    ∀ ind, c.info = .muts #[.indc ind] → ind.indices.toNat = 0 → ind.ctors.size = 1 →
      ∀ ct, ind.ctors[0]? = some ct → ct.fields.toNat ≠ 0 := by
  intro ind hmuts hidx hsz ct hct hf0
  have hmod : ModeledAt E A := modeledAt_of_blockRoute hR
  have hms : ms = #[.indc ind] := Ixon.ConstantInfo.muts.inj (hB.muts.symm.trans hmuts)
  subst hms
  have hrec : ∀ a d, recordOf E₀ a = some d → recordOf E a = some d := fun a d hd' =>
    (recordOf_eq_recordAt_of_decoded hst.decoded a).trans (hst.runRecord a d hd')
  obtain ⟨ct', T, Bd, hct', -, hET, hpeel, hhd, hlen, hat⟩ :=
    modeledCtor_trees (c := ⟨E, Ix.Kernel.Env.empty, t, none⟩)
      (hst.good Ix.Kernel.Env.empty none) (hrec _ _ hB.record) hmuts
      (hrec _ _ (hB.members 0 (.indc ind) rfl)) hmod (hmem 0 Nat.zero_lt_one) 0 (by omega)
  have e4 : ct' = ct := Option.some.inj (hct'.symm.trans hct)
  subst ct'
  rw [hf0, Nat.add_zero] at hpeel
  rw [hidx, Nat.add_zero] at hlen
  have hargs : ∀ X ∈ Bd.args, X = .atom := by
    intro X hX
    obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hX
    have hklt : k < Bd.args.length := (List.getElem?_eq_some_iff.mp hk).1
    rw [hat k (by omega)] at hk
    exact (Option.some.inj hk).symm
  have hans := ctorAnswer_spine_atoms (isInd := Route.isIndAt E) hET hpeel hhd hargs
  have hctl : ind.ctors.toList = [ct] := by
    obtain ⟨x, hx⟩ := Claim.array_of_size_one ind.ctors hsz
    rw [hx] at hct
    have e5 : x = ct := by simpa using hct
    simp [hx, e5]
  rw [blockRoute_one (hrec _ _ hB.record) hmuts hctl, hans] at hR
  exact Bool.false_ne_true (Option.some.inj hR)

/-- **The constructors' shapes at a block of one inductive on the modeled route**, from the
check of its member over a store the run is good for (`famCtorTrees_of_run` at a step store). -/
theorem famCtorTrees_at {calls : List (Call F)} {t : Ix.Kernel.RoleTable} {E₀ E : Ixon.Env}
    (hst : StepStore calls t E₀ E) {bAddr A : _root_.Address} {c : Ixon.Constant}
    {ms : Array Ixon.MutConst} {lim : Option Nat} (hB : FamBlockRecord E₀ A c ms)
    (hR : Route.blockRoute E A = some true)
    (hmem : ∀ k, k < ms.size → Claim.MemberCheckedLimAt calls bAddr t A ms k lim) :
    ∀ ind, c.info = .muts #[.indc ind] → ∀ j < ind.ctors.size,
      ∃ (ct : Ixon.Constructor) (T Bd : Route.ScanTree),
        ind.ctors[j]? = some ct ∧ ct.params.toNat = ind.params.toNat ∧
        Route.ExprTree c.refs.toList
          (L1.blockRecurAddrs A (#[.indc ind] : Array Ixon.MutConst).toList)
          c.sharing.toList 4294967295 ct.typ T ∧
        T.peel (ct.params.toNat + ct.fields.toNat) = some Bd ∧ (∃ a, Bd.head = .const a) ∧
        Bd.args.length = ct.params.toNat + ind.indices.toNat ∧
        ∀ k < ct.params.toNat, Bd.args[k]? = some .atom := by
  intro ind hmuts
  have hmod : ModeledAt E A := modeledAt_of_blockRoute hR
  have hms : ms = #[.indc ind] := Ixon.ConstantInfo.muts.inj (hB.muts.symm.trans hmuts)
  subst hms
  have hrec : ∀ a d, recordOf E₀ a = some d → recordOf E a = some d := fun a d hd' =>
    (recordOf_eq_recordAt_of_decoded hst.decoded a).trans (hst.runRecord a d hd')
  exact modeledCtor_trees (c := ⟨E, Ix.Kernel.Env.empty, t, none⟩)
    (hst.good Ix.Kernel.Env.empty none) (hrec _ _ hB.record) hmuts
    (hrec _ _ (hB.members 0 (.indc ind) rfl)) hmod (hmem 0 Nat.zero_lt_one)

/-! ## The family record installed -/

/-- **The family record is installed after the family step**: at each of its constant addresses
the step stores the reading of a recursor projection (`FamDeclReads`), a recursor
(`isRecursor_of_reads_rPrj`, `StoredAs`) new in the step, which has a model companion
(`hasModel_declIndRenJ`). -/
theorem familyInstalled_of_step {t : Ix.Kernel.RoleTable} (htwf : t.wf = true) {E₀ : Ixon.Env}
    {B rb : _root_.Address} {cb crb : Ixon.Constant} {rs : Array Ixon.MutConst}
    (hrb : FamRecRecord E₀ rb crb rs) {env : Ix.Kernel.Env .anon}
    {h : Ix.Kernel.Key .anon → Ix.Kernel.Key .anon} {as blk new : List (ConstantInfo .anon)}
    (hg : AliasGroup env h as) (hreads : FamDeclReads t E₀ B cb rb crb blk)
    (hd : DeclIndRenRunJ (famJ h) ⟨as ++ env.consts⟩ blk ⟨new ++ env.consts⟩)
    (hst : ∀ ci ∈ blk, ∃ c', (⟨new ++ env.consts⟩ : Ix.Kernel.Env .anon).find? ci.name = some c' ∧
      StoredAs c' ci)
    (hfresh : ∀ x, FamAddr B cb rb crb x → env.find? (keyOf t x) = none) :
    FamilyInstalled t ⟨new ++ env.consts⟩ rb crb := by
  intro x hx
  have hxF : FamAddr B cb rb crb x := Or.inr hx
  obtain ⟨ci₀, hci₀, hk⟩ := hreads.2.2.1 x hxF
  obtain ⟨y, -, hy, hry⟩ := hreads.2.1 ci₀ hci₀
  have hyx : y = x := Core.keyOf_inj htwf (hy.symm.trans hk)
  rw [hyx] at hry
  have hisR : isRecursor ci₀ = true := by
    rcases hx with ⟨-, hs⟩ | ⟨ms, i, m, hms, hm, hxm | ⟨ind, j, hind, -, -⟩⟩
    · exact (standalone_not_block hs ⟨rs, hrb.muts⟩).elim
    · have hrs : rs = ms := Ixon.ConstantInfo.muts.inj (hrb.muts.symm.trans hms)
      subst hrs
      obtain ⟨r, rfl⟩ := hrb.recrs m (by simpa using Array.mem_of_getElem? hm)
      have hrec : recordOf E₀ x = some (memberProjection rb i (.recr r)) := by
        rw [hxm]
        exact hrb.members i _ hm
      exact isRecursor_of_reads_rPrj (p := ⟨i.toUInt64, rb⟩) hry hrec rfl
    · have hrs : rs = ms := Ixon.ConstantInfo.muts.inj (hrb.muts.symm.trans hms)
      subst hrs
      obtain ⟨r, hr⟩ := hrb.recrs m (by simpa using Array.mem_of_getElem? hm)
      rw [hind] at hr
      exact nomatch hr
  obtain ⟨c', hc', hS⟩ := hst ci₀ hci₀
  rw [hk] at hc'
  cases ci₀ with
  | recInfo cv mI rP rules =>
    obtain ⟨cv', rules', hcv, -, -⟩ := storedAs_rec hS
    subst hcv
    refine ⟨⟨cv', mI, rP, rules', hc'⟩, ?_⟩
    refine Decl.FamilyAlias.hasModel_declIndRenJ hd hc' ?_
    refine find?_append_none as (fun b hb heq => ?_) (hfresh x hxF)
    obtain ⟨n, d, hn⟩ := AliasGroup.name_aux hg b hb
    rw [hn] at heq
    exact auxKey_ne_of_isBaseKey (Decl.isBaseKey_keyOf t x) heq
  | _ => exact absurd hisR Bool.false_ne_true

/-! ## What the family check gives the closure's step -/

/-- **What the family check of the block at `B` with its family record at `rb` hands the closure's
step**, at the closure's store `R₁` of group `g` (module docstring). Each field is the circuit
side's, open until the circuit's family changes, as the fields of `FamilyBlockCheck`:

* `seam`: from `KernelModeled::check_family` and the readers of its loads, over a record store
  for `R₁` the run's calls are good for, at the group's validation limit; the block's inert
  clause is handed (the run's facts, `ClosureRunFacts.famNotInert`); with the family as read and
  the selected `tys` and `rhsss`, the members' and recursors' loads of `members_val` and
  `check_recs` at those selected forms (`FamilyTysCanon`), and the companion facts of each
  recursor at its selected type from `KernelModeled::check_recs` and `check_rules`
  (`FamRecsCompanion`), at every record store for `R₁` (the clause the step keeps is asked at
  each of them);
* `recRefs`: from `KernelModeled::check_family`'s `family_refs_ok`, whose
  `assert_inner_refs_safe` covers every reference the family record uses
  (`KernelClaim::assert_safe_used_refs`, which reads the safety of the record and its owner unless
  `KernelRoles::walk_covered` answers `1`, and `assert_used_not_block`, with
  `KernelClaim::assert_not_block_ref`). -/
structure ClosureFamilyFacts (L : Ix.Kernel.Env .anon → NativeFam .anon → Prop)
    (calls : List (Call F)) (t : Ix.Kernel.RoleTable) (g : Nat) (R₁ : Ixon.Env)
    (envT : Ix.Kernel.Env .anon) (E₀ : Ixon.Env) (B : _root_.Address) (cb : Ixon.Constant)
    (rb : _root_.Address) (crb : Ixon.Constant) (adv : _root_.Address → Prop) : Prop where
  /-- The seam: the family as read, the facts of its check, the selected annotated types and
  right-hand sides as the circuit loads them, and the companion facts of each recursor of the
  family at its selected type at every record store for `R₁`, at each environment the step is
  handed, over a record store the run is good for. -/
  seam : ∀ Ec : Ixon.Env, RecordsFor R₁ Ec → StepStore calls t E₀ Ec →
    ∀ env : Ix.Kernel.Env .anon,
    (∀ ci ∈ envT.consts, ci ∈ env.consts) → (env.consts.map (·.name)).Nodup →
    Decl.PrefixInv.{u} Ec t (some (Binding.valLimit g)) env → FoldExtra.{u} L t Ec env →
    InertClause t cb →
    (∀ x, UsedRef E₀ B x ∨ UsedRef E₀ rb x →
      (env.find? (keyOf t x)).isSome = true ∨ FamAddr B cb rb crb x ∨ ¬ NeedOk E₀ x) →
    (∀ a, adv a → ∀ ca, recordOf E₀ a = some ca → ∀ x, ConstAddrOf a ca x →
      (env.find? (keyOf t x)).isSome = true) →
    (∀ a, adv a → ∀ x, UsedRef E₀ a x →
      (env.find? (keyOf t x)).isSome = true ∨ FamAddr B cb rb crb x ∨ ¬ NeedOk E₀ x) →
    (∀ x, FamAddr B cb rb crb x → env.find? (keyOf t x) = none) →
    ∃ (blk : List (ConstantInfo .anon)) (adv' : FamilyAdvice)
      (tys : List IxVM.Refinement.Core.KExpr)
      (rhsss : List (List IxVM.Refinement.Core.KExpr)),
      FamDeclReads t E₀ B cb rb crb blk ∧ FamilyCheckFacts env blk adv' tys rhsss ∧
      (∀ ms rs, cb.info = .muts ms → crb.info = .muts rs →
        FamilyTysCanon t E₀ B cb ms rb crb rs blk tys rhsss) ∧
      ∀ E : Ixon.Env, RecordsFor R₁ E → FamRecsCompanion E t env blk tys
  /-- Each reference the family record uses is covered at the group's validation limit (its
  role's group is below the group, so the fold's table environment stores it) or is one a step
  needs stored (a record of the run's store, no block, in Lean's logic with its block). With the
  step's need hypothesis and the family's addresses stored after the step, the family record's
  references are stored after it. -/
  recRefs : ∀ x, UsedRef E₀ rb x →
    Claim.CoveredAt t (some (Binding.valLimit g)) x ∨ NeedOk E₀ x

/-- **The family check's facts at every new block of a group's closure with its selected family
record**, at the binders of `Binding.ClosureFamilySteps`. -/
def ClosureFamilyCheck (L : Ix.Kernel.Env .anon → NativeFam .anon → Prop)
    (calls : List (Call F)) (ρ : Binding.BRun) (t : Ix.Kernel.RoleTable) (g : Nat) : Prop :=
  ∀ (R R' R₁ : Ixon.Env) (env envT : Ix.Kernel.Env .anon)
    (famOf₀ famOf : _root_.Address → Option _root_.Address)
    (adv cont : _root_.Address → _root_.Address → Prop) (bAddr B rb : _root_.Address)
    (cb crb : Ixon.Constant),
    Binding.ClosureCtx.{u} L calls ρ t g R R' R₁ env famOf₀ famOf adv cont bAddr →
    (∀ ci ∈ env.consts, ci ∈ envT.consts) → (envT.consts.map (·.name)).Nodup →
    Binding.New R R₁ B → recordOf R₁ B = some cb → (∀ B', famOf B' ≠ some B) →
    famOf B = some rb → recordOf R₁ rb = some crb →
    (∀ x, FamAddr B cb rb crb x → ¬ StoredAt t envT x) →
    ClosureFamilyFacts.{u} L calls t g R₁ envT ρ.E₀ B cb rb crb (adv B)

/-! ## The step -/

/-- **The closure's step of a new block with its selected family record, at a group of a binding
run** (module docstring). -/
theorem closureFamilySteps_of_check {L : Ix.Kernel.Env .anon → NativeFam .anon → Prop}
    (hL : LinkLaws L) {calls : List (Call F)} {t : Ix.Kernel.RoleTable} {ρ : Binding.BRun}
    {Rs : Nat → Ixon.Env} (hrun : Binding.BindingRun calls t ρ Rs) (ht : t.check = .ok ())
    {g : Nat} (hg6 : 6 ≤ g) (hchk : ClosureFamilyCheck.{u} L calls ρ t g) :
    Binding.ClosureFamilySteps.{u} L calls ρ t g := by
  intro R R' R₁ env₀ envT famOf₀ famOf adv cont bAddr B rb cb crb hC hextT hndT hnB hcb hunc
    hfam hcrb hfrT
  have hF := hchk R R' R₁ env₀ envT famOf₀ famOf adv cont bAddr B rb cb crb hC hextT hndT hnB
    hcb hunc hfam hcrb hfrT
  have htwf : t.wf = true := by
    unfold Ix.Kernel.RoleTable.wf
    rw [ht]
    rfl
  have hS : LoadedReads.RunStore calls ρ.E₀ := hrun.runStore
  have hcov : LoadedReads.HashedRecordsStored calls ρ.E₀ := hrun.hashedStored
  -- the closure's store: within the run's records, with every blob the run loaded
  have hloaded : ∀ a lr, R₁.consts.get? a = some lr → ρ.E₀.consts.get? a = some lr :=
    fun a lr h => hC.admits.loaded a lr (hC.store.le₂.1 a lr h)
  have hblobs : ∀ x b, ρ.E₀.blobs.get? x = some b → R₁.blobs.get? x = some b :=
    fun x b h => hC.store.blobs x b (hC.reads.blobs x b h)
  have hcb' : recordOf R' B = some cb := Binding.recordOf_of_loaded hC.store.le₂.1 hcb
  have hcb₀ : recordOf ρ.E₀ B = some cb := Binding.recordOf_of_loaded hloaded hcb
  have hcrb₀ : recordOf ρ.E₀ rb = some crb := Binding.recordOf_of_loaded hloaded hcrb
  have hnB' : Binding.New R R' B := ⟨by rw [hcb']; rfl, hnB.2⟩
  -- the family's records, from the run's family checks
  obtain ⟨-, hroute, -⟩ := hC.checks.famCall B rb hfam
  obtain ⟨cb', ms, crb', rs, flat, hFB⟩ := hC.checks.family B rb hfam
  have e1 : cb' = cb := Option.some.inj (hFB.block.record.symm.trans hcb₀)
  subst cb'
  have e2 : crb' = crb := Option.some.inj (hFB.record.record.symm.trans hcrb₀)
  subst crb'
  have hB : FamBlockRecord ρ.E₀ B cb ms := hFB.block
  have hRB : FamRecRecord ρ.E₀ rb crb rs := hFB.record
  -- a record store for the closure's store that the run's calls are good for
  have hzc : R₁.consts.get? Ix.HostAdmission.Merkle.padding = none := by
    cases h : R₁.consts.get? Ix.HostAdmission.Merkle.padding with
    | none => rfl
    | some lc =>
      have h' := hC.store.le₂.1 _ lc h
      rw [hC.admits.zeroFree.1] at h'
      cases h'
  have hzb : R₁.blobs.get? Ix.HostAdmission.Merkle.padding = none := by
    cases h : R₁.blobs.get? Ix.HostAdmission.Merkle.padding with
    | none => rfl
    | some b =>
      have h' := hC.store.le₂.2 _ b h
      rw [hC.admits.zeroFree.2] at h'
      cases h'
  obtain ⟨Ec, hRc, hst⟩ := hrun.stepStores R₁ hloaded
    (fun a b h => hC.admits.loadedBlobs a b (hC.store.le₂.2 a b h))
    (fun p hp lc h => hC.admits.committed p hp lc (hC.store.le₂.1 _ lc h)) ⟨hzc, hzb⟩
  have hcanon₀ : L1.CanonicalHashCoverage ρ.E₀ calls := by
    intro bytes value hashed size exactRead
    obtain ⟨entry, stored, bytesEq, cached⟩ := hcov bytes value hashed size
      (L1.deConstant_of_deConstantExact exactRead) exactRead
    refine ⟨⟨entry, value, stored, cached, ?_⟩, rfl⟩
    rw [bytesEq]
    exact exactRead
  have hcanon : L1.CanonicalHashCoverage Ec calls :=
    Assembly.canonicalHashCoverage_frame hcanon₀ hst.decoded
      (fun a v h => hst.runRecord a v ((hS.recordOf_eq_recordAt a).trans h))
  -- the check of the block at the group's validation limit
  have hkind : UnitKind cb := Or.inr (Or.inr ⟨ms, hB.muts⟩)
  -- a block of inductive types has no twin's shape
  have hntw : ¬ (∃ rs : Array Ixon.MutConst, cb.info = .muts rs ∧ 0 < rs.size ∧
      ∀ m ∈ rs.toList, ∃ r, m = Ixon.MutConst.recr r) := by
    rintro ⟨rs, hrs, hpos, hrecs⟩
    have e : rs = ms := Ixon.ConstantInfo.muts.inj (hrs.symm.trans hB.muts)
    subst e
    obtain ⟨m, hm⟩ : ∃ m, m ∈ rs.toList := by
      cases hl : rs.toList with
      | nil =>
        have h0 : rs.size = 0 := by rw [← Array.length_toList, hl]; rfl
        exact absurd hpos (by omega)
      | cons m _ => exact ⟨m, by simp⟩
    obtain ⟨r, hr⟩ := hrecs m hm
    obtain ⟨ind, hind⟩ := hB.indcs m hm
    rw [hr] at hind
    cases hind
  have hchkB : ρ.checked B (Binding.valLimit g) := by
    rcases hC.famAdmits.checked B cb hnB' hcb' hkind hntw with h | ⟨B', hB', -⟩
    · exact h
    · exact (hunc B' hB').elim
  obtain ⟨bAddr', hiff⟩ := hrun.checked_iff
  have hU : Binding.UnitCheckedAt calls bAddr' t ρ.E₀ B (some (Binding.valLimit g)) :=
    (hiff B _).mp hchkB
  have hmem : ∀ k, k < ms.size →
      Claim.MemberCheckedLimAt calls bAddr' t B ms k (some (Binding.valLimit g)) := by
    rcases hU with h | ⟨c', ms', hc'', hms', hk'⟩
    · exact (Claim.checked_not_block hS hcb₀ hB.muts h).elim
    · rw [Option.some.inj (hc''.symm.trans hcb₀), hB.muts] at hms'
      have e : ms' = ms := (Ixon.ConstantInfo.muts.inj hms').symm
      rw [e] at hk'
      exact hk'
  have hpos : 0 < ms.size := by
    obtain ⟨cb₂, ms₂, hcb₂, hms₂, hpos₂⟩ := hC.run.famNonempty B rb hfam
    have e : cb₂ = cb := Option.some.inj (hcb₂.symm.trans hcb₀)
    rw [e, hB.muts] at hms₂
    rw [Ixon.ConstantInfo.muts.inj hms₂]
    exact hpos₂
  -- the route: modeled at the step's store, and so at every record store for the closure's store
  have hrouteEc : Route.blockRoute Ec B = some true :=
    blockRoute_of_modeledRoute hS hst hcanon hB.indcs (hmem 0 hpos) hroute
  have hrouteE : ∀ E, RecordsFor R₁ E → Route.blockRoute E B = some true := fun E hE =>
    (blockRoute_recordsFor hC.closed hE hcb).trans
      ((blockRoute_recordsFor hC.closed hRc hcb).symm.trans hrouteEc)
  -- the run's records at the family's addresses are the closure's store's
  have hheld : ∀ x, FamAddr B cb rb crb x → ∀ d, recordOf ρ.E₀ x = some d →
      recordOf R₁ x = some d := by
    intro x hx d hd
    have hsome : ∃ P, recordOf R₁ x = some P := by
      rcases hx with hx | hx
      · rcases Binding.constAddr_record hC.closed hcb hx with ⟨-, hs⟩ | ⟨-, P, hP, -, -⟩
        · exact (standalone_not_block hs ⟨ms, hB.muts⟩).elim
        · exact ⟨P, hP⟩
      · rcases Binding.constAddr_record hC.closed hcrb hx with ⟨-, hs⟩ | ⟨-, P, hP, -, -⟩
        · exact (standalone_not_block hs ⟨rs, hRB.muts⟩).elim
        · exact ⟨P, hP⟩
    obtain ⟨P, hP⟩ := hsome
    have e : P = d := Option.some.inj ((Binding.recordOf_of_loaded hloaded hP).symm.trans hd)
    rw [← e]
    exact hP
  have hEof : ∀ E, RecordsFor R₁ E → ∀ x, FamAddr B cb rb crb x → ∀ d,
      recordOf ρ.E₀ x = some d → recordOf E x = some d :=
    fun E hE x hx d hd => Binding.recordOf_of_recordsFor hE (hheld x hx d hd)
  -- the walk's facts at the block, over the step's store
  have hfree := famUnitFree_at hst hB hrouteEc hmem
  have htrees := famCtorTrees_at hst hB hrouteEc hmem
  have hsz : ∀ x, FamAddr B cb rb crb x → x.hash.size = 32 := by
    intro x hx
    rcases hx with hx | hx
    · exact TwinFamily.constAddr_hash_size_of_block hB.muts hx
    · exact TwinFamily.constAddr_hash_size_of_block hRB.muts hx
  -- key freedom of the two records' constant addresses
  have hnrb : Binding.New R R' rb := (hC.famAdmits.famNew B rb hfam hnB').1
  have hkey : ∀ x, FamAddr B cb rb crb x → Decl.KeyFree (keyOf t x) := by
    intro x hx
    rcases hx with hx' | hx'
    · exact Binding.plain_keyFree hC ht hg6 hextT hnB' hcb hx' (hfrT x (Or.inl hx'))
    · exact Binding.plain_keyFree hC ht hg6 hextT hnrb hcrb hx' (hfrT x (Or.inr hx'))
  -- the block's inert clause, from the run's facts
  have hinert : InertClause t cb := fun i hi x hx =>
    Claim.inertKey_keyOf_false ht
      (hC.run.famNotInert B rb x hfam hnB' (usedRef_of_idx hcb₀ hi hx))
  -- the step
  intro env Reg hext hnd hcl hrefs hadv1 hadv2 hfresh
  have hClc := hcl Ec hRc (some (Binding.valLimit g)) (Binding.carried_valLimit g)
    (Binding.limWithin_below t g)
  obtain ⟨blk, adv', tys, rhsss, hreads, hFacts, hTys, hComp⟩ :=
    hF.seam Ec hRc hst env hext hnd hClc.prefixInv hClc.extra hinert hrefs hadv1 hadv2 hfresh
  have heq : env.find? Ix.Kernel.eqName = some Ix.Kernel.eqA :=
    eqPin_of_shape hC.bnd.shape (fun ci hci => hext ci (hextT ci hci)) hnd
  obtain ⟨h, as, env₂, hg, hroots, hd, hst₂, hN, hR⟩ :=
    famStepConclusion_installed hFacts hreads hClc.store hClc.auxRoot heq hfresh hkey
  obtain ⟨new, henv, hperm⟩ := declIndRunJ_names_perm hd.shape
  have henv₂ : env₂ = ⟨(new ++ as) ++ env.consts⟩ := by
    rw [henv]
    simp [List.append_assoc]
  subst henv₂
  -- the members' names
  have hmemb : ∀ ci ∈ new, ∃ x, FamAddr B cb rb crb x ∧ ci.name = keyOf t x := by
    intro ci hci
    have hk : ci.name ∈ blk.map (·.name) := hperm.subset (List.mem_map.mpr ⟨ci, hci, rfl⟩)
    obtain ⟨ci₁, hci₁, hn⟩ := List.mem_map.mp hk
    obtain ⟨x, hx, hkx, -⟩ := hreads.2.1 ci₁ hci₁
    exact ⟨x, hx, hn.symm.trans hkx⟩
  have hbaseN : ∀ ci ∈ new, Decl.isBaseKey ci.name = true := by
    intro ci hci
    obtain ⟨x, -, hk⟩ := hmemb ci hci
    rw [hk]
    exact Decl.isBaseKey_keyOf t x
  have hnotalias : ∀ k, Decl.isBaseKey k = true → ∀ a ∈ as, a.name ≠ k := by
    intro k hk a ha hn
    obtain ⟨n, d, hna⟩ := AliasGroup.name_aux hg a ha
    rw [hna] at hn
    exact auxKey_ne_of_isBaseKey hk hn
  -- the block's references stored after the step
  have hused : Decl.UsedRefsStored t ⟨(new ++ as) ++ env.consts⟩ cb := by
    intro i hi x hx
    have hu : UsedRef ρ.E₀ B x := usedRef_of_idx hcb₀ hi hx
    rcases hrefs x (Or.inl hu) with hs | hf | hn
    · obtain ⟨ci, hci⟩ := Option.isSome_iff_exists.mp hs
      obtain ⟨hmem', hname⟩ := find?_mem_name hci
      have hs' := find?_isSome_of_mem (E := ⟨(new ++ as) ++ env.consts⟩)
        (List.mem_append_right (new ++ as) hmem')
      rw [hname] at hs'
      exact Option.isSome_iff_exists.mp hs'
    · exact famFound_of_step hreads hst₂ x hf
    · exact absurd (hC.run.famNeedOk B rb x hfam hnB' hu) hn
  -- the family record's references stored after the step
  have husedR : Decl.UsedRefsStored t ⟨(new ++ as) ++ env.consts⟩ crb := by
    intro i hi x hx
    have hu : UsedRef ρ.E₀ rb x := usedRef_of_idx hcrb₀ hi hx
    have hold : (env.find? (keyOf t x)).isSome = true →
        ∃ ci, (⟨(new ++ as) ++ env.consts⟩ : Ix.Kernel.Env .anon).find? (keyOf t x) = some ci := by
      intro hs
      obtain ⟨ci, hci⟩ := Option.isSome_iff_exists.mp hs
      obtain ⟨hmem', hname⟩ := find?_mem_name hci
      have hs' := find?_isSome_of_mem (E := ⟨(new ++ as) ++ env.consts⟩)
        (List.mem_append_right (new ++ as) hmem')
      rw [hname] at hs'
      exact Option.isSome_iff_exists.mp hs'
    rcases hF.recRefs x hu with hcov | hneed
    · -- covered at the group's validation limit: its role's group is below the group
      obtain ⟨ci, hci, hname⟩ := coveredAt_stored hC.bnd.shape htwf
        (fun r hr => Nat.lt_of_lt_of_le (hr _ rfl) (Binding.valLimit_le g)) hcov
      exact hold (find_isSome_of_storedAt ⟨ci, hext ci (hextT ci hci), hname⟩)
    · rcases hrefs x (Or.inr hu) with hs | hf | hn
      · exact hold hs
      · exact famFound_of_step hreads hst₂ x hf
      · exact absurd hneed hn
  -- the seam of the loads, at the installation from the selected forms
  have hcanonM : FamilyMembersCanon t ρ.E₀ B cb ms rb crb rs ⟨(new ++ as) ++ env.consts⟩ :=
    familyMembersCanon_of_tys ht hB hRB hFacts hreads (hTys ms rs hB.muts hRB.muts) hN hR husedR
  -- the new constants' names are distinct
  have hndNA : ((new ++ as).map (·.name)).Nodup := by
    rw [List.map_append]
    refine List.nodup_append.mpr ⟨hperm.nodup_iff.mpr hreads.1, AliasGroup.names_nodup hg, ?_⟩
    intro k hk k' hk' heq'
    obtain ⟨ci, hci, rfl⟩ := List.mem_map.mp hk
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hk'
    exact hnotalias _ (hbaseN ci hci) a ha heq'.symm
  -- each new constant an alias (a definition) or under a member's name
  have hnameNA : ∀ c ∈ new ++ as, (∃ cv v hint, c = ConstantInfo.defnInfo cv v hint) ∨
      ∃ ci ∈ blk, c.name = ci.name := by
    intro c hc
    rcases List.mem_append.mp hc with hc | hc
    · have hk : c.name ∈ blk.map (·.name) := hperm.subset (List.mem_map.mpr ⟨c, hc, rfl⟩)
      obtain ⟨ci, hci, hn⟩ := List.mem_map.mp hk
      exact Or.inr ⟨ci, hci, hn.symm⟩
    · exact Or.inl (AliasGroup.defn_of_mem hg c hc).1
  -- the stored rules' facts after the step
  have hna : ∀ ci ∈ blk, Decl.NonAuxKey ci.name := fun ci hci => by
    obtain ⟨x, -, hk, -⟩ := hreads.2.1 ci hci
    rw [hk]
    exact Decl.isBaseKey_iff_nonAuxKey.mp (Decl.isBaseKey_keyOf t x)
  have hSrec : Ix.Kernel.RecCtorsStored (⟨(new ++ as) ++ env.consts⟩ : Ix.Kernel.Env .anon) :=
    (Decl.FamilyAlias.foldStoreInv_famStep hg hreads.2.2.2 hna hd hClc.foldStore).store.rec_ctors
  -- the stored recursors' loaded form, self-mention scoping, and `check_recs` header counts
  have hstoredRecs : Binding.StoredFamilyRecs t R₁ ⟨(new ++ as) ++ env.consts⟩ B cb rb crb := by
    refine ⟨?_, fun ms' rs' hms' hrs' => ?_⟩
    swap
    · obtain ⟨off, hBE₀, hlv⟩ := hC.checks.familyRecLvls B rb cb crb ms' rs' hfam hcb₀ hcrb₀ hms' hrs'
      exact ⟨off, hBE₀.of_closed_sub ht htwf
        (fun y c hy => Binding.recordOf_of_loaded hloaded hy) hC.closed hblobs
        (by show (recordOf R₁ B).isSome = true; rw [hcb]; rfl),
        hlv⟩
    intro ms' rs' k rc hms' hrs' hk
    have ems : ms' = ms := Ixon.ConstantInfo.muts.inj (hms'.symm.trans hB.muts)
    have ers : rs' = rs := Ixon.ConstantInfo.muts.inj (hrs'.symm.trans hRB.muts)
    subst ms' rs'
    have hT := hTys ms rs hB.muts hRB.muts
    have hku : k < UInt64.size := Nat.lt_trans (Array.getElem?_eq_some_iff.mp hk).1 hT.rsBound
    have hk_toNat : k.toUInt64.toNat = k := by
      change (UInt64.ofNat k).toNat = k
      rw [UInt64.toNat_ofNat']
      exact Nat.mod_eq_of_lt hku
    have hx_rb : ConstAddrOf rb crb (memberAddr rb k (.recr rc)) :=
      Or.inr ⟨rs, k, .recr rc, hRB.muts, hk, Or.inl rfl⟩
    have hxF : FamAddr B cb rb crb (memberAddr rb k (.recr rc)) := Or.inr hx_rb
    obtain ⟨ci₀, hci₀, hname₀⟩ := hreads.2.2.1 _ hxF
    obtain ⟨y, -, hy, hry⟩ := hreads.2.1 ci₀ hci₀
    have hyx : y = memberAddr rb k (.recr rc) := Core.keyOf_inj htwf (hy.symm.trans hname₀)
    rw [hyx] at hry
    have hP₀ : recordOf ρ.E₀ (memberAddr rb k (.recr rc)) =
        some (memberProjection rb k (.recr rc)) := hRB.members k (.recr rc) hk
    have hinfoP : (memberProjection rb k (.recr rc)).info = .rPrj ⟨k.toUInt64, rb⟩ := rfl
    obtain ⟨cb', rs'', rc', hMA₀, hRR₀⟩ := TwinFamily.reads_rprj hP₀ hinfoP hry
    obtain ⟨hcb', hrs'', hmem', -, -, -⟩ := hMA₀
    have ecb' : cb' = crb := Option.some.inj (hcb'.symm.trans hRB.record)
    rw [ecb'] at hrs'' hRR₀
    have ers'' : rs'' = rs := Ixon.ConstantInfo.muts.inj (hrs''.symm.trans hRB.muts)
    rw [ers''] at hmem' hRR₀
    rw [hk_toNat] at hmem'
    have erc' : rc' = rc := Ixon.MutConst.recr.inj (Option.some.inj (hmem'.symm.trans hk))
    rw [erc'] at hRR₀
    have hci_rec : ∃ cv mI rP rules₀, ci₀ = .recInfo cv mI rP rules₀ := by
      obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hci_eq⟩ := hRR₀
      exact ⟨_, _, _, _, hci_eq⟩
    obtain ⟨cv, mI, rP, rules₀, hci_eq⟩ := hci_rec
    subst hci_eq
    have hcv_name : cv.name = keyOf t (memberAddr rb k (.recr rc)) := hname₀
    have hcrb' : recordOf R' rb = some crb := Binding.recordOf_of_loaded hC.store.le₂.1 hcrb
    have hry' : Reads t R' (memberAddr rb k (.recr rc)) (.recInfo cv mI rP rules₀) :=
      hC.reads.reads rb crb (memberAddr rb k (.recr rc)) _ hnrb hcrb' hx_rb hry
    have hry₁ : Reads t R₁ (memberAddr rb k (.recr rc)) (.recInfo cv mI rP rules₀) := by
      unfold Reads at hry' ⊢
      refine Binding.readsIn_of_agree (fun z cz hcz hkindZ => ?_) hC.store.blobs
        (fun cz hcz => hheld _ hxF cz (Binding.recordOf_of_loaded hC.admits.loaded hcz)) hry'
      cases h1 : R₁.consts.get? z with
      | some lc =>
        have h2 := hC.store.le₂.1 z lc h1
        unfold recordOf at hcz ⊢
        rw [h2] at hcz
        rw [h1]
        exact hcz
      | none =>
        exfalso
        have hsome : (R'.consts.get? z).isSome = true := by
          unfold recordOf at hcz
          cases hg' : R'.consts.get? z with
          | none => rw [hg'] at hcz; cases hcz
          | some _ => rfl
        have hru : Binding.RoleUnitAt t g z := hC.store.units z hsome h1
        have hRnone : recordOf R z = none := by
          unfold recordOf
          cases hgR : R.consts.get? z with
          | none => rfl
          | some lc =>
            have := hC.store.le₁.1 z lc hgR
            rw [h1] at this
            cases this
        have hnewZ : Binding.New R R' z := ⟨by rw [hcz]; rfl, hRnone⟩
        rcases hC.run.roleUnitForm z cz hru hnewZ hcz with ⟨d, hd⟩ | ⟨ax, hax⟩
        · rcases hkindZ with ⟨_, hkZ⟩ | ⟨_, hkZ⟩ <;> (rw [hd] at hkZ; cases hkZ)
        · rcases hkindZ with ⟨_, hkZ⟩ | ⟨_, hkZ⟩ <;> (rw [hax] at hkZ; cases hkZ)
    have hP₁ : recordOf R₁ (memberAddr rb k (.recr rc)) =
        some (memberProjection rb k (.recr rc)) := hheld _ hxF _ hP₀
    obtain ⟨cb₁, rs₁, rc₁, hMA₁, hRR₁⟩ := TwinFamily.reads_rprj hP₁ hinfoP hry₁
    obtain ⟨hcb₁, hrs₁, hmem₁, -, -, -⟩ := hMA₁
    have ecb₁ : cb₁ = crb := Option.some.inj (hcb₁.symm.trans hcrb)
    rw [ecb₁] at hrs₁ hRR₁
    have ers₁ : rs₁ = rs := Ixon.ConstantInfo.muts.inj (hrs₁.symm.trans hRB.muts)
    rw [ers₁] at hmem₁ hRR₁
    rw [hk_toNat] at hmem₁
    have erc₁ : rc₁ = rc := Ixon.MutConst.recr.inj (Option.some.inj (hmem₁.symm.trans hk))
    rw [erc₁] at hRR₁
    have hrec_mem : ConstantInfo.recInfo cv mI rP rules₀ ∈ Decl.FamilyAlias.recsOf blk :=
      List.mem_filter.mpr ⟨hci₀, rfl⟩
    obtain ⟨idx, hidx⟩ := List.getElem?_of_mem hrec_mem
    obtain ⟨⟨tyA, htyA⟩, ⟨rhss, hrhss⟩⟩ := tys_of_rec hFacts hidx
    obtain ⟨rules', hf', -, -⟩ := hR idx cv mI rP rules₀ tyA rhss hidx htyA hrhss
    have hf_k : (⟨(new ++ as) ++ env.consts⟩ : Ix.Kernel.Env .anon).find?
        (keyOf t (memberAddr rb k (.recr rc))) =
        some (.recInfo ⟨cv.name, cv.levelParams, tyA⟩ mI rP rules') := by
      rw [← hcv_name]
      exact hf'
    obtain ⟨cSA, hcSA, hSA'⟩ := hst₂ _ hci₀
    have ecSA : cSA = .recInfo ⟨cv.name, cv.levelParams, tyA⟩ mI rP rules' :=
      Option.some.inj (hcSA.symm.trans hf')
    rw [ecSA] at hSA'
    have hTML : TwinFamily.TwinMemberLoaded crb rs ⟨k.toUInt64, rb⟩ rc cv.levelParams cv.type
        rules₀ ⟨cv.name, cv.levelParams, tyA⟩ rules' := by
      have hRR₀' : RecReads t (recordOf ρ.E₀) (fun x => ρ.E₀.blobs.get? x) crb (blockSelf t rb rs)
          (keyOf t (memberAddr rb (⟨k.toUInt64, rb⟩ : Ixon.RecursorProj).idx.toNat (.recr rc)))
          rc (.recInfo cv mI rP rules₀) := by
        simpa [hk_toNat] using hRR₀
      have hf'' : (⟨(new ++ as) ++ env.consts⟩ : Ix.Kernel.Env .anon).find?
          (keyOf t (memberAddr rb (⟨k.toUInt64, rb⟩ : Ixon.RecursorProj).idx.toNat (.recr rc))) =
          some (.recInfo ⟨cv.name, cv.levelParams, tyA⟩ mI rP rules') := by
        simpa [hk_toNat] using hf_k
      exact hcanonM.recLoaded ⟨k.toUInt64, rb⟩ rc cv mI rP rules₀
        ⟨cv.name, cv.levelParams, tyA⟩ mI rP rules' rfl (by simpa [hk_toNat] using hk) hRR₀' hf''
    have hmeta := hT.recMeta idx cv mI rP rules₀ tyA rhss hidx htyA hrhss ⟨k.toUInt64, rb⟩ rc rfl
      (by simpa [hk_toNat] using hk) (by simpa [hk_toNat] using hcv_name)
      (by rw [hcv_name]; exact hRR₀)
    obtain ⟨hns, hnp, hmot, ⟨Bm, im, cbm, msm, indm, D, lvls, himu, husedM, hPm₀, hBm₀, hmsm, him,
      hpi, hfn, hni⟩, hconcl⟩ := hmeta
    obtain ⟨crb', i_u, hcrb'_u, hi_u, hx_u⟩ := husedM
    have ecrb'_u : crb' = crb := Option.some.inj (hcrb'_u.symm.trans hcrb₀)
    subst crb'
    obtain ⟨Pm₁, hPm₁⟩ := Option.isSome_iff_exists.mp ((hC.closed.1 rb crb hcrb).2 i_u hi_u _ hx_u)
    have ePm : Pm₁ = memberProjection Bm im (.indc indm) :=
      Option.some.inj ((Binding.recordOf_of_loaded hloaded hPm₁).symm.trans hPm₀)
    subst Pm₁
    have hownM : Ix.Cert.ownerOf (memberAddr Bm im (.indc indm))
        (memberProjection Bm im (.indc indm)) = Bm := rfl
    obtain ⟨cbm₁, hcbm₁⟩ := Option.isSome_iff_exists.mp (hownM ▸ (hC.closed.1 _ _ hPm₁).1)
    have ecbm : cbm₁ = cbm :=
      Option.some.inj ((Binding.recordOf_of_loaded hloaded hcbm₁).symm.trans hBm₀)
    subst cbm₁
    exact ⟨cv, mI, rP, rules₀, ⟨cv.name, cv.levelParams, tyA⟩, rules', hku, hRR₁, hf_k, rfl, rfl,
      hSA', hTML, hns, hnp, hmot,
      ⟨Bm, im, cbm, msm, indm, D, lvls, himu, hPm₁, hcbm₁, hmsm, him, hpi, hfn, hni⟩, hconcl⟩
  refine ⟨new ++ as, Reg, hndNA, ?_, ?_, ?_, ?_, ?_, hstoredRecs, ?_⟩
  · -- fresh in the prefix
    intro ci hci
    rcases List.mem_append.mp hci with hci | hci
    · obtain ⟨x, hx, hk⟩ := hmemb ci hci
      rw [hk]
      exact hfresh x hx
    · exact AliasGroup.fresh_prefix hg ci hci
  · -- the clause, with the same registry, at every record store and carried limit
    intro E hE lim hcE hlE
    have hCE := hcl E hE lim hcE hlE
    have hLC : FamLoadCtx ⟨E, env, t, lim⟩ (new ++ as) B cb ms rb crb rs :=
      famLoadCtx_at hE.1 (Binding.blob_of_recordsFor hE hblobs) hB hRB
        (Binding.recordOf_of_recordsFor hE hcb)
        (fun i m hm => hEof E hE _ (Or.inl (Or.inr ⟨ms, i, m, hB.muts, hm, Or.inl rfl⟩)) _
          (hB.members i m hm))
        (fun i ind j hm hj => hEof E hE _
          (Or.inl (Or.inr ⟨ms, i, .indc ind, hB.muts, hm, Or.inr ⟨ind, j, rfl, hj, rfl⟩⟩)) _
          (hB.ctors i ind j hm hj))
        (Binding.recordOf_of_recordsFor hE hcrb)
        (fun i m hm => hEof E hE _ (Or.inr (Or.inr ⟨rs, i, m, hRB.muts, hm, Or.inl rfl⟩)) _
          (hRB.members i m hm))
        (modeledAt_of_blockRoute (hrouteE E hE)) hfree (hrouteE E hE) htrees hCE.prefixInv hg
        hreads hd hst₂ hused hcanonM
    exact famStepKeeps_with hL hsz
      (famModeled_at hB hRB (fun x hx d hd => hE.2.1 x d (hheld x hx d hd))
        (modeledAt_of_blockRoute (hrouteE E hE)))
      hCE hg hroots hreads hd
      (recCompanionFacts_of_tys hB hRB (Binding.recordOf_of_recordsFor hE hcrb)
        (fun i m hm => hEof E hE _ (Or.inr (Or.inr ⟨rs, i, m, hRB.muts, hm, Or.inl rfl⟩)) _
          (hRB.members i m hm))
        hreads (hTys ms rs hB.muts hRB.muts) hFacts hndNA hnameNA hN hR hSrec (hComp E hE))
      hLC.newLoads
  · -- no constant at an operation's key
    intro ci hci
    rcases List.mem_append.mp hci with hm | hm
    · obtain ⟨x, hx, hn⟩ := hmemb ci hm
      rw [hn]
      exact Binding.not_mem_opNames_of_keyFree (hkey x hx)
    · obtain ⟨n, d, hn⟩ := AliasGroup.name_aux hg ci hm
      have hn' : ci.name = .aux n d := hn
      rw [hn']
      intro hop
      have hb := RoleOps.isBaseKey_of_mem_opNames hop
      exact nomatch hb
  · -- each address of the family, stored as its reading
    intro x hx
    obtain ⟨ci₀, hci₀, hk⟩ := hreads.2.2.1 x hx
    obtain ⟨x', hx', hk', hr⟩ := hreads.2.1 ci₀ hci₀
    have hxx : x' = x := Core.keyOf_inj htwf (hk'.symm.trans hk)
    subst hxx
    obtain ⟨c', hc', hSA⟩ := hst₂ ci₀ hci₀
    obtain ⟨hmem', hname⟩ := find?_mem_name hc'
    refine ⟨c', ?_, ci₀, hname.trans hk', hr, hSA⟩
    rcases List.mem_append.mp hmem' with hmem' | hmem'
    · rcases List.mem_append.mp hmem' with hmem' | hmem'
      · exact List.mem_append_left _ hmem'
      · exfalso
        exact hnotalias (keyOf t x') (Decl.isBaseKey_keyOf t x') c' hmem'
          (hname.trans hk')
    · exfalso
      have h1 := find?_isSome_of_mem (E := env) hmem'
      rw [hname, hk', hfresh x' hx'] at h1
      exact Bool.false_ne_true h1
  · -- the family record installed
    exact familyInstalled_of_step htwf hRB hg hreads hd hst₂ hfresh
  · -- each new constant at an address's key or at a derived key
    intro ci hci
    rcases List.mem_append.mp hci with hci | hci
    · exact Or.inl (hmemb ci hci)
    · obtain ⟨n, d, hn⟩ := AliasGroup.name_aux hg ci hci
      exact Or.inr ⟨n, d, hn⟩

/-- **The closure's step of a new block with its selected family record at every group of every
binding run**, from the family check's facts there: the residual's `ClosureFamilySteps`
hypothesis from `ClosureFamilyCheck`. -/
theorem closureFamilySteps_of_checkRow
    (hchk : ∀ calls, Binding.AtGroups (Binding.BindingRun calls)
      (ClosureFamilyCheck.{u} FormerOpenTraceAt calls)) :
    ∀ calls, Binding.AtGroups (Binding.BindingRun calls)
      (Binding.ClosureFamilySteps.{u} FormerOpenTraceAt calls) :=
  fun calls t ρ Rs hrun hall ht g hg6 hg =>
    closureFamilySteps_of_check linkLaws_formerOpenTrace hrun ht hg6
      (hchk calls t ρ Rs hrun hall ht g hg6 hg)

end IxVM.Refinement.Typing.FamilyAlias
