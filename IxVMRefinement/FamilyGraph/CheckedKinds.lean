import IxVMRefinement.Endpoint.WalkedKindSteps
import IxVMRefinement.FamilyGraph.Skeleton
import IxVMRefinement.FamilyGraph.CheckedUnit

/-! # The steps of the kinds of unit, for every checked unit, and the units a family check checks

Each proved step of a kind of unit reads of the run, about the unit's own record, only what
`CheckedUnit` holds: its check at the limit, the inert and cover clauses, freshness and free
keys. None reads that the walk reached the record. This module states each once, as a
`CheckedUnitStep`, by the theorem that already proves the step:

* `standaloneValue_checked`: a standalone definition, theorem or opaque record;
* `definitionBlock_checked`: a block of definitions;
* `standaloneRecursor_checked`: a standalone recursor record. The recursor arm of the record's
  check is read off the check itself (`recArmLimAt_of_checked`), and the basis exclusion at a
  fresh record needs no walk;
* `nativeBlockAlias_checked`: a one-type native block whose former is declared at a definition;
* `nativeBlockOtherTelescope_checked`: a one-type native block whose former reads as a telescope
  of another length, which the circuit refuses.

The top-walked forms the composed statement asks follow by `walkedUnitStep_of_checked`
(`standaloneRecursor_walked`, as an instance, has the composed statement's type).

**Units a family check checks.** `InnerChecked` is what the run must give of the records checked
inside a family check, beside the family graph: the check of each at the fold's limit; that no
reference one uses is an inert axiom's; that a reference one uses is stored by the witness's
environment, covered, or an in-logic constant address owned by a checked record of smaller rank;
and that a block among them, when no block claims it and it is no twin, is a block of
definitions or one inductive type on the native route. From it and the graph an inner unit has
`CheckedUnit` (`checkedUnit_of_inner`), so its step is the step of its kind
(`innerUnitStep_of_checked`), and `innerUnitSteps_of_kinds` is the family skeleton's step
hypothesis for inner units, at the fold's clause at the opened head trace, from the one kind
step that is not proved yet (the one-type native block declared at its telescope). -/

universe u

set_option linter.unusedVariables false

namespace IxVM.Refinement.Typing

open IxVM.Consistency
open Aiur.Generic.SourceSemantics (Call)
open IxVM (F)
open Ix.Kernel.Semantics (NativeFam)

/-! ## The kinds, for every checked unit -/

/-- The check of a record that declares one constant is the check of the record itself. -/
theorem CheckedUnit.direct {calls : List (Call F)} {bAddr : _root_.Address}
    {t : Ix.Kernel.RoleTable} {envT : Ix.Kernel.Env .anon} {E₀ : Ixon.Env} {lim : Option Nat}
    {A : _root_.Address} {c : Ixon.Constant}
    (hU : CheckedUnit calls bAddr t envT E₀ lim A c) (hs : Standalone c) :
    Claim.CheckedLimAt calls bAddr t A lim := by
  rcases hU.checked with ⟨ms, hms, -⟩ | h
  · exact (standalone_not_block hs ⟨ms, hms⟩).elim
  · exact h

/-- **The step of every checked standalone definition, theorem or opaque record keeps the fold's
clause**, at the limit of its check, for any link that satisfies the link laws. -/
theorem standaloneValue_checked
    {L : Ix.Kernel.Env .anon → NativeFam .anon → Prop} (hL : LinkLaws L) :
    CheckedUnitStep.{u} (FoldExtra.{u} L) fun _ _ _ _ c =>
      ∃ d : Ixon.Definition, c.info = .defn d := by
  intro calls bAddr t E₀ lim R envT E hctx A c hc hlog hkind ht hS hcov hcanon hU
  obtain ⟨d, hinfo⟩ := hkind
  exact unitStep_value_foldExtra hL ht hS hctx.toStepStore hc hinfo hlog
    (hU.direct (Or.inl ⟨d, hinfo⟩)) hU.keys hU.inert hU.cover

/-- **The step of every checked block of definitions keeps the fold's clause**, at the limit of
its members' checks, for any link that satisfies the link laws. -/
theorem definitionBlock_checked
    {L : Ix.Kernel.Env .anon → NativeFam .anon → Prop} (hL : LinkLaws L) :
    CheckedUnitStep.{u} (FoldExtra.{u} L) fun _ _ _ _ c =>
      ∃ ms : Array Ixon.MutConst, c.info = .muts ms ∧ DefnBlock ms := by
  intro calls bAddr t E₀ lim R envT E hctx A c hc hlog hkind ht hS hcov hcanon hU
  obtain ⟨ms, hmuts, hdefs⟩ := hkind
  exact unitStep_defnBlock_foldExtra hL ht hS hcov hctx.toStepStore hc hmuts hlog hdefs
    (memberChecked_of_walked_block hS hc hmuts hU.checked) hU.keys hU.inert hU.cover

/-- **The check of a recursor record took the recursor arm**, at the limit of the check: the
check loaded the record and ran `check_const` on the loaded `Rec` value. -/
theorem recArmLimAt_of_checked {calls : List (Call F)} {bAddr : _root_.Address}
    {t : Ix.Kernel.RoleTable} {E₀ : Ixon.Env} {lim : Option Nat}
    (hS : LoadedReads.RunStore calls E₀) {A : _root_.Address} {c : Ixon.Constant}
    {rc : Ixon.Recursor} (hc : recordOf E₀ A = some c) (hinfo : c.info = .recr rc)
    (hchk : Claim.CheckedLimAt calls bAddr t A lim) : Claim.RecArmLimAt calls bAddr t A lim := by
  obtain ⟨h_pre, m_chk, h'_chk, rcv, ap, ptr, v, r_chk, cs_load, cs_chk,
    hrc_pre, hrc_m, ha_pre, ha_m, ev_ld, -, hsub_ld, hld, ev_chk, -, hsub_chk⟩ := hchk
  obtain ⟨ab, hab, hA⟩ := ha_pre
  obtain ⟨raw, c', hh, hba, hx, hrec⟩ := Claim.get_ci_recr_value hab ev_ld
  have hrec₀ : Ix.Cert.recordAt E₀ (Core.ixAddr ab) = some c := by
    rw [hA]
    exact (hS.recordOf_eq_recordAt A).symm.trans hc
  have hcc : c' = c := hS.record_eq hrec₀ (Core.hashed_mono hsub_ld hh) hba hx
  subst c'
  obtain ⟨levels, type, parameters, indices, motives, minors, rules, k, unsafeFlag, block,
    position, hv⟩ := hrec rc hinfo
  have hvv := Except.ok.inj (hld.symm.trans hv)
  subst hvv
  exact ⟨h_pre, m_chk, h'_chk, rcv, ap, ptr, r_chk, levels, type, parameters, indices, motives,
    minors, rules, k, unsafeFlag, block, position, cs_load, cs_chk, hrc_pre, hrc_m,
    ⟨ab, hab, hA⟩, ha_m, ev_ld, hsub_ld, hv, ev_chk, hsub_chk⟩

/-- **The step of every checked standalone recursor record keeps the fold's clause**, at the
limit of its check and at the opened head trace. The parent that heads the major premise is
native because the recursor arm refuses a recursor of a modeled family. -/
theorem standaloneRecursor_checked :
    CheckedUnitStep.{u} (FoldExtra.{u} FormerOpenTraceAt) fun _ _ _ _ c =>
      ∃ rc : Ixon.Recursor, c.info = .recr rc := by
  intro calls bAddr t E₀ lim R envT E hctx A c hc hlog hkind ht hS hcov hcanon hU
  obtain ⟨rc, hinfo⟩ := hkind
  have hst : StepStore calls t E₀ E := hctx.toStepStore
  have hs : Standalone c := Or.inr (Or.inl ⟨rc, hinfo⟩)
  have hkey : Decl.KeyFree (keyOf t A) := hU.keys A (Or.inl ⟨rfl, hs⟩)
  have harm : RecArmRun calls t A lim :=
    recArmRun_of_limArm (recArmLimAt_of_checked hS hc hinfo (hU.direct hs))
  have hres : RecMajorFreshNotBasis.{u} t envT E₀ E lim A c rc :=
    recMajorFreshNotBasis_of_arm ht hS hst hc hinfo harm hU.inert hU.cover hctx.shape.prelude
      hctx.recordsFor hkey
  exact unitStep_recLate_foldExtra linkLaws_formerOpenTrace (RecMajorTie t E₀ A c rc) ht hinfo
    (address_size_of_record hS hc)
    (fun env hstep =>
      recParent_of_arm_tied ht hS hst hc hinfo harm hU.inert hU.cover hres env hstep)
    (fun env P ip fam hstep hlv hpar htie hread =>
      (recLateOutAll_of_arm ht hS hcov hst hc hinfo hlog harm hkey hU.inert hU.cover hstep hlv
        hpar htie hread).at (hst.held hc) hst.runBlob)

/-- **The step of every checked one-type native block whose former is declared at a definition
keeps the fold's clause at the opened head trace**, at the limit of its member's check. -/
theorem nativeBlockAlias_checked :
    CheckedUnitStep.{u} (FoldExtra.{u} FormerOpenTraceAt) fun calls t E₀ B cb =>
      ∃ ind : Ixon.Inductive,
        BlockUnitRecord E₀ B cb ind ∧ NativeRouteAt calls B ∧ FormerAtAlias t E₀ B cb ind := by
  intro calls bAddr t E₀ lim R envT E hctx B cb hc hlog hkind ht hS hcov hcanon hU
  obtain ⟨ind, hrec, hnat, halias⟩ := hkind
  have hmem : Claim.MemberCheckedLimAt calls bAddr t B #[.indc ind] 0 lim :=
    memberChecked_of_walked_block hS hc hrec.muts hU.checked 0 (by simp)
  exact unitStep_nativeBlockAlias ht hS hctx hrec hmem hnat halias hU.keys hU.inert hU.cover
    hcanon

/-- **The step of every checked one-type native block whose former reads as a telescope of
another length**, for every carried clause: the circuit refuses the block. -/
theorem nativeBlockOtherTelescope_checked
    {X : Ix.Kernel.RoleTable → Ixon.Env → Ix.Kernel.Env .anon → Prop} :
    CheckedUnitStep.{u} X fun calls t E₀ B cb =>
      ∃ ind : Ixon.Inductive,
        BlockUnitRecord E₀ B cb ind ∧ NativeRouteAt calls B ∧ FormerTeleOther t E₀ B cb ind := by
  intro calls bAddr t E₀ lim R envT E hctx B cb hc hlog hkind ht hS hcov hcanon hU
  obtain ⟨ind, hrec, hnat, hother⟩ := hkind
  exact unitStep_formerTeleOther ht hS hctx.toStepStore hrec hU.checked hnat hother hU.inert
    hU.cover

/-- **The step of every top-walked standalone recursor record keeps the fold's clause**: the
composed statement's obligation for this kind, as the instance of the step of every checked
one. -/
theorem standaloneRecursor_walked :
    Endpoint.WalkedUnitStep.{u} (FoldExtra.{u} FormerOpenTraceAt) fun _ _ _ _ c =>
      ∃ rc : Ixon.Recursor, c.info = .recr rc :=
  walkedUnitStep_of_checked standaloneRecursor_checked

/-! ## The units a family check checks -/

/-- **What the run gives of the records checked inside a family check, beside the family graph**
(module docstring). -/
structure InnerChecked (calls : List (Call F)) (bAddr : _root_.Address)
    (t : Ix.Kernel.RoleTable) (envT : Ix.Kernel.Env .anon) (E₀ : Ixon.Env) (lim : Option Nat)
    (Top : _root_.Address → Prop) (rank : _root_.Address → Nat)
    (fam twin : _root_.Address → Option _root_.Address) (Inner : _root_.Address → Prop) :
    Prop where
  /-- The family check checked the record at the fold's limit: every member of a block, or the
  record. -/
  checked : ∀ a c, Inner a → recordOf E₀ a = some c →
    (∃ ms, c.info = .muts ms ∧
        ∀ k, k < ms.size → Claim.MemberCheckedLimAt calls bAddr t a ms k lim) ∨
      Claim.CheckedLimAt calls bAddr t a lim
  /-- No reference the record uses is an inert axiom's. -/
  notInert : ∀ a x, Inner a → UsedRef E₀ a x → ¬ InertAt t x
  /-- A reference the record uses is stored by the witness's environment, covered, or an
  in-logic constant address owned by a checked unclaimed record of smaller rank. -/
  refsBelow : ∀ a x, Inner a → UsedRef E₀ a x →
    StoredAt t envT x ∨ Covered t x ∨
      (NeedOk E₀ x ∧ OwnedBelow E₀ Top Inner rank fam (rank a) x)
  /-- A block among them that no block claims and that is no twin is empty, a block of
  definitions, or one inductive type that the run's dispatch put on the native route (an
  observation answering `0`; at a step's context every observation answers so,
  `nativeRouteAt_of_nativeObs`). -/
  blocks : ∀ a c ms, Inner a → Unclaimed fam a → twin a = none → recordOf E₀ a = some c →
    c.info = .muts ms → ¬ DefnBlock ms → ms.size ≠ 0 →
    (∃ ind : Ixon.Inductive, ms = #[.indc ind]) ∧ Claim.NativeObsAt calls a

section Inner

variable {calls : List (Call F)} {bAddr : _root_.Address} {t : Ix.Kernel.RoleTable}
  {R E₀ E : Ixon.Env} {envT : Ix.Kernel.Env .anon} {lim : Option Nat}
  {seeds : List _root_.Address} {Top : _root_.Address → Prop} {rank : _root_.Address → Nat}
  {fam twin : _root_.Address → Option _root_.Address}
  {adv : _root_.Address → _root_.Address → Prop} {Inner : _root_.Address → Prop}

/-- **A unit checked inside a family check has what a step reads of the run**: its check from
the family check, the inert clause from `notInert`, the cover clause from `refsBelow` (a
reference owned below is none of the record's own), free keys from freshness. -/
theorem checkedUnit_of_inner (hG : TopGraph t E₀ seeds Top rank)
    (hF : FamilyGraph t envT E₀ Top rank fam twin adv Inner)
    (hI : InnerChecked calls bAddr t envT E₀ lim Top rank fam twin Inner)
    (hctx : StepCtx.{u} calls t R envT E₀ E) (ht : t.check = .ok ())
    {A : _root_.Address} {c : Ixon.Constant} (hIA : Inner A) (hU : Unclaimed fam A)
    (hc : recordOf E₀ A = some c) (hns : ∀ x, ConstAddrOf A c x → ¬ StoredAt t envT x) :
    CheckedUnit calls bAddr t envT E₀ lim A c := by
  have htwf : t.wf = true := by
    unfold Ix.Kernel.RoleTable.wf
    rw [ht]
    rfl
  refine ⟨hI.checked A c hIA hc, ?_, ?_, hns,
    fun x hx => keyFree_of_not_stored hctx.shape ht (hns x hx)⟩
  · intro i hi x hx
    exact Claim.inertKey_keyOf_false ht (hI.notInert A x hIA (usedRef_of_idx hc hi hx))
  · intro env h i hi x hx hnin
    have hused := usedRef_of_idx hc hi hx
    rcases hI.refsBelow A x hIA hused with hst | hcov | ⟨hok, hob⟩
    · obtain ⟨ci, hci, hname⟩ := hst
      exact Option.isSome_iff_exists.mp (find_isSome_of_storedAt ⟨ci, h.ext ci hci, hname⟩)
    · obtain ⟨ci, hci, hname⟩ := covered_stored hctx.shape htwf hcov
      exact Option.isSome_iff_exists.mp (find_isSome_of_storedAt ⟨ci, h.ext ci hci, hname⟩)
    · rcases h.refs x hused with hs | ho | hn
      · exact Option.isSome_iff_exists.mp hs
      · exfalso
        obtain ⟨D, hWD, hUD, hrk, cD, hcD, hown | ⟨rb, crb, hrb, hcrb, hxr⟩⟩ := hob
        · have hDA : D = A := walked_owns_apart hG hF hWD (Or.inr hIA) hcD hc hown ho
          rw [hDA] at hrk
          exact Nat.lt_irrefl _ hrk
        · have hAr : A = rb := walked_eq_famRecord hG hF (Or.inr hIA) hc ho hrb hcrb hxr
          rw [← hAr] at hrb
          exact hU D hrb
      · exact absurd hok hn

/-- **The step of a unit checked inside a family check is the step of its kind.** -/
theorem innerUnitStep_of_checked (hG : TopGraph t E₀ seeds Top rank)
    (hF : FamilyGraph t envT E₀ Top rank fam twin adv Inner)
    (hI : InnerChecked calls bAddr t envT E₀ lim Top rank fam twin Inner)
    (hctx : StepCtx.{u} calls t R envT E₀ E) (ht : t.check = .ok ())
    (hS : LoadedReads.RunStore calls E₀) (hcov : LoadedReads.HashedRecordsStored calls E₀)
    (hcanon : L1.CanonicalHashCoverage E calls)
    {X : Ix.Kernel.RoleTable → Ixon.Env → Ix.Kernel.Env .anon → Prop}
    {Kind : List (Call F) → Ix.Kernel.RoleTable → Ixon.Env → _root_.Address → Ixon.Constant →
      Prop}
    (hstep : CheckedUnitStep.{u} X Kind)
    {A : _root_.Address} {c : Ixon.Constant} (hIA : Inner A) (hU : Unclaimed fam A)
    (hc : recordOf E₀ A = some c) (hlog : InLogic c) (hkind : Kind calls t E₀ A c) :
    UnitStep.{u} (X t E) t envT E₀ E lim A c := by
  intro env hext hnd hinv hXe href hfresh
  have hns : ∀ x, ConstAddrOf A c x → ¬ StoredAt t envT x := by
    intro x hx hst
    obtain ⟨ci, hci, hname⟩ := hst
    have hs : (env.find? (keyOf t x)).isSome = true :=
      find_isSome_of_storedAt ⟨ci, hext ci hci, hname⟩
    rw [hfresh x hx] at hs
    simp at hs
  exact hstep calls bAddr t E₀ lim R envT E hctx A c hc hlog hkind ht hS hcov hcanon
    (checkedUnit_of_inner hG hF hI hctx ht hIA hU hc hns) env hext hnd hinv hXe href hfresh

/-- **The step of every unit checked inside a family check, from the step of each kind**, at
the fold's clause at the opened head trace: the family skeleton's step hypothesis for inner
units. The one kind step taken as a hypothesis is the one-type native block declared at its
telescope; the others are proved for every checked unit. -/
theorem innerUnitSteps_of_kinds
    (nativeBlockTelescope :
      CheckedUnitStep.{u} (FoldExtra.{u} FormerOpenTraceAt) fun calls t E₀ B cb =>
        ∃ ind : Ixon.Inductive,
          BlockUnitRecord E₀ B cb ind ∧ NativeRouteAt calls B ∧ FormerAtTele t E₀ B cb ind)
    (hG : TopGraph t E₀ seeds Top rank)
    (hF : FamilyGraph t envT E₀ Top rank fam twin adv Inner)
    (hI : InnerChecked calls bAddr t envT E₀ lim Top rank fam twin Inner)
    (ht : t.check = .ok ()) (hS : LoadedReads.RunStore calls E₀)
    (hcov : LoadedReads.HashedRecordsStored calls E₀) :
    ∀ E, StepCtx.{u} calls t R envT E₀ E → ∀ A c, Inner A → Unclaimed fam A →
      recordOf E₀ A = some c → InLogic c → UnitKind c → fam A = none → twin A = none →
      UnitStep.{u} (FoldExtra.{u} FormerOpenTraceAt t E) t envT E₀ E lim A c := by
  intro E hctx A c hIA hU hc hlog hk hfa htw
  have hcanon₀ : L1.CanonicalHashCoverage E₀ calls := by
    intro bytes value hashed size exactRead
    obtain ⟨entry, stored, bytesEq, cached⟩ := hcov bytes value hashed size
      (L1.deConstant_of_deConstantExact exactRead) exactRead
    refine ⟨⟨entry, value, stored, cached, ?_⟩, rfl⟩
    rw [bytesEq]
    exact exactRead
  have hcanon : L1.CanonicalHashCoverage E calls :=
    Assembly.canonicalHashCoverage_frame hcanon₀ hctx.recordsFor.1
      (fun a v h => hctx.runRecord a v ((hS.recordOf_eq_recordAt a).trans h))
  have step : ∀ {Kind : List (Call F) → Ix.Kernel.RoleTable → Ixon.Env → _root_.Address →
      Ixon.Constant → Prop},
      CheckedUnitStep.{u} (FoldExtra.{u} FormerOpenTraceAt) Kind → Kind calls t E₀ A c →
      UnitStep.{u} (FoldExtra.{u} FormerOpenTraceAt t E) t envT E₀ E lim A c :=
    fun h hkind => innerUnitStep_of_checked hG hF hI hctx ht hS hcov hcanon h hIA hU hc hlog hkind
  rcases hk with ⟨d, hinfo⟩ | ⟨rc, hinfo⟩ | ⟨ms, hinfo⟩
  · exact step (standaloneValue_checked linkLaws_formerOpenTrace) ⟨d, hinfo⟩
  · exact step standaloneRecursor_checked ⟨rc, hinfo⟩
  · by_cases hdefs : DefnBlock ms
    · exact step (definitionBlock_checked linkLaws_formerOpenTrace) ⟨ms, hinfo, hdefs⟩
    · by_cases h0 : ms.size = 0
      · exact unitStep_emptyBlock hinfo h0
      · obtain ⟨⟨ind, hms⟩, hobs⟩ := hI.blocks A c ms hIA hU htw hc hinfo hdefs h0
        have hnat : NativeRouteAt calls A :=
          nativeRouteAt_of_nativeObs (c := ⟨E, envT, t, lim⟩) (hctx.good envT lim) hcanon hobs
        rw [hms] at hinfo
        have hmem := hF.innerMembers A c #[.indc ind] hIA hc hinfo 0 (.indc ind) (by rfl)
        have hrec : BlockUnitRecord E₀ A c ind :=
          ⟨hc, hinfo, hlog, hmem.1, fun j hj => hmem.2 ind j rfl hj⟩
        rcases formerAt_cases t E₀ A c ind with htele | halias | hother
        · exact step nativeBlockTelescope ⟨ind, hrec, hnat, htele⟩
        · exact step nativeBlockAlias_checked ⟨ind, hrec, hnat, halias⟩
        · exact step nativeBlockOtherTelescope_checked ⟨ind, hrec, hnat, hother⟩

end Inner

end IxVM.Refinement.Typing
