import IxVMRefinement.Binding.StoreOpOrder
import IxVMRefinement.RoleVal.BoundSafety
import IxVMRefinement.RoleVal.AxiomRecordLim

/-! # The references of a record a group's walk reaches

What the walk of group `g` observed of the references a record it reaches uses (`GroupReach`,
a record of the walk's closed list, `GroupReach.listed`).

* `new_reach_cases`: a record new in a group's admission that is no projection record and no
  axiom record is reached by the group's walk or through its payload.
* `walkedRef_needOk`: a reference a walk-reached record uses is one a step needs stored
  (`NeedOk`): a record of the run's store, no block, in Lean's logic with its block. Not already
  stored, the walk loaded it and found no block (`Claim.NotBlockIn`), listed it, and reaches it
  (`groupReach_sourceSafe_of_run`); already stored, it is bound to a walked role, walked anchor,
  operation, standard axiom, or quotient role, each of which is no block and in Lean's logic with
  its block.
* `RoleVal.validate_role_inert_record`, `RoleVal.ValidateRoleIn.inert_record`: for a role
  specified as an inert axiom, the record at the role's bound address is a safe axiom record,
  decoded from bytes the validation hashed (`KernelRoles::validate_inert_axiom` matches the loaded
  constant as an axiom and asserts its unsafe flag `0`).
* `walkedRef_not_inert`: no reference a walk-reached record uses is an inert axiom's. The walk
  asked `KernelRoles::assert_ref_allowed` about it, which admits a reference bound to an inert role
  only if the role's group is at or above the validation limit (`Claim.refAllowed_inert`). A
  covered reference is bound to a role of a group below the limit, the one role at its address.
  Otherwise the walk checked the reference's record at the limit; the record is the inert role's
  axiom record, and the check of an axiom record finds the role at its address in force
  (`Claim.checkedLimAt_standing_role`), of a group below the limit.
-/

set_option linter.unusedVariables false

namespace IxVM.Refinement.RoleVal

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open IxVM.Refinement.Core

set_option maxRecDepth 100000 in
/-- An inert role is specified as an inert axiom (decided). -/
theorem specKind_four_of_inert (ro : Ix.Kernel.Role) (h : ro.inert = true) :
    roleSpecKindNat ro = 4 := by
  cases ro <;> first | rfl | exact absurd h (by decide)

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 100000 in
/-- **The record of an inert axiom, in the role's validation**: the record at the role's bound
address is decoded from bytes the validation hashed, and it is a safe axiom record. -/
theorem validate_role_inert_record {t : Ix.Kernel.RoleTable} {bAddr : _root_.Address}
    {ro : Ix.Kernel.Role} {x_rc x_tbl r : SourceValue F} {h h' : Heap F}
    {calls : List (Call F)}
    (htbl : Claim.TableFullRep t bAddr h x_tbl)
    (ev : ObsFn W "KernelRoles::validate_role" [x_rc, x_tbl, .field (roleNum ro)] h r h' calls)
    (hk : roleSpecKindNat ro = 4) :
    ∃ (a : _root_.Address) (rawBytes : ByteArray) (c : Ixon.Constant) (ax : Ixon.Axiom),
      t.addressOf? ro = some a ∧ rawBytes.size < 4294967296 ∧ Hashed calls rawBytes ∧
      Address.blake3Pure rawBytes = a ∧ Ixon.deConstant rawBytes = .ok c ∧
      Ixon.deConstantExact rawBytes = .ok c ∧ c.info = .axio ax ∧ ax.isUnsafe = false := by
  cases Obs.«KernelRoles::validate_role».obs ev with
  | n0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ev124 _ _ =>
    obtain ⟨hsk_f, _⟩ := role_spec_kind_spec ev124
    rw [hk] at hsk_f
    exact absurd (Value.field.inj hsk_f) (by decide)
  | n1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ev124 _ _ =>
    obtain ⟨hsk_f, _⟩ := role_spec_kind_spec ev124
    rw [hk] at hsk_f
    exact absurd (Value.field.inj hsk_f) (by decide)
  | n2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ev124 _ _ =>
    obtain ⟨hsk_f, _⟩ := role_spec_kind_spec ev124
    rw [hk] at hsk_f
    exact absurd (Value.field.inj hsk_f) (by decide)
  | n3 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ev124 _ _ =>
    obtain ⟨hsk_f, _⟩ := role_spec_kind_spec ev124
    rw [hk] at hsk_f
    exact absurd (Value.field.inj hsk_f) (by decide)
  | n5 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ev124 _ _ =>
    obtain ⟨hsk_f, _⟩ := role_spec_kind_spec ev124
    rw [hk] at hsk_f
    exact absurd (Value.field.inj hsk_f) (by decide)
  | n4 v1 m2 cs12 v31 m32 p39 cs45 v67 v68 m70 cs78 m90 cs98 m111 cs122 cs332
      ev14 ev47 ld41 ev80 ev100 _ ev124 ev334 hc367 =>
    obtain ⟨-, a, ha_m2, had⟩ := role_bound_addr_uncond htbl.toTableRep ev14
    obtain ⟨ab, hab, rfl⟩ := ha_m2
    match Obs.«KernelRoles::validate_inert_axiom».obs ev334 with
    | .run (hv15 := hci) (heq58 := hu) .. =>
      rw [hci] at ld41
      obtain ⟨rawBytes, c, ax, hsz, hh, hblk, hde, hdeE, hinfo, hu'⟩ :=
        Claim.get_ci_axiom_record hab ev47 ld41
      have hsafe : ax.isUnsafe = false := by
        cases hb : ax.isUnsafe with
        | false => rfl
        | true =>
          rw [hb, hu] at hu'
          have e : (Value.field (0 : F) : SourceValue F) = .field 1 := hu'
          exact absurd (Value.field.inj e) zero_ne_one
      have hsub : ∀ cl ∈ cs45, cl ∈ calls := fun cl hm => by rw [hc367]; simp [hm]
      exact ⟨_, rawBytes, c, ax, had, hsz, Claim.hashed_mono hsub hh, hblk, hde, hdeE, hinfo,
        hsafe⟩

/-- **The same from the observed validation of the role.** -/
theorem ValidateRoleIn.inert_record {calls : List (Call F)} {bAddr : _root_.Address}
    {t : Ix.Kernel.RoleTable} {g : Nat} {ro : Ix.Kernel.Role}
    (hv : ValidateRoleIn calls bAddr t g ro) (hk : roleSpecKindNat ro = 4) :
    ∃ (a : _root_.Address) (rawBytes : ByteArray) (c : Ixon.Constant) (ax : Ixon.Axiom),
      t.addressOf? ro = some a ∧ rawBytes.size < 4294967296 ∧ Hashed calls rawBytes ∧
      Address.blake3Pure rawBytes = a ∧ Ixon.deConstant rawBytes = .ok c ∧
      Ixon.deConstantExact rawBytes = .ok c ∧ c.info = .axio ax ∧ ax.isUnsafe = false := by
  obtain ⟨h, h', x_rc, x_tbl, res, cs, hrc, htbl, ev, hsub⟩ := hv
  obtain ⟨a, rawBytes, c, ax, had, hsz, hh, hblk, hde, hdeE, hinfo, hsafe⟩ :=
    validate_role_inert_record htbl ev hk
  exact ⟨a, rawBytes, c, ax, had, hsz, Claim.hashed_mono hsub hh, hblk, hde, hdeE, hinfo, hsafe⟩

end IxVM.Refinement.RoleVal

namespace IxVM.Refinement.Binding

open IxVM.Consistency
open IxVM.Refinement.Typing
open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library
open IxVM (F)
open IxVM.Refinement.StoreInhabit (basisStore)

private def quotRowOk (r : Ix.Kernel.Role) : Bool :=
  match ctab.addressOf? r with
  | none => false
  | some a =>
    StoreInhabit.basisRows.any fun e =>
      e.1 == a && match e.2.info with
        | .quot _ => true
        | .axio ax => !ax.isUnsafe
        | _ => false

set_option maxRecDepth 100000 in
private theorem quotRole_basis_ok :
    ∀ r : Ix.Kernel.Role, RoleVal.isQuotRole r = true →
      r ∈ TableInhabit.basisRoleOrder ∧ quotRowOk r = true := by
  intro r
  cases r <;> decide +kernel

section Run

variable {calls : List (Call F)} {bAddr : _root_.Address} {t : Ix.Kernel.RoleTable}
  {E₀ : Ixon.Env} {Pay : PayloadRel}

/-- **A new record that is no projection record and no axiom record is reached by the group's
walk or through its payload** (`groupAdds_cases`, `payAdds_cases`): the other records a group
adds are the projection records beside a reached block and the group's standard axiom. -/
theorem new_reach_cases (hC : CollisionFreeRun calls E₀) (hb : BasisRowsLoaded E₀)
    (hax : AxiomRolesDeclared t E₀) (hP : PayloadFacts t E₀ Pay) {g : Nat} (hg : 6 ≤ g)
    {recs : List (Claim.TopRec calls bAddr t (some (valLimit g)))}
    (hw : GroupWalked calls bAddr t E₀ g recs) {a : _root_.Address} {c : Ixon.Constant}
    (hnew : New (groupStore t E₀ Pay g) (groupStore t E₀ Pay (g + 1)) a)
    (hE : recordOf E₀ a = some c) (hnp : ¬ IsProj c) (hna : ∀ ax, c.info ≠ .axio ax) :
    GroupReach t E₀ g a ∨ PayReach t E₀ Pay g a := by
  obtain ⟨-, -, -, hadd, -⟩ := new_groupStore hb hg hnew
  rcases groupAdds_cases hC hax hw hadd with ⟨hra, -⟩ | ⟨-, -, -, -, p, hp, hproj, -⟩ |
      ⟨-, -, -, -, c₂, ax, hc₂, hinfo, -⟩ | hpay
  · exact Or.inl hra
  · have e : p = c := Option.some.inj (hp.symm.trans hE)
    rw [e] at hproj
    exact (hnp hproj).elim
  · have e : c₂ = c := Option.some.inj (hc₂.symm.trans hE)
    rw [e] at hinfo
    exact (hna ax hinfo).elim
  · rcases payAdds_cases hP hpay with ⟨hr, -⟩ | ⟨-, -, -, -, -, p, hp, hproj, -⟩
    · exact Or.inr hr
    · have e : p = c := Option.some.inj (hp.symm.trans hE)
      rw [e] at hproj
      exact (hnp hproj).elim

/-- The bound record of a walked role or walked anchor is `NeedOk`. -/
private theorem walkedRole_needOk (hC : CollisionFreeRun calls E₀)
    (hval : ∀ g, g < 77 → ∀ r ∈ roleGroup g, RoleValidationIn calls bAddr t g r)
    (hroots : RootsSafe t E₀) {r : Ix.Kernel.Role}
    (hwk : RoleVal.roleWalksBound r = true ∨ RoleVal.anchorWalked r = true)
    {x : _root_.Address} (had : t.addressOf? r = some x) : NeedOk E₀ x := by
  have hsafe := hroots.bound r hwk x had
  obtain ⟨a', had', h₀, h₁, ap, ptr, v, cs, ha, ev, hsub, -, -⟩ :=
    RoleVal.ValidateRoleIn.bound_load_safe
      (show RoleVal.ValidateRoleIn calls bAddr t (Ix.SpecDigest.groupOf r) r from
        hval _ (RoleVal.groupOf_lt_77 r) r (role_mem_roleGroup r))
      (RoleVal.roleSpecKind_of_walked r hwk)
  have e : a' = x := Option.some.inj (had'.symm.trans had)
  rw [e] at ha
  obtain ⟨ab, hab, hab'⟩ := ha
  obtain ⟨raw, c', hsz, hh, hba, hx', -, hhead⟩ := Claim.get_ci_head hab ev
  have hcx : recordOf E₀ x = some c' := by
    rw [← hab', ← hba]
    exact Claim.recordOf_hashed hC.runStore hC.hashedStored (Core.hashed_mono hsub hh) hsz
      (L1.deConstant_of_deConstantExact hx') hx'
  exact ⟨c', hcx, fun ⟨ms, hms⟩ => hhead.notMuts ms hms, (hsafe c' hcx).1, (hsafe c' hcx).2⟩

/-- **A reference a walk-reached record uses is one a step needs stored** (module docstring). -/
theorem walkedRef_needOk (hC : CollisionFreeRun calls E₀) (hb : BasisRowsLoaded E₀)
    (hpin : PreludePinned t) (hax : AxiomRolesDeclared t E₀)
    (hval : ∀ g, g < 77 → ∀ r ∈ roleGroup g, RoleValidationIn calls bAddr t g r)
    (hroots : RootsSafe t E₀) {g : Nat} (hg : g < 77)
    {recs : List (Claim.TopRec calls bAddr t (some (valLimit g)))}
    (hw : GroupWalked calls bAddr t E₀ g recs) {A x : _root_.Address}
    (hA : GroupReach t E₀ g A) (hu : UsedRef E₀ A x) : NeedOk E₀ x := by
  by_cases hst : AlreadyStoredRole t g x
  · rcases hst with ⟨r, had, hwr, -⟩ | ⟨r, had, -, hkind⟩ | ⟨r, had, hk2, -⟩
    · have hwb : RoleVal.roleWalksBound r = true := by
        rw [← Claim.walkedRole_eq_roleWalksBound]
        exact hwr
      exact walkedRole_needOk hC hval hroots (Or.inl hwb) had
    · rcases hkind with hwk | hs | hq
      · exact walkedRole_needOk hC hval hroots (Or.inr hwk) had
      · obtain ⟨c, ax, hc, hi, hsafe⟩ := hax r hs x had
        refine ⟨c, hc, fun ⟨ms, hms⟩ => by rw [hi] at hms; cases hms,
          (by simp only [InLogic, hi, hsafe]), fun cb hcb => ?_⟩
        have hown : Ix.Cert.ownerOf x c = x := by simp [Ix.Cert.ownerOf, hi]
        rw [hown, hc] at hcb
        cases Option.some.inj hcb
        simp only [InLogic, hi, hsafe]
      · obtain ⟨hbas, hok⟩ := quotRole_basis_ok r hq
        have hctab : ctab.addressOf? r = some x := by
          rw [← addressOf_basis hpin hbas]; exact had
        unfold quotRowOk at hok
        simp only [hctab] at hok
        obtain ⟨⟨a', c⟩, hmem, hcond⟩ := List.any_eq_true.mp hok
        obtain ⟨ha', hinfoOk⟩ := Bool.and_eq_true.mp hcond
        have ea : a' = x := beq_iff_eq.mp ha'
        subst ea
        have hrecB : recordOf basisStore a' = some c := StoreInhabit.store_record_of_mem hmem
        have hgetB : basisStore.consts.get? a' = some (StoreInhabit.mkLazy (Ixon.serConstant c) c) :=
          StoreInhabit.store_get?_of_mem hmem
        have hE : recordOf E₀ a' = some c := by
          unfold recordOf at hrecB ⊢
          rw [hgetB] at hrecB
          rw [hb a' _ hgetB]
          exact hrecB
        cases hci : c.info with
        | quot q =>
          refine ⟨c, hE, fun ⟨ms, hms⟩ => by rw [hci] at hms; cases hms,
            (by simp only [InLogic, hci]), fun cb hcb => ?_⟩
          have hown : Ix.Cert.ownerOf a' c = a' := by simp [Ix.Cert.ownerOf, hci]
          rw [hown, hE] at hcb
          cases Option.some.inj hcb
          simp only [InLogic, hci]
        | axio ax =>
          simp only [hci] at hinfoOk
          have hsafe : ax.isUnsafe = false := by
            cases hu' : ax.isUnsafe <;> simp [hu'] at hinfoOk ⊢
          refine ⟨c, hE, fun ⟨ms, hms⟩ => by rw [hci] at hms; cases hms,
            (by simp only [InLogic, hci, hsafe]), fun cb hcb => ?_⟩
          have hown : Ix.Cert.ownerOf a' c = a' := by simp [Ix.Cert.ownerOf, hci]
          rw [hown, hE] at hcb
          cases Option.some.inj hcb
          simp only [InLogic, hci, hsafe]
        | defn _ | recr _ | muts _ | dPrj _ | iPrj _ | cPrj _ | rPrj _ =>
          simp only [hci] at hinfoOk; cases hinfoOk
    · exact walkedRole_needOk hC hval hroots
        (Or.inl (op_walksBound ((specKind_two_iff r).mp hk2))) had
  · have hcov : ¬ Claim.CoveredAt t (some (valLimit g)) x := AlreadyStoredRole.not_covered hst
    have hsafe := groupReach_sourceSafe_of_run hC hval hroots hg hw x (GroupReach.ref hA hu hst)
    obtain ⟨y, hy, hya⟩ := hA.listed hC.hashedStored hw
    obtain ⟨c, i, hc, hi, hx⟩ := hu
    have hrec := topRec_recordOf hC.hashedStored y
    rw [hya] at hrec
    have ec : c = y.c := Option.some.inj (hc.symm.trans hrec)
    rw [ec] at hi hx
    rcases ((hw.closed y hy).2 i (by rw [Assembly.usedRefIdxs_eq]; exact hi) x hx).2 with
      ⟨⟨raw, cx, hh, hbl, hde, hnb⟩, y', hy', hya', -⟩ | hcov'
    · have hcx := topRec_recordOf hC.hashedStored y'
      rw [hya'] at hcx
      have eb : raw = y'.rawBytes :=
        hC.runStore.hashed_inj hh y'.hhashed (by rw [hbl, y'.hblake, hya'])
      have ecx : cx = y'.c := by
        have h1 := y'.hde
        rw [← eb, hde] at h1
        exact Except.ok.inj h1
      rw [← ecx] at hcx
      exact ⟨cx, hcx, fun ⟨ms, hms⟩ => hnb ms hms, (hsafe cx hcx).1, (hsafe cx hcx).2⟩
    · exact (hcov hcov').elim

/-- **No reference a walk-reached record uses is an inert axiom's** (module docstring). -/
theorem walkedRef_not_inert (hC : CollisionFreeRun calls E₀)
    (hval : ∀ g, g < 77 → ∀ r ∈ roleGroup g, RoleValidationIn calls bAddr t g r) {g : Nat}
    {recs : List (Claim.TopRec calls bAddr t (some (valLimit g)))}
    (hw : GroupWalked calls bAddr t E₀ g recs) {A x : _root_.Address}
    (hA : GroupReach t E₀ g A) (hu : UsedRef E₀ A x) : ¬ InertAt t x := by
  rintro ⟨ro, hin, hof⟩
  have hv := hval _ (RoleVal.groupOf_lt_77 ro) ro (role_mem_roleGroup ro)
  have hwf := hv.wf
  obtain ⟨y, hy, hya⟩ := hA.listed hC.hashedStored hw
  obtain ⟨c, i, hc, hi, hx⟩ := hu
  have hrec := topRec_recordOf hC.hashedStored y
  rw [hya] at hrec
  have ec : c = y.c := Option.some.inj (hc.symm.trans hrec)
  rw [ec] at hi hx
  obtain ⟨hal, hrest⟩ := (hw.closed y hy).2 i (by rw [Assembly.usedRefIdxs_eq]; exact hi) x hx
  obtain ⟨n, hn, hle⟩ := Claim.refAllowed_inert hal hin hof
  have e : n = valLimit g := (Option.some.inj hn).symm
  rw [e] at hle
  rcases hrest with ⟨-, y', hy', hya', -⟩ | ⟨r, had, -, hlt⟩
  · obtain ⟨a, raw, cx, ax, had, hsz, hh, hbl, hde, hdeE, hinfo, hsafe⟩ :=
      RoleVal.ValidateRoleIn.inert_record
        (show RoleVal.ValidateRoleIn calls bAddr t (Ix.SpecDigest.groupOf ro) ro from hv)
        (RoleVal.specKind_four_of_inert ro hin)
    have ea : a = x := Option.some.inj (had.symm.trans hof)
    have hcx : recordOf E₀ x = some cx := by
      rw [← ea, ← hbl]
      exact Claim.recordOf_hashed hC.runStore hC.hashedStored hh hsz hde hdeE
    have hl : InLogic cx := by simp only [InLogic, hinfo, hsafe]
    have hyc : y'.c = cx := by
      have h1 := topRec_recordOf hC.hashedStored y'
      rw [hya', hcx] at h1
      exact (Option.some.inj h1).symm
    have hchk : Claim.CheckedLimAt calls bAddr t x (some (valLimit g)) := by
      rcases y'.hchecked with ⟨ms, hms, -⟩ | hck
      · rw [hyc, hinfo] at hms
        cases hms
      · rw [hya'] at hck
        exact hck
    obtain ⟨ro', hb', hcase⟩ :=
      Claim.checkedLimAt_standing_role hC.runStore hcx hl (Or.inl ⟨ax, hinfo⟩) hchk
    rcases hcase with ⟨-, hforce, -⟩ | ⟨⟨q, hq⟩, -⟩
    · have e' : ro' = ro := addressOf_role_inj hwf hb' hof
      have hlt := hforce _ rfl
      rw [e'] at hlt
      exact absurd hlt (Nat.not_lt.mpr hle)
    · rw [hinfo] at hq
      cases hq
  · have e' : r = ro := addressOf_role_inj hwf had hof
    have hlt' := hlt _ rfl
    rw [e'] at hlt'
    exact absurd hlt' (Nat.not_lt.mpr hle)

end Run

end IxVM.Refinement.Binding
