import IxVMRefinement.Binding.AxiomValidation
import IxVMRefinement.Binding.OpRefsStored
import IxVMRefinement.Binding.OpRefine
import IxVMRefinement.Binding.OpRoleUnit
import IxVMRefinement.Binding.WalkChecks
import IxVMRefinement.RoleVal.GroupWalkLim
import IxVMRefinement.Claim.TopDefn

/-! # What a binding run's validation of an operation gives the fold

`KernelRoles::validate_role` at an operation (`KernelRoles.lean:756`, kind 2) loads the bound
constant (`get_ci`) and checks that it has no universe parameter; `validate_op`
(`KernelRoles.lean:968`) loads the record and asserts it a standalone definition, asserts it
safe, pins its type (`assert_type_pinned(ty, role_type(tbl, r))`), walks the record with its
closure (`run_check_transitive(rc, a)`), and compares the recurrences or checks the
certificates (`validate_op_equations`). This file reads those observations.

* `validate_role_op_obs`: **the record and the pin**: the record at the bound address is a
  safe standalone definition with no universe parameter, and every annotation of the reading of
  its type has the operation's shape (`RoleOps.OpTyShape`).
* `op_walk_facts`: **the walk**: the record is checked under the group's role context at the
  group's validation limit, and each reference it uses is a checked record in Lean's logic that
  is no block, or the address of a walked role of an earlier group.
* `Typing.checkedLimAt_defn_canon`: `Typing.checkedLimAt_defn_step` with the reading and the
  canonical annotations exposed (the stored terms are the ones every load represents).
* `opFront_of_checkedLim`: the definition's check (`RoleOps.OpFront`) at the closure's
  environment from that check evidence.
* `OpEquationFacts`: what `validate_op_equations` gives: one comparison per recurrence
  (`OpRefine.EqObs`) or one checked proof per certificate statement (`OpRefine.CertObs`).
* `opValidationFactsW_of_equations`: **`OpValidationFactsW` from `OpEquationFacts`**: the record
  is new (the closure's coverage would otherwise store the operation, which the invariant below
  the group excludes), its references are stored (`usedRefsStored_of_walkedStored`), the check,
  the pin, the reading over the store after the group, and the reload.
-/

universe u

set_option linter.unusedVariables false

namespace IxVM.Refinement.Binding

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library
open IxVM (F)
open IxVM.Refinement.Core
open Ix.Kernel (Role)
open Ix.Kernel.Semantics (NativeFam)

/-! ## Decided facts of the operations -/

set_option maxRecDepth 100000 in
/-- The roles specified as operations are the fifteen `Nat` operations. -/
theorem specKind_two_iff (ro : Role) :
    RoleVal.roleSpecKindNat ro = 2 ↔ ro ∈ RoleOps.opRoles := by
  cases ro <;> decide

set_option maxRecDepth 100000 in
/-- An operation's record is walked, it has no universe parameter, and it has a specified type. -/
theorem op_facts_all : ∀ r ∈ RoleOps.opRoles,
    IxVM.Consistency.walkedRole r = true ∧ specLevels r = some 0 ∧
      (specTypeRaw r).isSome = true := by
  decide +kernel

private theorem claimInfo_defn {h : Heap F} {info : Ixon.ConstantInfo} {dv : SourceValue F}
    (hinfo : Claim.RepConstantInfo h info (.construct "Ixon::ConstantInfo" "Defn" [dv])) :
    ∃ d : Ixon.Definition, info = .defn d := by
  cases info with
  | defn d => exact ⟨d, rfl⟩
  | recr _ | axio _ | quot _ | cPrj _ | rPrj _ | iPrj _ | dPrj _ | muts _ =>
    obtain ⟨_, hmk, _⟩ := hinfo
    simp at hmk

theorem defnConst_toConstantVal (k : Ix.DefKind) (cv : Ix.Kernel.ConstantVal .anon)
    (v : KExpr) (hn : Ix.Kernel.ReducibilityHint) :
    (LoadedReads.defnConst k cv v hn).toConstantVal = cv := by
  cases k <;> rfl

theorem recordOf_sub {R R' : Ixon.Env}
    (h : ∀ a lc, R.consts.get? a = some lc → R'.consts.get? a = some lc) :
    ∀ x c, IxVM.Consistency.recordOf R x = some c → IxVM.Consistency.recordOf R' x = some c := by
  intro x c hc
  unfold IxVM.Consistency.recordOf at hc ⊢
  cases hg : R.consts.get? x with
  | none => rw [hg] at hc; cases hc
  | some lc => rw [hg] at hc; rw [h x lc hg]; exact hc

/-! ## The record and the pin -/

set_option maxHeartbeats 3200000 in
/-- **The record and the pin of an operation, from its observed validation** (module
docstring). The pin is stated for every record store that holds the record, at which the
validation's calls hash no collision, and for every well-scoped reading of the record over it. -/
theorem validate_role_op_obs {t : Ix.Kernel.RoleTable} (ht : t.check = .ok ())
    {calls : List (Call F)} {bAddr : _root_.Address} {g : Nat} {r : Role} {E₀ : Ixon.Env}
    (hS : LoadedReads.RunStore calls E₀) (hH : LoadedReads.HashedRecordsStored calls E₀)
    (hv : RoleVal.ValidateRoleIn calls bAddr t g r) (hop : r ∈ RoleOps.opRoles) :
    ∃ (a : _root_.Address) (c : Ixon.Constant) (d : Ixon.Definition),
      t.addressOf? r = some a ∧ IxVM.Consistency.recordOf E₀ a = some c ∧ c.info = .defn d ∧
      d.kind = .defn ∧ d.safety = .safe ∧ d.lvls.toNat = 0 ∧
      ∀ (Ec : Ixon.Env) (env : Ix.Kernel.Env .anon) (ty₀ val₀ : KExpr),
        Good ⟨Ec, env, t, none⟩ calls → IxVM.Consistency.recordOf Ec a = some c →
        (IxVM.Consistency.exprReader t (fun x => Ec.blobs.get? x) c id
          (IxVM.Consistency.soloSelf t a)).read d.typ = .ok ty₀ →
        (IxVM.Consistency.exprReader t (fun x => Ec.blobs.get? x) c id
          (IxVM.Consistency.soloSelf t a)).read d.value = .ok val₀ →
        ty₀.looseBVarsBounded 0 = true → ty₀.allLevelParamsDefined [] = true →
        val₀.looseBVarsBounded 0 = true → val₀.allLevelParamsDefined [] = true →
        ∀ ty, IxVM.Consistency.Annotates ty ty₀ → RoleOps.OpTyShape (.role r) ty := by
  obtain ⟨h, h', x_rc, x_tbl, res, cs, hrc, htbl, ev, hsubV⟩ := hv
  have htwf : t.wf = true := wf_of_check ht
  obtain ⟨-, hn₀, hTS⟩ := op_facts_all r hop
  obtain ⟨T₀, hT⟩ := Option.isSome_iff_exists.mp hTS
  have hk2 : RoleVal.roleSpecKindNat r = 2 := (specKind_two_iff r).mpr hop
  have htblR : TableRep t h x_tbl := htbl.toTableRep
  cases Obs.«KernelRoles::validate_role».obs ev with
  | n2 v1 m2 cs12 v31 m32 p39 cs45 v67 v68 m70 cs78 m90 cs98 m111 cs122 cs236
      ev14 ev47 ld41 ev80 ev100 heq109 ev124 ev238 hc279 =>
    have hsub45 : ∀ cl ∈ cs45, cl ∈ calls := fun cl hm => hsubV cl (by rw [hc279]; simp [hm])
    have hsub236 : ∀ cl ∈ cs236, cl ∈ calls := fun cl hm => hsubV cl (by rw [hc279]; simp [hm])
    obtain ⟨ext_ba, a, ha_m2, had⟩ := RoleVal.role_bound_addr_uncond htblR ev14
    have ext_m111 : Heap.Extends m2 m111 :=
      ev47.heap_extends.trans (ev80.heap_extends.trans
        (ev100.heap_extends.trans ev124.heap_extends))
    match Obs.«KernelRoles::validate_op».obs ev238 with
    | .other (heq575 := hbad) .. => exact (zero_ne_one (Value.field.inj hbad)).elim
    | .Defn (m2 := rawHeap) (m200 := m200) (cs12 := csLd) (x_ty := x_ty)
        (x_safety := x_safety) (ev14 := rawLoad) (hv114 := hci) (sg207 := sg)
        (ev242 := evT) (ev221 := evP) (hc544 := hca) .. =>
      have hsubLd : ∀ cl ∈ csLd, cl ∈ calls := fun cl hm =>
        hsub236 cl (by rw [hca]; simp [hm])
      -- the record: a standalone definition
      obtain ⟨-, rawBytes, c, hsz, hh, hblk, hde, hdeE, hrep, -⟩ :=
        Claim.load_verified_constant_de (S0.addr_mono ext_m111 ha_m2) rawLoad
      obtain ⟨iv, _, _, _, _, hmk, hiv, -⟩ := hrep
      have hargs := (Value.construct.inj hmk).2.2
      injection hargs with hiv_eq
      rw [← hiv_eq] at hiv
      obtain ⟨d, hinfo⟩ := claimInfo_defn hiv
      have hcE : IxVM.Consistency.recordOf E₀ a = some c := by
        rw [← hblk]
        exact Claim.recordOf_hashed hS hH (Claim.hashed_mono hsubLd hh) hsz hde hdeE
      obtain ⟨b, hbr, hba⟩ := ha_m2
      subst hba
      have hrecA : Ix.Cert.recordAt E₀ (ixAddr b) = some c := by
        rw [← hS.recordOf_eq_recordAt]
        exact hcE
      -- the load of `get_ci` in the role's validation
      obtain ⟨raw', c', hh', ha', hex', hres⟩ := L1.get_ci_trace_spec hbr ev47
      have hcc : c' = c := hS.record_eq hrecA (Core.hashed_mono hsub45 hh') ha' hex'
      rw [hcc] at hres
      unfold L1.GetCITraceResult at hres
      rw [hinfo] at hres
      obtain ⟨blobs, tree, v, hhp, built, hld, htr⟩ := hres
      have hv31 : v = v31 := Except.ok.inj (hld.symm.trans ld41)
      obtain ⟨hnlvls, tyPtr, valPtr, hintV, hvsh, -, -⟩ := htr.toRaw
      -- the kind and the safety
      have hci' := hci
      rw [← hv31, hvsh] at hci'
      have hkind : d.kind = .defn := by
        cases hk : d.kind with
        | defn => rfl
        | opaq => simp [L1.defnValShape, hk, Core.kciEnum] at hci'
        | thm => simp [L1.defnValShape, hk, Core.kciEnum] at hci'
      have hsh : L1.defnValShape d tyPtr valPtr hintV = .construct Core.kciEnum "Defn"
          [.field (d.lvls.toNat : F), tyPtr, valPtr, L1.repDefSafetyVal d.safety, hintV] := by
        simp [L1.defnValShape, hkind]
      rw [hsh] at hci'
      have hfl := (Value.construct.inj hci').2.2
      simp only [List.cons.injEq] at hfl
      obtain ⟨-, hxty, -, hxsafe, -⟩ := hfl
      have ext_sg : Heap.Extends rawHeap m200 := by
        cases sg with
        | Safe _ _ he _ => rw [he]
        | other _ hbad _ _ _ => exact absurd (Value.field.inj hbad) zero_ne_one
      have hsafety : d.safety = .safe := by
        cases sg with
        | Safe hs _ _ _ =>
          rw [← hxsafe] at hs
          cases hds : d.safety with
          | safe => rfl
          | unsaf => rw [hds] at hs; simp [L1.repDefSafetyVal] at hs
          | part => rw [hds] at hs; simp [L1.repDefSafetyVal] at hs
        | other _ hbad _ _ _ => exact absurd (Value.field.inj hbad) zero_ne_one
      -- no universe parameter
      have ev80' := ev80
      rw [← hv31, hvsh, hsh] at ev80'
      obtain ⟨e67, -⟩ := const_num_lvls_fields ev80'
      obtain ⟨e68, -, hlt8⟩ := role_levels_spec hn₀ ev100
      have hlv0 : d.lvls.toNat = 0 := by
        have hf' : ((d.lvls.toNat : Nat) : F) = ((0 : Nat) : F) :=
          Value.field.inj (e67.symm.trans (heq109.trans e68))
        have hv' := congrArg ZMod.val hf'
        rw [RolesAux.val_natCast (by omega), RolesAux.val_natCast (by omega)] at hv'
        exact hv'
      have hlogic : IxVM.Consistency.InLogic c := by
        unfold IxVM.Consistency.InLogic
        rw [hinfo]
        show Ix.Kernel.Reader.safetyDecline d = none
        unfold Ix.Kernel.Reader.safetyDecline
        rw [hkind, hsafety]
        rfl
      refine ⟨ixAddr b, c, d, had, hcE, hinfo, hkind, hsafety, hlv0, ?_⟩
      -- the pin
      intro Ec env ty₀ val₀ hgood hcEc hty hval hlbbT hdefT hlbbV hdefV ty hann
      have hgE : Good ⟨Ec, env, t, none⟩ cs45 := hgood.sub hsub45
      have hdefT' : ty₀.allLevelParamsDefined (List.range d.lvls.toNat) = true := by
        rw [hlv0]; exact hdefT
      have hdefV' : val₀.allLevelParamsDefined (List.range d.lvls.toNat) = true := by
        rw [hlv0]; exact hdefV
      obtain ⟨tyP, valP, -, -, hannP, -, hrepP⟩ :=
        LoadedReads.get_ci_defn_canon_exact ht hgE.1 hbr ev47 hcEc hinfo hlogic hty hval hlbbT
          hdefT' hlbbV hdefV'
      obtain ⟨v', hldv, hciv⟩ := hrepP .opaque
      have hvv : v' = v := Except.ok.inj (hldv.symm.trans hld)
      obtain ⟨tag, nl, tyF, rest, hvF, hvr⟩ := ciRepExact_typeField hciv
      rw [defnConst_toConstantVal] at hvr
      have htyF : tyF = x_ty := by
        have e := hvF.symm.trans (hvv.trans (hvsh.trans hsh))
        have e2 := (Value.construct.inj e).2.2
        simp only [List.cons.injEq] at e2
        exact e2.2.1.trans hxty
      have htm : Decl.TmCExact (Core.keyOf t) m32 tyP x_ty := by
        have h4 := hvr.2.2.2
        dsimp only at h4
        rw [Decl.posOf_range, htyF] at h4
        exact h4
      have ext32_200 : Heap.Extends m32 m200 :=
        (ev80.heap_extends.trans (ev100.heap_extends.trans ev124.heap_extends)).trans
          (rawLoad.heap_extends.trans ext_sg)
      have htbl200 : TableRep t m200 x_tbl :=
        htblR.mono (ext_ba.trans (ev47.heap_extends.trans ext32_200))
      have hpinE : tyP.erasePw = T₀.erasePw :=
        typePinned_erasePw htwf hT htbl200 (htm.mono ext32_200) evT evP
      exact opTyShape_of_pinned hop hT ((annotates_erasePw_eq hann hannP).trans hpinE)
  | n0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ev124 _ _ =>
    obtain ⟨hsk_f, -⟩ := RoleVal.role_spec_kind_spec ev124
    rw [hk2] at hsk_f
    exact absurd (Value.field.inj hsk_f) (by decide)
  | n1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ev124 _ _ =>
    obtain ⟨hsk_f, -⟩ := RoleVal.role_spec_kind_spec ev124
    rw [hk2] at hsk_f
    exact absurd (Value.field.inj hsk_f) (by decide)
  | n3 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ev124 _ _ =>
    obtain ⟨hsk_f, -⟩ := RoleVal.role_spec_kind_spec ev124
    rw [hk2] at hsk_f
    exact absurd (Value.field.inj hsk_f) (by decide)
  | n4 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ev124 _ _ =>
    obtain ⟨hsk_f, -⟩ := RoleVal.role_spec_kind_spec ev124
    rw [hk2] at hsk_f
    exact absurd (Value.field.inj hsk_f) (by decide)
  | n5 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ev124 _ _ =>
    obtain ⟨hsk_f, -⟩ := RoleVal.role_spec_kind_spec ev124
    rw [hk2] at hsk_f
    exact absurd (Value.field.inj hsk_f) (by decide)

/-! ## The walk -/

/-- **The walk of an operation's record, from its observed validation** (module docstring):
the record's check under the group's role context at the group's validation limit, and what
the walk gives each reference the record uses. -/
theorem op_walk_facts {t : Ix.Kernel.RoleTable} {calls : List (Call F)} {ρ : BRun}
    {Rs : Nat → Ixon.Env} (hrun : BindingRun calls t ρ Rs) {bAddr : _root_.Address}
    (hρ : ρ = observedRun calls bAddr t ρ.E₀ ρ.rank) {g : Nat} {r : Role} {a : _root_.Address}
    {R R' : Ixon.Env} {c : Ixon.Constant} {d : Ixon.Definition}
    (hval : RoleVal.ValidateRoleIn calls bAddr t g r) (hop : r ∈ RoleOps.opRoles)
    (ha : t.addressOf? r = some a) (hadm : Admits ρ t g R R')
    (hcE : IxVM.Consistency.recordOf ρ.E₀ a = some c) (hinfo : c.info = .defn d)
    (hlogic : IxVM.Consistency.InLogic c) (hcR' : IxVM.Consistency.recordOf R' a = some c) :
    Claim.CheckedLimAt calls bAddr t a (some (valLimit g)) ∧
    ∀ x, Typing.UsedRef R' a x →
      (∃ (cx : Ixon.Constant) (n : Nat), IxVM.Consistency.recordOf R' x = some cx ∧
        (∀ ms, cx.info ≠ .muts ms) ∧ IxVM.Consistency.InLogic cx ∧
        (∀ cb, IxVM.Consistency.recordOf R' (Ix.Cert.ownerOf x cx) = some cb →
          IxVM.Consistency.InLogic cb) ∧ ρ.checked x n) ∨
      (∃ r', IxVM.Consistency.walkedRole r' = true ∧ Ix.SpecDigest.groupOf r' < g ∧
        t.addressOf? r' = some x) := by
  have hwr : RoleVal.roleWalksBound r = true := by
    rw [← Claim.walkedRole_eq_roleWalksBound]
    exact (op_facts_all r hop).1
  obtain ⟨a₂, recs, ha₂, hcl, hmem⟩ := RoleVal.ValidateRoleIn.lim_walks hval (Or.inl hwr)
  have e₂ : a₂ = a := Option.some.inj (ha₂.symm.trans ha)
  rw [e₂] at hmem
  obtain ⟨ra, hra, hraA⟩ := List.mem_map.mp hmem
  have hraE : IxVM.Consistency.recordOf ρ.E₀ a = some ra.c := by
    rw [← hraA]
    exact topRec_recordOf hrun.hashedStored ra
  have hrac : ra.c = c := Option.some.inj (hraE.symm.trans hcE)
  have hchk : Claim.CheckedLimAt calls bAddr t a (some (valLimit g)) := by
    rcases ra.hchecked with ⟨ms, hms, -⟩ | hc
    · rw [hrac, hinfo] at hms
      cases hms
    · rw [← hraA]
      exact hc
  refine ⟨hchk, fun x hu => ?_⟩
  obtain ⟨c₂, i, hc₂, hi, hx⟩ := hu
  have e₃ : c₂ = c := Option.some.inj (hc₂.symm.trans hcR')
  rw [e₃] at hi hx
  have hcov_right : Claim.CoveredAt t (some (valLimit g)) x →
      ∃ r', IxVM.Consistency.walkedRole r' = true ∧ Ix.SpecDigest.groupOf r' < g ∧
        t.addressOf? r' = some x := by
    rintro ⟨r', hr', hw', hlt'⟩
    exact ⟨r', hw', Nat.lt_of_lt_of_le (hlt' _ rfl) (valLimit_le g), hr'⟩
  have hi' : i ∈ S0.usedRefIdxs ra.c := by
    rw [hrac, Assembly.usedRefIdxs_eq]
    exact hi
  have hx' : ra.c.refs[i]? = some x := by
    rw [hrac]
    exact hx
  obtain ⟨-, hrest⟩ := (hcl ra hra).2 i hi' x hx'
  by_cases hcov : Claim.CoveredAt t (some (valLimit g)) x
  · exact Or.inr (hcov_right hcov)
  rcases hrest with ⟨hnb, r', hr', hr'x, -⟩ | hcov'
  swap
  · exact absurd hcov' hcov
  left
  -- the record at `x`
  have hxE : IxVM.Consistency.recordOf ρ.E₀ x = some r'.c := by
    rw [← hr'x]
    exact topRec_recordOf hrun.hashedStored r'
  obtain ⟨cx, hcx⟩ := Option.isSome_iff_exists.mp ((hadm.usedClosed.1 a c hcR').2 i hi x hx)
  have hcxE : IxVM.Consistency.recordOf ρ.E₀ x = some cx := recordOf_sub hadm.loaded x cx hcx
  have ecx : cx = r'.c := Option.some.inj (hcxE.symm.trans hxE)
  -- no block
  have hnm : ∀ ms, cx.info ≠ .muts ms := by
    obtain ⟨raw, c'', hhr, hbr, hdr, hnm⟩ := hnb
    have eraw : raw = r'.rawBytes :=
      hrun.runStore.hashed_inj hhr r'.hhashed (hbr.trans (hr'x.symm.trans r'.hblake.symm))
    rw [eraw, r'.hde] at hdr
    have e₄ : r'.c = c'' := Except.ok.inj hdr
    rw [ecx, e₄]
    exact hnm
  -- in Lean's logic, with its block
  have hsafeA : Claim.SourceSafe ρ.E₀ a := by
    intro c' hc'
    rw [hcE] at hc'
    cases hc'
    have ho : Ix.Cert.ownerOf a c = a := by simp [Ix.Cert.ownerOf, hinfo]
    refine ⟨hlogic, fun cb hcb => ?_⟩
    rw [ho, hcE] at hcb
    cases hcb
    exact hlogic
  have hguard : Claim.RecordRefsIn calls t bAddr (some (valLimit g)) a c := by
    have hg := ra.hguard
    rw [hraA, hrac] at hg
    exact hg
  have hsx := Claim.RecordRefsIn.safe hrun.runStore hrun.hashedStored hcE hsafeA hguard i hi x
    (by rw [Array.getElem?_toList]; exact hx) hcov
  obtain ⟨hlx, hox⟩ := hsx cx hcxE
  refine ⟨cx, valLimit g, hcx, hnm, hlx,
    fun cb hcb => hox cb (recordOf_sub hadm.loaded _ cb hcb), ?_⟩
  -- checked at the limit
  have e₅ : ρ.checked = (observedRun calls bAddr t ρ.E₀ ρ.rank).checked :=
    congrArg BRun.checked hρ
  rw [e₅]
  show UnitCheckedAt calls bAddr t ρ.E₀ x (some (valLimit g))
  rcases r'.hchecked with ⟨ms, hms, -⟩ | hc
  · exact (hnm ms (by rw [ecx]; exact hms)).elim
  · left
    rw [← hr'x]
    exact hc

end IxVM.Refinement.Binding

/-! ## The definition's check, with the canonical annotations -/

namespace IxVM.Refinement.Typing

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open IxVM (F)
open IxVM.Refinement.Obs
open IxVM.Consistency

variable {t : Ix.Kernel.RoleTable} {calls : List (Call F)} {E₀ : Ixon.Env}

/-- **`checkedLimAt_defn_step` with the reading and the canonical annotations exposed**: the
walk's check of a standalone definition gives the reading of its type and value over the run's
store, their scoping, the stored terms as the canonical annotations of the reading
(`canonAnn`, the terms every load of the record represents), and the check evidence at the
prefix's keying. -/
theorem checkedLimAt_defn_canon (ht : t.check = .ok ()) (hbound : Bounded calls)
    (hS : LoadedReads.RunStore calls E₀) {bAddr a : _root_.Address}
    {order_role : List _root_.Address} {c : Ixon.Constant} {d : Ixon.Definition}
    (hrec : Ix.Cert.recordAt E₀ a = some c) (hinfo : c.info = .defn d) (hlogic : InLogic c)
    (hkind : d.kind = .defn)
    (hnot_role : a ∉ order_role) {lim : Option Nat} (hchk : Claim.CheckedLimAt calls bAddr t a lim)
    (Ecore : Ixon.Env) {env : Ix.Kernel.Env .anon} (hstored : Decl.UsedRefsStored t env c) :
    ∃ (ty₀ val₀ ty' val' : Ix.Kernel.Expr .anon),
      (exprReader t (fun x => E₀.blobs.get? x) c id (soloSelf t a)).read d.typ = .ok ty₀ ∧
      (exprReader t (fun x => E₀.blobs.get? x) c id (soloSelf t a)).read d.value = .ok val₀ ∧
      ty₀.looseBVarsBounded 0 = true ∧
      ty₀.allLevelParamsDefined (List.range d.lvls.toNat) = true ∧
      val₀.looseBVarsBounded 0 = true ∧
      val₀.allLevelParamsDefined (List.range d.lvls.toNat) = true ∧
      LoadedReads.canonAnn c (List.range d.lvls.toNat) 0 d.typ ty₀ = some ty' ∧
      LoadedReads.canonAnn c (List.range d.lvls.toNat) (0 + 1) d.value val₀ = some val' ∧
      Annotates ty' ty₀ ∧ Annotates val' val₀ ∧
      ∀ hn : Ix.Kernel.ReducibilityHint,
        Decl.CheckedDefnAtLim (Core.Ctx.stored ⟨Ecore, env, t, lim⟩).κ lim calls t
          bAddr Ecore order_role
          (LoadedReads.defnDecl d.kind ⟨Core.keyOf t a, List.range d.lvls.toNat, ty₀⟩ val₀ hn)
          (LoadedReads.defnDecl d.kind ⟨Core.keyOf t a, List.range d.lvls.toNat, ty'⟩ val'
            hn) := by
  have hsafe : Ix.Kernel.Reader.safetyDecline d = none := by
    have hl := hlogic
    unfold InLogic at hl
    rw [hinfo] at hl
    exact hl
  obtain ⟨h_pre, m_chk, h'_chk, rc, ap, ptr, v, r_chk, cs_load, cs_chk,
    hrc_pre, hrc_m, ha_pre, ha_m, ev_ld, hcl_ld, hsub_ld, hld, ev_chk, hcl_chk, hsub_chk⟩ := hchk
  obtain ⟨a', ha'_ref, rfl⟩ := ha_pre
  obtain ⟨rawBytes, c', hh, hba, hex, hres⟩ := L1.get_ci_trace_spec ha'_ref ev_ld
  have hc : c = c' := (hS.record_eq hrec (Core.hashed_mono hsub_ld hh) hba hex).symm
  subst hc
  unfold L1.GetCITraceResult at hres
  rw [hinfo] at hres
  obtain ⟨blobs, tree, v', hhp, built, hld', htr⟩ := hres
  rw [hld] at hld'
  injection hld' with hvv
  subst hvv
  have hblob : ∀ x bs, (x, bs) ∈ blobs → E₀.blobs.get? x = some bs := by
    intro x bs hm
    obtain ⟨hhx, hxa⟩ := hhp (x, bs) hm
    have hhx' : Hashed cs_load bs := hhx
    have hxa' : Address.blake3Pure bs = x := hxa
    have hrun := hS.blobs bs (Core.hashed_mono hsub_ld hhx')
    rw [hxa'] at hrun
    exact hrun
  obtain ⟨raw', ty₀, val₀, hty, hval, hreads, -⟩ :=
    LoadedReads.defn_reading (store := recordOf E₀) (blob := fun x => E₀.blobs.get? x) ht
      (hS.recordOf_of_recordAt hrec) hinfo hlogic hblob htr.toRaw
  obtain ⟨h1, h2, h3, h4⟩ :=
    LoadedReads.checkedDefn_scope_lim ht hbound hkind hsafe hblob raw' hty hval ev_chk
      hsub_chk
  have hrecur : L1.defnRecurAddrs d (Core.ixAddr a') = [] := by
    have hf := (L1.defnIsUnsafeCI_eq_false_iff d).mpr hsafe
    simp [L1.defnRecurAddrs, hf]
  rw [hrecur] at htr
  obtain ⟨hnlvls, tyPtr, valPtr, hint, planT, planV, hv, rty, rval, hpT, hpV, hlT, hlV⟩ := htr
  subst hv
  have hagree : L1.BlobReadAgreement (readCtx t (fun x => E₀.blobs.get? x)).blob blobs :=
    L1.BlobReadAgreement.of_mem hblob
  obtain ⟨ty', hcT, hannT, htmT⟩ :=
    LoadedReads.annotation_canon ht hnlvls hagree rty built hpT hlT hty h1 h2
  obtain ⟨val', hcV, hannV, htmV⟩ :=
    LoadedReads.annotation_canon ht hnlvls hagree rval built hpV hlV hval h3 h4
  have heT : ∀ i, i ∈ exprRefIdxs d.typ → i ∈ usedRefIdxs c := by
    intro i hi
    unfold usedRefIdxs
    rw [hinfo]
    exact List.mem_append_right _ (List.mem_append_left _ hi)
  have heV : ∀ i, i ∈ exprRefIdxs d.value → i ∈ usedRefIdxs c := by
    intro i hi
    unfold usedRefIdxs
    rw [hinfo]
    exact List.mem_append_right _ (List.mem_append_right _ hi)
  have htmT' := Decl.tmC_stored_of_usedRefs (E₀ := Ecore) (lim := lim) rty heT hstored htmT
  have htmV' := Decl.tmC_stored_of_usedRefs (E₀ := Ecore) (lim := lim) rval heV hstored htmV
  refine ⟨ty₀, val₀, ty', val', hty, hval, h1, h2, h3, h4, hcT, hcV, hannT, hannV, fun hn => ?_⟩
  exact LoadedReads.checkedDefn_at_lim (E := Ecore) (order_role := order_role)
    (decl_addr := Core.ixAddr a') hnot_role hkind hsafe hrc_m.toRCRep hnlvls h1 h2 h3 h4 hannT
    hannV htmT' htmV' ev_chk hsub_chk hn

end IxVM.Refinement.Typing

namespace IxVM.Refinement.Binding

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library
open IxVM (F)
open IxVM.Refinement.Core
open Ix.Kernel (Role)
open Ix.Kernel.Semantics (NativeFam)

/-! ## The definition's check at the closure's environment -/

private theorem typesRep_nil' (κ : _root_.Address → KKey) (Γ : Nat → KExpr)
    {m m_pre : Aiur.Heap F}
    (hm : m = m_pre ++
      [.construct IxVM.Refinement.Obs.Names.«Lists::Node<&KernelTypes::KExprNode>» "Nil" []]) :
    TypesRep κ Γ m 0
      (.ptr (.enum IxVM.Refinement.Obs.Names.«Lists::Node<&KernelTypes::KExprNode>»)
        m_pre.length) := by
  rw [hm]
  exact Decl.typesRep_alloc_nil κ Γ m_pre

/-- **The definition's check of an operation's record, from the walk's check at the group's
limit** (`OpRefine.opFront_of_checked` over `Decl.CheckedDefnAtLim`, the form
`Typing.checkedLimAt_defn_canon` gives). -/
theorem opFront_of_checkedLim {calls : List (Call F)} {t : Ix.Kernel.RoleTable}
    {bAddr : _root_.Address} {E : Ixon.Env} {order_role : List _root_.Address} {lim : Nat}
    {env : Ix.Kernel.Env .anon} {d d' : Ix.Kernel.Declaration .anon} {k : KKey}
    {ty₀ val₀ ty val : KExpr} {hn : Ix.Kernel.ReducibilityHint}
    (hinv : Decl.PrefixInv.{u} E t (some lim) env)
    (hchk : Decl.CheckedDefnAtLim (Ctx.stored ⟨E, env, t, some lim⟩).κ (some lim) calls t
      bAddr E order_role d d')
    (hgood : Good ⟨E, env, t, none⟩ calls)
    (hd : d = .defnDecl ⟨k, [], ty₀⟩ val₀ hn) (hd' : d' = .defnDecl ⟨k, [], ty⟩ val hn) :
    RoleOps.OpFront env ty val ty val := by
  cases hchk with
  | @defnDecl a nlvls ty₀' val₀' ty' val' hn' m_pre1 m_es m_es' m_pre2 m_kc m_kc'
      x_rc x_ty x_val v_sort r_kc cs_es cs_kc
      hnot_role _ _ hty_def _ hval_def hty_ann hval_ann hty'_def hval'_def
      hm_es hty_tmc_es hrc_es ev_es _ hsub_es
      _ hm_kc hty_tmc_kc hval_tmc_kc hrc_kc ev_kc _ hsub_kc =>
    simp only [Ix.Kernel.Declaration.defnDecl.injEq, Ix.Kernel.ConstantVal.mk.injEq] at hd hd'
    obtain ⟨⟨-, -, e1⟩, e2, -⟩ := hd
    obtain ⟨⟨-, hl, e3⟩, e4, -⟩ := hd'
    subst e1
    subst e2
    subst e3
    subst e4
    have hn0 : nlvls = 0 := by
      cases nlvls with
      | zero => rfl
      | succ n => exact absurd hl (by simp [List.range_succ])
    subst hn0
    let c : ScopedCtx := Ctx.stored ⟨E, env, t, some lim⟩
    have hgood_c : Good c.toCtx calls := hgood
    obtain ⟨hef, hlf⟩ := hinv.scopedCoreFacts
    have hty_tmc_es' : TmC c.κ m_es ty' x_ty := by
      have h := hty_tmc_es
      rwa [Decl.posOf_range 0 ty'] at h
    have hty_tmc_kc' : TmC c.κ m_kc ty' x_ty := by
      have h := hty_tmc_kc
      rwa [Decl.posOf_range 0 ty'] at h
    have hval_tmc_kc' : TmC c.κ m_kc val' x_val := by
      have h := hval_tmc_kc
      rwa [Decl.posOf_range 0 val'] at h
    obtain ⟨-, hty_nfv, hty_bvs, hty_an⟩ := OpRefine.tmC_props hty_tmc_es'
    obtain ⟨-, hval_nfv, hval_bvs, hval_an⟩ := OpRefine.tmC_props hval_tmc_kc'
    obtain ⟨stype, u', _, hinf_ty, hred_ty, _, _⟩ :=
      Decl.scoped_core_ensure_sort (c := c) hrc_es (typesRep_nil' c.κ _ hm_es)
        (Decl.ghostScoped_zero _) hef hlf
        (CoreGood.ofRaw (hgood_c.sub hsub_es) (fun _ _ => trivial)) ev_es
        (hty_tmc_es' 0 (fun _ => .sort .zero))
    obtain ⟨vtype, hinf_val, hde_val⟩ :=
      Decl.scoped_core_check (c := c) hrc_kc (typesRep_nil' c.κ _ hm_kc)
        (Decl.ghostScoped_zero _) hef hlf
        (CoreGood.ofRaw (hgood_c.sub hsub_kc) (fun _ _ => trivial)) ev_kc
        (hval_tmc_kc' 0 (fun _ => .sort .zero)) (hty_tmc_kc' 0 (fun _ => .sort .zero))
    exact ⟨hty_bvs, hty_nfv, hty_an, hty'_def, ⟨stype, u', hinf_ty, hred_ty⟩,
      hval_bvs, hval_nfv, hval_an, hval'_def, ⟨vtype, hinf_val, hde_val⟩⟩

/-! ## The recurrences and the certificates -/

/-- **What the run's comparison of an operation's recurrences, or check of its certificates,
gives at the closure's environment** (the last part of `validate_op`: `validate_op_equations`):
at a binding run, an operation's group, its admission, the closure's store and environment
with the closure's coverage, a record store for the store after the group the run's calls are
good for, the record (a definition with no universe parameter, in Lean's logic), the reading of
its value and the stored value (its canonical annotation), the record's references stored, and
the prefix half of a well-founded operation's check at the closure's environment
(`RoleOps.WfPrefix`, which `OpRefine.wfPrefix_of_bnd` gives from the invariant below the group):
one comparison per recurrence (`OpRefine.EqObs`) for a structural operation, and one checked
proof per certificate statement (`OpRefine.CertObs`) for a well-founded one. -/
def OpEquationFacts (calls : List (Call F)) : Prop :=
  ∀ (t : Ix.Kernel.RoleTable) (ρ : BRun) (Rs : Nat → Ixon.Env), BindingRun calls t ρ Rs →
    t.check = .ok () →
    ∀ (g : Nat) (r : Role) (a : _root_.Address) (R R₁ R' Ec : Ixon.Env)
      (env₁ : Ix.Kernel.Env .anon) (c : Ixon.Constant) (d : Ixon.Definition) (val₀ val : KExpr),
      6 ≤ g → g < 77 → IxVM.Consistency.roleGroup g = [r] → r ∈ RoleOps.opRoles → t.addressOf? r = some a →
      Admits ρ t g R R' → AdmitsReads ρ t R R' → AddsAt R₁ R' a →
      WalkedStored ρ t (· < g) R₁ env₁ →
      Typing.RecordsFor R' Ec → Typing.StepStore calls t ρ.E₀ Ec →
      Decl.PrefixInv.{u} Ec t (some (valLimit g)) env₁ →
      IxVM.Consistency.recordOf ρ.E₀ a = some c → c.info = .defn d → d.lvls.toNat = 0 →
      IxVM.Consistency.InLogic c →
      (IxVM.Consistency.exprReader t (fun x => ρ.E₀.blobs.get? x) c id
        (IxVM.Consistency.soloSelf t a)).read d.value = .ok val₀ →
      val₀.looseBVarsBounded 0 = true → val₀.allLevelParamsDefined [] = true →
      LoadedReads.canonAnn c [] (0 + 1) d.value val₀ = some val →
      Decl.UsedRefsStored t env₁ c → RoleOps.WfPrefix env₁ (.role r) →
      ((Ix.Kernel.Key.role r : KKey) ∈ Ix.Kernel.natOpNames →
          ∀ eq ∈ Ix.Kernel.natOpEquations 0 (Ix.Kernel.Key.role r : KKey),
            OpRefine.EqObs Ec t (valLimit g) env₁ (.role r) val eq) ∧
      ((Ix.Kernel.Key.role r : KKey) ∈ Ix.Kernel.natDivModNames →
          ∃ proofs : List KExpr, List.Forall₂ (fun st P =>
            P.looseBVarsBounded 0 = true ∧ P.hasFvar = false ∧ Decl.noLetExpr P = true ∧
              P.allLevelParamsDefined [] = true ∧
              OpRefine.CertObs Ec t (valLimit g) env₁ (.role r) val st P)
            (Ix.Kernel.divModCertStmts (Ix.Kernel.Key.role r : KKey)) proofs)

/-! ## The validation facts -/

set_option maxHeartbeats 3200000 in
/-- **`OpValidationFactsW` from the recurrences' and certificates' facts** (module docstring):
the record and its reading, the pin, the definition's check, the reload, from the observed
validation; the recurrences and certificates from `OpEquationFacts`. -/
theorem opValidationFactsW_of_equations (L : Ix.Kernel.Env .anon → NativeFam .anon → Prop)
    (calls : List (Call F)) (heqs : OpEquationFacts.{u} calls) :
    OpValidationFactsW.{u} L calls := by
  intro t ρ Rs hrun hss hall ht g r a R R₁ R' env₁ h6 h77 hgrp hop ha hadm hrd hb hadds hle hws
  have htwf : t.wf = true := wf_of_check ht
  have hrg : r ∈ IxVM.Consistency.roleGroup g := by rw [hgrp]; exact List.mem_singleton.mpr rfl
  have hgr : Ix.SpecDigest.groupOf r = g := OpInstall.groupOf_of_mem_roleGroup hrg
  have hkeya : keyOf t a = Ix.Kernel.Key.role r := keyOf_of_addressOf htwf ha
  have hkeya' : IxVM.Consistency.keyOf t a = Ix.Kernel.Key.role r := hkeya
  obtain ⟨bAddr, tb, -, -, hρ⟩ := hrun.observed
  have hval : RoleVal.ValidateRoleIn calls bAddr t g r := by
    have e : ρ.validated = (observedRun calls bAddr t ρ.E₀ ρ.rank).validated :=
      congrArg BRun.validated hρ
    have h1 := hadm.validated r hrg
    rw [e] at h1
    exact h1
  obtain ⟨a', c, d, ha', hcE, hinfo, hkind, hsafety, hlv0, hpin⟩ :=
    validate_role_op_obs ht hrun.runStore hrun.hashedStored hval hop
  have ea : a' = a := Option.some.inj (ha'.symm.trans ha)
  rw [ea] at hcE hpin
  have hlogic : IxVM.Consistency.InLogic c := by
    unfold IxVM.Consistency.InLogic
    rw [hinfo]
    show Ix.Kernel.Reader.safetyDecline d = none
    unfold Ix.Kernel.Reader.safetyDecline
    rw [hkind, hsafety]
    rfl
  have hcR' : IxVM.Consistency.recordOf R' a = some c := by
    obtain ⟨c₁, hc₁⟩ := Option.isSome_iff_exists.mp
      (hadm.kept r hrg (Or.inl (OpInstall.op_kept hop).1) a ha)
    have h1 := recordOf_sub hadm.loaded a c₁ hc₁
    rw [hcE] at h1
    rw [hc₁, Option.some.inj h1]
  obtain ⟨hchk, hrefs⟩ := op_walk_facts hrun hρ hval hop ha hadm hcE hinfo hlogic hcR'
  have ho : Ix.Cert.ownerOf a c = a := by simp [Ix.Cert.ownerOf, hinfo]
  -- the record is new: the closure's coverage would store the operation
  have hR₁ : IxVM.Consistency.recordOf R₁ a = none := by
    cases h₁ : IxVM.Consistency.recordOf R₁ a with
    | none => rfl
    | some c₁ =>
      exfalso
      have e₁ : c₁ = c := Option.some.inj ((OpInstall.recordOf_up hadds h₁).symm.trans hcR')
      rw [e₁] at h₁
      have hown : ∀ cb, IxVM.Consistency.recordOf R₁ (Ix.Cert.ownerOf a c) = some cb →
          IxVM.Consistency.InLogic cb := by
        intro cb hcb
        rw [ho, h₁] at hcb
        cases hcb
        exact hlogic
      have hchkρ : ρ.checked a (valLimit g) := by
        have e₅ : ρ.checked = (observedRun calls bAddr t ρ.E₀ ρ.rank).checked :=
          congrArg BRun.checked hρ
        rw [e₅]
        exact Or.inl hchk
      have hst := hws.1 a c (valLimit g) h₁ (fun ms h => by rw [hinfo] at h; cases h) hlogic
        hown hchkρ
      rw [hkeya'] at hst
      have hlt : Ix.SpecDigest.groupOf r < g := hb.facts.opsAdmitted r hop hst
      omega
  have hnew : New R R' a := by
    refine ⟨by rw [hcR']; rfl, ?_⟩
    cases h : IxVM.Consistency.recordOf R a with
    | none => rfl
    | some c₀ =>
      exfalso
      have h' := recordOf_sub hle.1 a c₀ h
      rw [hR₁] at h'
      cases h'
  have hunit : RoleUnitAt t g a := ⟨r, hrg, ha, Or.inl hop⟩
  have hstored : Decl.UsedRefsStored t env₁ c :=
    usedRefsStored_of_walkedStored hadm hadds hws hnew hunit hcR' hrefs
  -- a record store for the store after the group
  obtain ⟨Ec, hEc, hst⟩ := hss R' hadm.loaded hadm.loadedBlobs hadm.committed hadm.zeroFree
  have hrecA : Ix.Cert.recordAt ρ.E₀ a = some c := by
    rw [← hrun.runStore.recordOf_eq_recordAt]
    exact hcE
  obtain ⟨ty₀, val₀, ty, val, hty, hvl, h1, h2, h3, h4, hcT, hcV, hannT, hannV, hcheck⟩ :=
    Typing.checkedLimAt_defn_canon (order_role := []) ht hrun.bounded hrun.runStore hrecA hinfo
      hlogic hkind (by simp) hchk Ec hstored
  have hrange : List.range d.lvls.toNat = [] := by rw [hlv0]; rfl
  have hinv : Decl.PrefixInv.{u} Ec t (some (valLimit g)) env₁ :=
    hb.inv (OpInstall.recordsFor_down hadds hEc) (carried_valLimit g) (limWithin_below t g)
  have hgood : Good ⟨Ec, env₁, t, none⟩ calls := hst.good env₁ none
  have hfront : RoleOps.OpFront env₁ ty val ty val :=
    opFront_of_checkedLim (k := Ix.Kernel.Key.role r) (ty₀ := ty₀) (val₀ := val₀) (ty := ty)
      (val := val) (hn := .opaque) hinv (hcheck .opaque) hgood
      (by simp only [LoadedReads.defnDecl, hkind, hrange, hkeya])
      (by simp only [LoadedReads.defnDecl, hkind, hrange, hkeya])
  -- the pin
  have hblobEc : ∀ x b, ρ.E₀.blobs.get? x = some b → Ec.blobs.get? x = some b :=
    fun x b hx => hEc.2.2.1 x b (hrd.blobs x b hx)
  have hcEc : IxVM.Consistency.recordOf Ec a = some c :=
    (Typing.recordOf_eq_recordAt_of_decoded hEc.1 a).trans (hEc.2.1 a c hcR')
  have h2' : ty₀.allLevelParamsDefined [] = true := by rw [hrange] at h2; exact h2
  have h4' : val₀.allLevelParamsDefined [] = true := by rw [hrange] at h4; exact h4
  have hsh : RoleOps.OpTyShape (.role r) ty :=
    hpin Ec env₁ ty₀ val₀ hgood hcEc (ReaderReads.exprReader_mono hblobEc hty)
      (ReaderReads.exprReader_mono hblobEc hvl) h1 h2' h3 h4' ty hannT
  -- the check facts
  have hcV' : LoadedReads.canonAnn c [] (0 + 1) d.value val₀ = some val := by
    rw [hrange] at hcV; exact hcV
  obtain ⟨hstruct, hwf⟩ := heqs t ρ Rs hrun ht g r a R R₁ R' Ec env₁ c d val₀ val h6 h77 hgrp hop
    ha hadm hrd hadds hws hEc hst hinv hcE hinfo hlv0 hlogic hvl h3 h4' hcV' hstored
    (OpRefine.wfPrefix_of_bnd hall hgrp hop hb)
  have hchecked : RoleOps.OpChecked env₁ (.role r) ty val ty val := by
    have hopN : (Ix.Kernel.Key.role r : KKey) ∈ RoleOps.opNames := by
      rw [RoleOps.opNames_eq_map]
      exact List.mem_map.mpr ⟨r, hop, rfl⟩
    rcases RoleOps.mem_opNames.mp hopN with hs | hw
    · exact OpRefine.opChecked_struct hall hgrp hop hs hb hinv hfront hsh (hstruct hs)
    · exact OpRefine.opChecked_wf hall hgrp hop hw hb hinv hfront hsh (hwf hw)
  -- the reading over the store after the group
  have hreads : IxVM.Consistency.Reads t R' a (.defnInfo ⟨.role r, [], ty₀⟩ val₀ .opaque) := by
    refine ⟨c, hcR', ?_⟩
    rw [hinfo]
    show IxVM.Consistency.InLogic c ∧ ∃ ty value,
      (IxVM.Consistency.exprReader t (fun x => R'.blobs.get? x) c id
        (IxVM.Consistency.soloSelf t a)).read d.typ = .ok ty ∧
      (IxVM.Consistency.exprReader t (fun x => R'.blobs.get? x) c id
        (IxVM.Consistency.soloSelf t a)).read d.value = .ok value ∧
      IxVM.Consistency.DefnShape d.kind
        ⟨IxVM.Consistency.keyOf t a, List.range d.lvls.toNat, ty⟩ value
        (.defnInfo ⟨.role r, [], ty₀⟩ val₀ .opaque)
    refine ⟨hlogic, ty₀, val₀, ReaderReads.exprReader_mono hrd.blobs hty,
      ReaderReads.exprReader_mono hrd.blobs hvl, ?_⟩
    rw [hkind, hrange, hkeya']
    show ∃ hint, _ = _
    exact ⟨.opaque, rfl⟩
  refine ⟨ty, val, ty, val, ty₀, val₀, .opaque, hchecked, hannT, hannV, hreads,
    ⟨c, d, hcR', hinfo⟩, Typing.address_size_of_record hrun.runStore hcE, ?_⟩
  -- the reload
  intro E hE
  have hrecE : IxVM.Consistency.recordOf E a = some c :=
    (Typing.recordOf_eq_recordAt_of_decoded hE.1 a).trans (hE.2.1 a c hcR')
  have hbl : ∀ x b, ρ.E₀.blobs.get? x = some b → E.blobs.get? x = some b :=
    fun x b hx => hE.2.2.1 x b (hrd.blobs x b hx)
  have hrl := LoadedReads.reloadsAs_defn_cons ht hrecE hinfo hlogic hbl hty hvl h1 h2 h3 h4
    hstored (LoadedReads.canonDefn_eq (key := IxVM.Consistency.keyOf t a) (hn := .opaque) hcT hcV)
  rw [hkind, hrange, hkeya'] at hrl
  exact hrl

end IxVM.Refinement.Binding
