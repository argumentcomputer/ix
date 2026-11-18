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
