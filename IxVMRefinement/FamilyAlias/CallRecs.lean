import IxVMRefinement.FamilyAlias.CallIotaRule
import IxVMRefinement.FamilyAlias.CallRecRefs
import IxVMRefinement.Assembly.TypingRecLateFamilyKey
import IxVMRefinement.Assembly.TypingRecLateNativeRead
import IxVMRefinement.Assembly.TypingRecParentArm
import IxVMRefinement.Decl.NativeRec
import IxVMRefinement.Callees.ProjAddr
import IxVMRefinement.Obs.KernelCheck8

/-! # Refinement of `KernelModeled::block_elim`, `check_recs`, and `check_rules`

Reads the elimination-level check (`block_elim`) and the recursor loop (`check_recs`,
`check_rules`, `check_rules_go`) out of an observed `KernelModeled::check_family` call:

* `level_is_not_zero_bit` and `block_elim_spec`: `block_elim` loads the block's first inductive
  member `ind0`, returning `bnl = ind0.lvls` and `uo ∈ {0, 1}`;
* `last_binder_dom_rawTm`, `check_carriers_familyKey`, `rec_to_parent_addr_rawTm_full`, and
  `check_recursor_canonical_lvls`: raw-syntax readings of `check_carriers`, `rec_to_parent_addr`,
  and `check_recursor_canonical_at`, establishing `familyKey`, `majorKey`, and
  `rc.lvls ∈ {ind0.lvls, ind0.lvls + 1}` (yielding `ps = LoadedReads.recPs rc ind0`);
* `peel_collect_doms_exact`, `leavesFixed_instSpine_of_noLooseIn`, and `pinsP_leavesFixed`:
  from `peel_collect` + `rename` + `peel_collect` + `spec_params_ptr_eq` and `rec_major_pins` +
  `lower_pins`, proves `LeavesFixed g` on every instantiated major-premise pin;
* `addrIn_rec_major_pins`: carries `AddrIn` back from the lowered major pins to the recursor's
  converted type;
* `rulesTrace_walk`: single-pass walk of `L1.RulesTraceRep` alongside `KernelModeled::check_rules_go`,
  producing the read rules, their canonical annotations (`LoadedReads.canonRules`), their
  constructor-projection hash witnesses, and `RulesFacts` via `CallIotaRule.check_iota_rule_facts`;
* `recMember_of_cons` and `checkRecs_walk`: walk `KernelModeled::check_recs` over `(recAs, recMs)`
  into `RecMemberData` for every recursor, yielding `FamRecCanon`, `MajorRefs`, `RecReads`,
  `MemberFacts`, `RulesFacts`, and `FamRecCompanion`. -/

namespace IxVM.Refinement.Typing.FamilyAlias

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open IxVM.Refinement.Core
open IxVM.Refinement.Decl (SubCalls posRulesJ)
open IxVM.Refinement.KernelLevels (RepKLevel RepKLevelList)
open IxVM.Consistency
open IxVM (F)
open IxVM.Refinement.Decl.FamilyAlias
  (aliasMap MemberFacts MembersFacts RuleFacts RulesFacts RecsFacts RuleCtor majorShape LeavesFixed)
open Ix.Kernel (Expr Level ConstantInfo ConstantVal RecRule LevelParam openPisAtFvars)
open Ix.Kernel.Semantics (NativeFam)

set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

universe u

/-! ## `level_is_not_zero` and `block_elim` -/

private theorem toNat_toUInt64_lt_r {n : Nat} (hn : n < UInt64.size) : n.toUInt64.toNat = n := by
  change (UInt64.ofNat n).toNat = n
  rw [UInt64.toNat_ofNat']
  exact Nat.mod_eq_of_lt hn

private theorem nat_eq_of_field_eq_u32_r {a b : Nat} (ha : a < 4294967296) (hb : b < 4294967296)
    (heq : (a : F) = (b : F)) : a = b := by
  have hmod : Aiur.Library.U32.Goldilocks.modulus = 18446744069414584321 := rfl
  have hv := congrArg ZMod.val heq
  rwa [ZMod.val_natCast_of_lt (by omega), ZMod.val_natCast_of_lt (by omega)] at hv

private theorem nat_eq_of_field_eq_u56_r {a b : Nat} (ha : a < 72057594037927936)
    (hb : b < 72057594037927936) (heq : (a : F) = (b : F)) : a = b := by
  have hmod : Aiur.Library.U32.Goldilocks.modulus = 18446744069414584321 := rfl
  have hv := congrArg ZMod.val heq
  rwa [ZMod.val_natCast_of_lt (by omega), ZMod.val_natCast_of_lt (by omega)] at hv

/-- Every observed `KernelLevels::level_is_not_zero` call returns `.field 0` or `.field 1`. -/
theorem level_is_not_zero_bit {x_l r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (ev : ObsFn Obs.W "KernelLevels::level_is_not_zero" [x_l] h r h' cs) :
    r = .field 0 ∨ r = .field 1 := by
  have hmain : ∀ (fname : String) (args : List (SourceValue F)) (h : Heap F) (r : SourceValue F)
      (h' : Heap F) (cs : List (Call F)),
      ObsFn Obs.W fname args h r h' cs → fname = "KernelLevels::level_is_not_zero" →
      ∀ x_l, args = [x_l] → r = .field 0 ∨ r = .field 1 :=
    ObsFn.strong_induction (world := Obs.W)
      (fun fname args _ r _ _ => fname = "KernelLevels::level_is_not_zero" →
        ∀ x_l, args = [x_l] → r = .field 0 ∨ r = .field 1)
      (fun fname args h r h' cs ev ih hfn x_l hargs => by
        subst hfn hargs
        have d0 := ObsFn.function_inv (s := IxVM.source)
          IxVM.KernelLevels.level_is_not_zero.lookup
          (by simp [IxVM.KernelLevels.level_is_not_zero, ControlLower.hasControl]) ev
        simp only [IxVM.KernelLevels.level_is_not_zero] at d0
        obtain ⟨_, _, _, _, c1, c2, _, sel, dArm, hcM⟩ := d0.matchValue_inv
        -- Arm 1: Zero => 0
        rcases selectArm_cons_inv sel with ⟨_, rfl⟩ | ⟨_, sel⟩
        · obtain ⟨rfl, _, _⟩ := dArm.literal_inv; exact Or.inl rfl
        -- Arm 2: Param(_) => 0
        rcases selectArm_cons_inv sel with ⟨_, rfl⟩ | ⟨_, sel⟩
        · obtain ⟨rfl, _, _⟩ := dArm.literal_inv; exact Or.inl rfl
        -- Arm 3: Succ(_) => 1
        rcases selectArm_cons_inv sel with ⟨_, rfl⟩ | ⟨_, sel⟩
        · obtain ⟨rfl, _, _⟩ := dArm.literal_inv; exact Or.inr rfl
        -- Arm 4: Max(a, b) => match (...) { (0, 0) => 0, _ => 1 }
        rcases selectArm_cons_inv sel with ⟨_, rfl⟩ | ⟨_, sel⟩
        · obtain ⟨_, _, _, _, _, _, _, sel2, dArm2, _⟩ := dArm.matchValue_inv
          rcases selectArm_cons_inv sel2 with ⟨_, rfl⟩ | ⟨_, sel2⟩
          · obtain ⟨rfl, _, _⟩ := dArm2.literal_inv; exact Or.inl rfl
          · rcases selectArm_cons_inv sel2 with ⟨_, rfl⟩ | ⟨_, sel2⟩
            · obtain ⟨rfl, _, _⟩ := dArm2.literal_inv; exact Or.inr rfl
            · exact (selectArm_nil_inv sel2).elim
        -- Arm 5: IMax(_, b) => level_is_not_zero(b)
        rcases selectArm_cons_inv sel with ⟨_, rfl⟩ | ⟨_, sel⟩
        · obtain ⟨vs, _, _, cs', aArgs, evTail, hc⟩ := dArm.call_inv
          rw [instanceName_plain_some] at evTail
          obtain ⟨xb, vs', _, _, _, rfl, _, aNil, hcA⟩ := aArgs.cons_inv
          obtain ⟨rfl, _, hcN⟩ := aNil.nil_inv
          have hlt : cs'.length < cs.length := by
            rw [hcM, hc, hcA, hcN]; simp only [List.length_append, List.length_cons, List.length_nil]
            omega
          exact ih _ _ _ _ _ _ hlt evTail rfl xb rfl
        · exact (selectArm_nil_inv sel).elim)
  exact hmain _ _ _ _ _ _ ev rfl x_l rfl

/-- **`KernelModeled::block_elim`**: loads the block's first inductive member `ind0` and returns
`bnl = .field (ind0.lvls.toNat : F)` and `uo ∈ {.field 0, .field 1}`. -/
theorem block_elim_spec {calls : List (Call F)} {E₀ : Ixon.Env} {B : _root_.Address}
    {cb : Ixon.Constant} {ms : Array Ixon.MutConst}
    (hbd : Bounded calls) (hS : LoadedReads.RunStore calls E₀)
    (hB : FamBlockRecord E₀ B cb ms) (hms_u64 : ms.size < UInt64.size)
    {typeAs : List Bytes.Address} {rc xtA bnl uo : SourceValue F} {h h' : Heap F}
    {cs : List (Call F)}
    (hsub : CallSub cs calls)
    (htypes : typeAs.map ixAddr =
      ms.toList.mapIdx fun i m => projAddr (Specs.Callees.memberProjInfo B i m))
    (htA : RepList addrListEnum (Bytes.RepAddressRef addrTy) h typeAs xtA)
    (ev : ObsFn Obs.W "KernelModeled::block_elim" [rc, xtA] h (.tuple [bnl, uo]) h' cs) :
    ∃ (a0 : Bytes.Address) (restAs : List Bytes.Address) (ind0 : Ixon.Inductive),
      typeAs = a0 :: restAs ∧
      ixAddr a0 = iprjAddr B 0 ∧
      ms[0]? = some (.indc ind0) ∧
      ind0.lvls.toNat < 4294967296 ∧
      bnl = .field (ind0.lvls.toNat : F) ∧
      (uo = .field 0 ∨ uo = .field 1) := by
  match Obs.«KernelModeled::block_elim».obs ev with
  | .run (x_t0 := x_t0) (x_rest := x_rest) (m27 := m27) (p35 := p35) (cs41 := cs41)
      (x_nl := x_nl) (v212 := v212) (ld11 := ld11) (ev43 := ev43) (ld37 := ld37)
      (he213 := he213) (ev232 := ev232) (hc242 := hc) .. =>
    obtain ⟨a0, restAs, rfl, ha0, -⟩ := Lib.rep_cons_of_load htA ld11
    have hms0 : 0 < ms.size := by
      have hlen := congrArg List.length htypes
      simp only [List.length_map, List.length_cons, List.length_mapIdx, Array.length_toList] at hlen
      omega
    have hm0_get : ms[0]? = some ms[0] := Array.getElem?_eq_getElem hms0
    obtain ⟨ind0, hind0⟩ := hB.indcs ms[0] (Array.mem_toList_iff.mpr (Array.getElem_mem hms0))
    have hms0_ind : ms[0]? = some (.indc ind0) := by rwa [hind0] at hm0_get
    have ha0_eq : ixAddr a0 = iprjAddr B 0 := by
      have h0 := congrArg (·[0]?) htypes
      simp only [List.map_cons, List.getElem?_cons_zero, List.getElem?_mapIdx,
        Array.getElem?_toList, hms0_ind, Option.map_some, Option.some.injEq] at h0
      exact h0
    have hsub41 : CallSub cs41 calls := fun cl hcl => hsub cl (by rw [hc]; simp [hcl])
    obtain ⟨_, c0, hh0, hba0, hex0, -, htr0⟩ :=
      L1.get_ci_block_trace_spec (bounded_sub hsub41 hbd) ha0 ev43
    have hrec0 : Ix.Cert.recordAt E₀ (ixAddr a0) = some (memberProjection B 0 (.indc ind0)) := by
      rw [← hS.recordOf_eq_recordAt, ha0_eq, ← LoadedReads.memberAddr_indc]
      exact hB.members 0 (.indc ind0) hms0_ind
    have hc0_eq : c0 = memberProjection B 0 (.indc ind0) :=
      hS.record_eq hrec0 (Core.hashed_mono hsub41 hh0) hba0 hex0
    subst hc0_eq
    unfold L1.GetCIBlockTraceResult at htr0
    simp only [memberProjection] at htr0
    obtain ⟨-, _, cb', ms', ind', _, _, _, v, hhBlk, hbaBlk, hexBlk, hmuts', hmi', -, -, -,
      hldv, hraw, -⟩ := htr0
    have hcb_eq : cb' = cb :=
      hS.record_eq ((hS.recordOf_eq_recordAt B).symm.trans hB.record)
        (Core.hashed_mono hsub41 hhBlk) hbaBlk hexBlk
    subst cb'
    have hms_eq : ms' = ms := Ixon.ConstantInfo.muts.inj (hmuts'.symm.trans hB.muts)
    subst ms'
    have h0_toNat : (0 : Nat).toUInt64.toNat = 0 := rfl
    rw [h0_toNat, Array.getElem?_toList, hms0_ind] at hmi'
    have hind'_eq : ind' = ind0 := Ixon.MutConst.indc.inj (Option.some.inj hmi').symm
    subst ind'
    obtain ⟨hlvls_lt, -, -, -, -, _, _, _, -, -, hv_eq, -⟩ := hraw
    have hv_ld := Except.ok.inj (hldv.symm.trans ld37)
    rw [hv_eq] at hv_ld
    injection hv_ld with _ _ hargs
    injection hargs with hnl_eq _
    injection he213 with htup
    injection htup with hbnl htup
    injection htup with huo _
    refine ⟨a0, restAs, ind0, rfl, ha0_eq, hms0_ind, hlvls_lt, hbnl.trans hnl_eq.symm, ?_⟩
    rw [huo]
    exact level_is_not_zero_bit ev232

/-! ## Raw-syntax readings of `check_carriers`, `rec_to_parent_addr`, and canonical levels -/

/-- `KernelModeled::last_binder_dom` on a raw heap term walks to the last literal `∀` domain
without modifying the heap. -/
theorem last_binder_dom_rawTm {κ : _root_.Address → KKey} {Γ : Nat → KExpr} :
    ∀ {k : Nat} {R E : KExpr} {x r : SourceValue F} {h h' : Heap F} {cs : List (Call F)},
      Decl.RawTm κ 0 Γ h k R E x →
      ObsFn Obs.W "KernelModeled::last_binder_dom" [x] h r h' cs →
      h' = h ∧ ∃ k' Rlast Elast, lastBinderDom R = some Rlast ∧ Decl.RawTm κ 0 Γ h k' Rlast Elast r := by
  have hmain : ∀ (fname : String) (args : List (SourceValue F)) (h : Heap F) (r : SourceValue F)
      (h' : Heap F) (cs : List (Call F)),
      ObsFn Obs.W fname args h r h' cs → fname = "KernelModeled::last_binder_dom" →
      ∀ (x : SourceValue F) (k : Nat) (R E : KExpr),
        args = [x] → Decl.RawTm κ 0 Γ h k R E x →
        h' = h ∧ ∃ k' Rlast Elast, lastBinderDom R = some Rlast ∧
          Decl.RawTm κ 0 Γ h k' Rlast Elast r :=
    ObsFn.strong_induction (world := Obs.W)
      (fun fname args h r h' cs => fname = "KernelModeled::last_binder_dom" →
        ∀ (x : SourceValue F) (k : Nat) (R E : KExpr),
          args = [x] → Decl.RawTm κ 0 Γ h k R E x →
          h' = h ∧ ∃ k' Rlast Elast, lastBinderDom R = some Rlast ∧
            Decl.RawTm κ 0 Γ h k' Rlast Elast r)
      (fun fname args h r h' cs ev ih hfn x k R E hargs hR => by
        subst hfn hargs
        match Obs.«KernelModeled::last_binder_dom».obs ev with
        | .Forall (x_d := xd) (x_b := xb) (cs76 := cs76)
            (ld12 := ld12) (ld47 := ld47) (ev78 := evRec) (hc87 := hc) .. =>
          obtain ⟨Rt, Rb, mR, _, _, _, rfl, -, _, hRb, -⟩ := hR.forallE_of_load ld12
          obtain ⟨Rt2, Rb2, mR2, _, _, _, rfl, -, _, _, -⟩ := hRb.forallE_of_load ld47
          have hlt : cs76.length < cs.length := by rw [hc]; simp
          obtain ⟨hh, k', Rlast, Elast, hlast, hRlast⟩ := ih _ _ _ _ _ _ hlt evRec rfl xb (k + 1) _ _ rfl hRb
          exact ⟨hh, k', Rlast, Elast, by simpa [lastBinderDom] using hlast, hRlast⟩
        | .other (x_d := xd) (x_b := xb) (v36 := v36)
            (ld12 := ld12) (ld47 := ld47) (hne88 := hne) (he93 := hr) (he94 := hh) .. =>
          subst hr hh
          obtain ⟨Rt, Rb, mR, T, _, _, rfl, -, hRt, hRb, -⟩ := hR.forallE_of_load ld12
          have hnotForall : ¬ Typing.IsForall Rb := by
            rintro ⟨d', b', m', rfl⟩
            cases hRb with
            | forallE cell _ _ _ =>
              rw [loadValue_enum_cell cell] at ld47
              exact hne [_, _, _] rfl (Except.ok.inj ld47).symm
          exact ⟨rfl, k, Rt, T, Typing.lastBinderDom_forallE_of_not hnotForall, hRt⟩)
  intro k R E x r h h' cs hR ev
  exact hmain _ _ _ _ _ _ ev rfl x k R E rfl hR

/-- `RawShape` preserves `familyKey`. -/
theorem familyKey_eq_of_rawShape {rc : Ixon.Recursor} {a b : KExpr} (h : RawShape a b) :
    familyKey rc a = familyKey rc b := by
  have hk := Typing.KeyShape.of_rawShape h
  unfold familyKey binderDom
  rcases Typing.keyShape_stripPis rc.params.toNat hk with ⟨h1, h2⟩ | ⟨_, body, _, body', h1, h2, h3⟩
  · rw [h1, h2]
  · rw [h1, h2]
    cases h3 with
    | forallE ht _ =>
      dsimp only [Option.bind]
      cases hl : lastBinderDom _ with
      | none =>
        cases hl' : lastBinderDom _ with
        | none => rfl
        | some d' =>
          obtain ⟨d, hd, _⟩ := Typing.lastBinderDom_keyShape ht.symm hl'
          rw [hl] at hd; cases hd
      | some d =>
        obtain ⟨d', hd', hdd'⟩ := Typing.lastBinderDom_keyShape ht hl
        rw [hd']
        exact Typing.headKey_eq_of_keyShape hdd'
    | bvar | fvar | sort | const | lit | app | lam | letE | proj => rfl

/-- **`KernelModeled::check_carriers`** on a raw heap term proves
`familyKey rc tyP = some (Core.keyOf t (iprjAddr B 0))`. -/
theorem check_carriers_familyKey {t : Ix.Kernel.RoleTable} {rc : Ixon.Recursor}
    {B : _root_.Address} {a0 : Bytes.Address} {restAs : List Bytes.Address}
    {tyP R E : KExpr} {x_ty xtA r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (hnp_lt : rc.params.toNat < 72057594037927936)
    (hshape : RawShape tyP R)
    (hR : Decl.RawTm (Core.keyOf t) 0 zeroGhost h 0 R E x_ty)
    (htA : RepList addrListEnum (Bytes.RepAddressRef addrTy) h (a0 :: restAs) xtA)
    (ha0 : ixAddr a0 = iprjAddr B 0)
    (ev : ObsFn Obs.W "KernelModeled::check_carriers" [x_ty, .field (rc.params.toNat : F), xtA]
      h r h' cs) :
    familyKey rc tyP = some (Core.keyOf t (iprjAddr B 0)) := by
  have hmod : Aiur.Library.U32.Goldilocks.modulus = 18446744069414584321 := rfl
  have hnp_val : ZMod.val (rc.params.toNat : F) = rc.params.toNat := SubstAux.val_natCast (by omega)
  match Obs.«KernelModeled::check_carriers».obs ev with
  | .run (ev20 := evPeel) (ev6 := evGo) .. =>
    obtain ⟨hh, rbs, rbody, ebody, hstrip, hbody⟩ :=
      Typing.peel_n_foralls_rawTm_val rc.params.toNat hnp_val hR evPeel
    subst hh
    match Obs.«KernelModeled::check_carriers_go».obs evGo with
    | .Nil (ld12 := ldNil) .. =>
      exact absurd (Lib.rep_nil_of_load htA ldNil) (List.cons_ne_nil _ _)
    | .Cons (x_t := x_t) (x_mdom := x_mdom) (x_head := x_head) (x_c := x_c) (v91 := v91)
        (m78 := m78) (m93 := m93) (ld12 := ld12) (ld53 := ld53) (ev103 := evLast)
        (ev90 := evSp) (ld137 := ld137) (ev180 := evEq) (heq203 := heq1) .. =>
      subst heq1
      obtain ⟨a0', _, hcons, ha0_ref, -⟩ := Lib.rep_cons_of_load htA ld12
      injection hcons with ha_eq _; subst ha_eq
      obtain ⟨Rd, Rb, mR, _, _, _, rfl, -, hRd, -, -⟩ := hbody.forallE_of_load ld53
      obtain ⟨hhLast, _, Rlast, Elast, hlast, hRlast⟩ := last_binder_dom_rawTm hRd evLast
      subst hhLast
      obtain ⟨hd, sp, Rh, Eh, Ras, Eas, htup, hRh, -, -, hRlast_eq, -, -⟩ :=
        Decl.collect_spine_rawTm_spec hRlast evSp
      injection htup with h1; injection h1 with hhd h1; injection h1 with hsp _; subst hhd hsp
      have hconst : ∃ ac us, Rh = .const (Core.keyOf t (ixAddr ac)) us ∧
          Bytes.RepAddressRef addrTy m78 ac x_c := by
        cases hRh with
        | const cell rac _ _ =>
          obtain ⟨-, hxs⟩ := load_cell cell ld137
          injection hxs with hcx _
          subst hcx
          exact ⟨_, _, rfl, rac⟩
        | bvarLocal cell _ _ | bvarFree cell _ _ _ | sort cell _ _ | app cell _ _ | lam cell _ _ _
        | forallE cell _ _ _ | letE cell _ _ _ | litNat cell _ _ | litStr cell _ _
        | proj cell _ _ =>
          exact (load_cell_ne cell ld137 (by decide)).elim
      obtain ⟨ac, us, rfl, hrac⟩ := hconst
      have ha0_m78 := Bytes.repAddressRef_heapMono₂ addrTy evSp.heap_extends ha0_ref
      have hbeq := (Lib.address_eq_spec evEq hrac ha0_m78).1
      have hac_eq : ac = a0 := by
        by_contra hne
        rw [ite_eq_right_iff.mpr fun hc => absurd hc hne] at hbeq
        exact absurd (Value.field.inj hbeq) one_ne_zero
      subst hac_eq
      have hhead : headKey Rlast = some (Core.keyOf t (iprjAddr B 0)) := by
        unfold headKey
        rw [hRlast_eq, Decl.getAppFn_mkAppN, ha0]; rfl
      have hfamR : familyKey rc R = some (Core.keyOf t (iprjAddr B 0)) := by
        unfold familyKey binderDom
        rw [hstrip]
        simp only [Option.bind_some]
        rw [hlast]
        exact hhead
      exact (familyKey_eq_of_rawShape hshape).trans hfamR

/-- **`KernelCheck::rec_to_parent_addr`** on a raw heap term: returns both the address witness
`Bytes.RepAddressRef` and `majorKey rc tyP = some (Core.keyOf t (ixAddr a_par))`. -/
theorem rec_to_parent_addr_rawTm_full {t : Ix.Kernel.RoleTable} {rc : Ixon.Recursor}
    {tyP R E : KExpr} {x_ty r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (hp_lt : rc.params.toNat < 72057594037927936)
    (hm_lt : rc.motives.toNat < 72057594037927936)
    (hmi_lt : rc.minors.toNat < 72057594037927936)
    (hi_lt : rc.indices.toNat < 72057594037927936)
    (hshape : RawShape tyP R)
    (hR : Decl.RawTm (Core.keyOf t) 0 zeroGhost h 0 R E x_ty)
    (ev : ObsFn Obs.W "KernelCheck::rec_to_parent_addr"
      [x_ty, .field (rc.params.toNat : F), .field (rc.motives.toNat : F),
        .field (rc.minors.toNat : F), .field (rc.indices.toNat : F)] h r h' cs) :
    ∃ a_par : Bytes.Address,
      Bytes.RepAddressRef addrTy h' a_par r ∧
      majorKey rc tyP = some (Core.keyOf t (ixAddr a_par)) := by
  have hmod : Aiur.Library.U32.Goldilocks.modulus = 18446744069414584321 := rfl
  obtain ⟨v1, x9, x17, v37, m38, cs48, x_major_ty, w86, w87, m104, cs115, x_head, w132, x_caddr,
    w162, op32, op24, op16, ev50, ld78, ev117, ld154, hr_eq, hh_eq, _⟩ :=
    Obs.«KernelCheck::rec_to_parent_addr».obs ev
  subst hr_eq hh_eq
  have hx17 : x17 = .field ((rc.params.toNat : F) + (rc.motives.toNat : F)) := by
    simp only [evalBinOp, Except.ok.injEq] at op32; exact op32.symm
  subst hx17
  have hx9 : x9 = .field ((rc.params.toNat : F) + (rc.motives.toNat : F) + (rc.minors.toNat : F)) := by
    simp only [evalBinOp, Except.ok.injEq] at op24; exact op24.symm
  subst hx9
  have hv1 : v1 = .field ((rc.params.toNat : F) + (rc.motives.toNat : F) +
      (rc.minors.toNat : F) + (rc.indices.toNat : F)) := by
    simp only [evalBinOp, Except.ok.injEq] at op16; exact op16.symm
  subst hv1
  have hsum : ZMod.val ((rc.params.toNat : F) + (rc.motives.toNat : F) +
      (rc.minors.toNat : F) + (rc.indices.toNat : F)) =
      rc.params.toNat + rc.motives.toNat + rc.minors.toNat + rc.indices.toNat := by
    rw [← Nat.cast_add, ← Nat.cast_add, ← Nat.cast_add]
    exact SubstAux.val_natCast (by omega)
  obtain ⟨hheap, rbs, rbody, ebody, hstrip, hbody⟩ :=
    Typing.peel_n_foralls_rawTm_val _ hsum hR ev50
  subst hheap
  obtain ⟨Rt, Rb, mR, _, _, _, rfl, -, hRt, -, -⟩ := hbody.forallE_of_load ld78
  obtain ⟨hd, sp, Rh, Eh, Ras, Eas, htup, hRh, -, -, hRt_eq, -, -⟩ :=
    Decl.collect_spine_rawTm_spec hRt ev117
  injection htup with h1; injection h1 with hhd h1; injection h1 with hsp _; subst hhd hsp
  have hconst : ∃ a us, Rh = .const (Core.keyOf t (ixAddr a)) us ∧
      Bytes.RepAddressRef addrTy h' a r := by
    cases hRh with
    | const cell ra _ _ =>
      obtain ⟨-, hxs⟩ := load_cell cell ld154
      injection hxs with hcx _
      subst hcx
      exact ⟨_, _, rfl, ra⟩
    | bvarLocal cell _ _ | bvarFree cell _ _ _ | sort cell _ _ | app cell _ _ | lam cell _ _ _
    | forallE cell _ _ _ | letE cell _ _ _ | litNat cell _ _ | litStr cell _ _
    | proj cell _ _ =>
      exact (load_cell_ne cell ld154 (by decide)).elim
  obtain ⟨a_par, us, rfl, hra⟩ := hconst
  have hmajR : majorKey rc R = some (Core.keyOf t (ixAddr a_par)) := by
    unfold majorKey binderDom headKey
    rw [hstrip]
    simp only [Option.bind_some]
    rw [hRt_eq, Decl.getAppFn_mkAppN]
    rfl
  exact ⟨a_par, hra, (Typing.majorKey_eq_of_rawShape (rc := rc) hshape).trans hmajR⟩

/-- **`KernelCheck::check_recursor_canonical_at`** at an `Induct` parent constrains the recursor's
level count to `bnl` or `bnl + 1`. -/
theorem check_recursor_canonical_lvls
    {rc ty np ni n nmin rules kf uf blk idx x parAddr uo form form' : SourceValue F}
    {p1 p2 p3 p4 p5 p6 p7 p8 : SourceValue F}
    {nlvls bnl : Nat} {h h' : Heap F} {cs : List (Call F)}
    (hnl_lt : nlvls < 4294967296) (hbnl_lt : bnl < 4294967296)
    (huo : uo = .field 0 ∨ uo = .field 1)
    (ev : ObsFn Obs.W "KernelCheck::check_recursor_canonical_at"
      [rc, .construct "KernelTypes::KConstantInfo" "Rec"
        [.field (nlvls : F), ty, np, ni, n, nmin, rules, kf, uf, blk, idx],
        x, .construct "KernelTypes::KConstantInfo" "Induct" [p1, p2, p3, p4, p5, p6, p7, p8],
        parAddr, uo, .field (bnl : F), form] h form' h' cs) :
    nlvls = bnl ∨ nlvls = bnl + 1 := by
  have hmod : Aiur.Library.U32.Goldilocks.modulus = 18446744069414584321 := rfl
  have handle : ∀ (v141 : SourceValue F),
      evalBinOp .add (.field (bnl : F)) uo = .ok v141 →
      (.field (nlvls : F) : SourceValue F) = v141 →
      nlvls = bnl ∨ nlvls = bnl + 1 := by
    intro v141 hop heq
    rcases huo with rfl | rfl
    · left
      rw [SubstAux.add_ok hop, add_zero] at heq
      exact nat_eq_of_field_eq_u32_r hnl_lt hbnl_lt (Value.field.inj heq)
    · right
      rw [SubstAux.add_ok hop] at heq
      have hcast : ((bnl : F) + 1) = ((bnl + 1 : Nat) : F) := by push_cast; rfl
      rw [hcast] at heq
      have hv := congrArg ZMod.val (Value.field.inj heq)
      rwa [SubstAux.val_natCast (by omega), SubstAux.val_natCast (by omega)] at hv
  match Obs.«KernelCheck::check_recursor_canonical_at».obs ev with
  | .Induct_n1_bind (hv15 := hv15) (op162 := op162) (heq165 := heq165) .. =>
    injection hv15 with _ _ hargs; injection hargs with hnl _; subst hnl
    exact handle _ op162 heq165
  | .Induct_other (hv15 := hv15) (op162 := op162) (heq165 := heq165) .. =>
    injection hv15 with _ _ hargs; injection hargs with hnl _; subst hnl
    exact handle _ op162 heq165
  | .other (hne944 := hne) .. =>
    exact (hne [p1, p2, p3, p4, p5, p6, p7, p8] rfl rfl).elim

/-! ## `LeavesFixed` for major-premise pins (`peel_collect`, `spec_params_ptr_eq`, `lower_pins`) -/

/-- At depth `0`, `Decl.TmExact` is monotone in its bound-variable limit `k`. -/
theorem tmExact_weaken_k {κ : _root_.Address → KKey} {Γ : Nat → KExpr} {h : Heap F}
    {k k' : Nat} {E : KExpr} {p : SourceValue F}
    (hle : k ≤ k') (rep : Decl.TmExact κ 0 Γ h k E p) :
    Decl.TmExact κ 0 Γ h k' E p := by
  induction rep generalizing k' with
  | bvarLocal cell hs hi => exact .bvarLocal cell hs (Nat.lt_of_lt_of_le hi hle)
  | bvarFree _ _ _ hd => exact absurd hd (Nat.not_lt_zero _)
  | sort cell rl => exact .sort cell rl
  | const cell ra rls => exact .const cell ra rls
  | app cell _ _ ihf iha => exact .app cell (ihf hle) (iha hle)
  | lam cell _ _ rl iht ihb => exact .lam cell (iht hle) (ihb (Nat.add_le_add_right hle 1)) rl
  | forallE cell _ _ rl iht ihb =>
    exact .forallE cell (iht hle) (ihb (Nat.add_le_add_right hle 1)) rl
  | letE cell _ _ _ iht ihv ihb =>
    exact .letE cell (iht hle) (ihv hle) (ihb (Nat.add_le_add_right hle 1))
  | litNat cell rl hc => exact .litNat cell rl hc
  | litStr cell rb hs => exact .litStr cell rb hs
  | proj cell ra _ ihe => exact .proj cell ra (ihe hle)

/-- `KernelModeled::peel_collect` at depth `0` collects the raw domains of the first `m` literal
`∀` binders in reverse order, represented at bound-variable depth `k + m`. -/
theorem peel_collect_doms_exact (m : Nat) :
    ∀ {κ : _root_.Address → KKey} {Γ : Nat → KExpr} {k : Nat} {E : KExpr}
      {accEs : List KExpr} {e acc r_e r_acc : SourceValue F} {n : F} {h h' : Heap F}
      {cs : List (Call F)},
      ZMod.val n = m →
      ObsFn Obs.W "KernelModeled::peel_collect" [e, .field n, acc] h (.tuple [r_e, r_acc]) h' cs →
      Decl.TmExact κ 0 Γ h k E e →
      RepList kexprListEnum (fun h D p => Decl.TmExact κ 0 Γ h (k + m) D p) h accEs acc →
      ∃ bs rem,
        E.stripPis m = some (bs, rem) ∧
        RepList kexprListEnum (fun h D p => Decl.TmExact κ 0 Γ h (k + m) D p) h'
          (bs.reverse.map Prod.fst ++ accEs) r_acc := by
  induction m with
  | zero =>
    intro κ Γ k E accEs e acc r_e r_acc n h h' cs hn ev hE hacc
    match Obs.«KernelModeled::peel_collect».obs ev with
    | .n0 (he19 := hr) (he34 := hh) .. =>
      subst hh
      injection hr with hl; injection hl with _ hl; injection hl with h2 _; subst h2
      exact ⟨[], E, rfl, by simpa using hacc⟩
    | .other (hne36 := hne) .. =>
      have := Lib.val_sub_one (fun (e : n = 0) => hne (by rw [e])); omega
  | succ m ih =>
    intro κ Γ k E accEs e acc r_e r_acc n h h' cs hn ev hE hacc
    match Obs.«KernelModeled::peel_collect».obs ev with
    | .n0 (hv14 := hv) .. => injection hv with h0; subst h0; simp at hn
    | .other (x_d := xd) (x_b := xb) (m107 := m107) (hne36 := hne) (ld51 := ld)
        (op104 := opSub) (hm115 := hm107) (ev80 := evRec) .. =>
      subst hm107
      obtain rfl := Lib.sub_one_inv opSub
      have hpred := Lib.val_sub_one (fun (e : n = 0) => hne (by rw [e]))
      obtain ⟨T, B, ℓ, rfl, hT, hB, _⟩ := hE.forallE_of_load ld
      have ext := Heap.Extends.snoc h (.construct kexprListEnum "Cons" [xd, acc])
      have hT' : Decl.TmExact κ 0 Γ (h ++ [.construct kexprListEnum "Cons" [xd, acc]])
          (k + 1 + m) T xd :=
        tmExact_weaken_k (by omega) (hT.mono ext)
      have hacc' : RepList kexprListEnum (fun h D p => Decl.TmExact κ 0 Γ h (k + 1 + m) D p)
          (h ++ [.construct kexprListEnum "Cons" [xd, acc]]) (T :: accEs)
          (.ptr (.enum kexprListEnum) h.length) := by
        rw [show k + 1 + m = k + (m + 1) by omega] at hT' ⊢
        exact .cons (by simp) hT'
          (RepLinkedList.mono (fun _ _ _ _ e x => x.mono e) ext hacc)
      obtain ⟨bs, rem, hstrip, hrep⟩ := ih (k := k + 1) (n := n - 1) (by omega) evRec
        (hB.mono ext) hacc'
      rw [show k + 1 + m = k + (m + 1) by omega] at hrep
      refine ⟨(T, bmeta ℓ) :: bs, rem, by simp [Expr.stripPis, hstrip], ?_⟩
      simpa [List.reverse_cons, List.map_append, List.append_assoc] using hrep

private theorem stripPis_instantiate1_doms_fixed {g : KKey → KKey} {v : KExpr}
    (hv : v.renameConsts g = v) :
    ∀ (m : Nat) (e : KExpr) (c : Nat) {bs : List (KExpr × Ix.Kernel.BinderMeta)} {rem : KExpr},
      e.stripPis m = some (bs, rem) →
      (∀ d ∈ bs.map Prod.fst, d.renameConsts g = d) →
      ∃ bs' rem', (e.instantiate1 v c).stripPis m = some (bs', rem') ∧
        ∀ d ∈ bs'.map Prod.fst, d.renameConsts g = d
  | 0, e, c, _, _, _, _ => ⟨[], e.instantiate1 v c, rfl, fun _ h => nomatch h⟩
  | m + 1, .forallE T B bm, c, bs, rem, hs, hfix => by
    simp only [Expr.stripPis] at hs
    cases hsb : B.stripPis m with
    | none => simp [hsb] at hs
    | some p =>
      rw [hsb] at hs; injection hs with hp; injection hp with hbs _; subst hbs
      have hT : T.renameConsts g = T := hfix T (by simp)
      have hrest : ∀ d ∈ p.1.map Prod.fst, d.renameConsts g = d :=
        fun d hd => hfix d (by simp [hd])
      obtain ⟨bs', rem', hs', hfix'⟩ := stripPis_instantiate1_doms_fixed hv m B (c + 1) hsb hrest
      refine ⟨(T.instantiate1 v c, bm) :: bs', rem', by simp [Expr.instantiate1, Expr.stripPis, hs'], ?_⟩
      intro d hd
      simp only [List.map_cons, List.mem_cons] at hd
      rcases hd with rfl | hd'
      · rw [Ix.Kernel.Expr.renameConsts_instantiate1_gen, hT, hv]
      · exact hfix' d hd'
  | _ + 1, .bvar _, _, _, _, hs, _ | _ + 1, .fvar _ _, _, _, _, hs, _
  | _ + 1, .sort _, _, _, _, hs, _ | _ + 1, .const _ _, _, _, _, hs, _
  | _ + 1, .app _ _, _, _, _, hs, _ | _ + 1, .lam _ _ _, _, _, _, hs, _
  | _ + 1, .letE _ _ _ _, _, _, _, hs, _ | _ + 1, .lit _, _, _, _, hs, _
  | _ + 1, .proj _ _ _, _, _, _, hs, _ => nomatch hs

private theorem openPisAtFvars_fixed_of_doms_fixed {g : KKey → KKey} :
    ∀ (m : Nat) (e : KExpr) (i : Nat) {bs : List (KExpr × Ix.Kernel.BinderMeta)} {rem rem' : KExpr}
      {fvs : List KExpr},
      e.stripPis m = some (bs, rem) →
      (∀ d ∈ bs.map Prod.fst, d.renameConsts g = d) →
      openPisAtFvars m e i = some (fvs, rem') →
      ∀ fv ∈ fvs, fv.renameConsts g = fv
  | 0, _, _, _, _, _, _, _, _, hop, _, hfv => by
    injection hop with hp; injection hp with hf _; subst hf; exact nomatch hfv
  | m + 1, .forallE T B bm, i, _, _, _, _, hs, hfix, hop, fv, hfv => by
    simp only [Expr.stripPis] at hs
    cases hsb : B.stripPis m with
    | none => simp [hsb] at hs
    | some p =>
      rw [hsb] at hs; injection hs with hp; injection hp with hbs _; subst hbs
      simp only [openPisAtFvars] at hop
      cases hopb : openPisAtFvars m (B.instantiate1 (.fvar i T)) (i + 1) with
      | none => simp [hopb] at hop
      | some q =>
        rw [hopb] at hop; injection hop with hp; injection hp with hf _; subst hf
        have hT : T.renameConsts g = T := hfix T (by simp)
        have hfv0 : (Expr.fvar i T).renameConsts g = .fvar i T := by simp [Expr.renameConsts, hT]
        rcases List.mem_cons.mp hfv with rfl | hfv'
        · exact hfv0
        · obtain ⟨bs', rem', hs', hfix'⟩ :=
            stripPis_instantiate1_doms_fixed hfv0 m B 0 hsb (fun d hd => hfix d (by simp [hd]))
          exact openPisAtFvars_fixed_of_doms_fixed m _ (i + 1) hs' hfix' hopb fv hfv'
  | _ + 1, .bvar _, _, _, _, _, _, hs, _, _, _, _ | _ + 1, .fvar _ _, _, _, _, _, _, hs, _, _, _, _
  | _ + 1, .sort _, _, _, _, _, _, hs, _, _, _, _ | _ + 1, .const _ _, _, _, _, _, _, hs, _, _, _, _
  | _ + 1, .app _ _, _, _, _, _, _, hs, _, _, _, _ | _ + 1, .lam _ _ _, _, _, _, _, _, hs, _, _, _, _
  | _ + 1, .letE _ _ _ _, _, _, _, _, _, hs, _, _, _, _ | _ + 1, .lit _, _, _, _, _, _, hs, _, _, _, _
  | _ + 1, .proj _ _ _, _, _, _, _, _, hs, _, _, _, _ => nomatch hs

private theorem noLooseIn_of_lbb0 :
    ∀ (e : KExpr) (c k : Nat), e.looseBVarsBounded 0 = true → Decl.noLooseIn c k e = true
  | .bvar i, _, _, h => by simp [Expr.looseBVarsBounded] at h
  | .fvar _ _, _, _, _ | .sort _, _, _, _ | .const _ _, _, _, _ | .lit _, _, _, _ => rfl
  | .app f a, c, k, h => by
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at h
    simp [Decl.noLooseIn, noLooseIn_of_lbb0 f c k h.1, noLooseIn_of_lbb0 a c k h.2]
  | .lam ty b _, c, k, h | .forallE ty b _, c, k, h => by
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at h
    -- Under 1 binder, loose bvars are < 1, which is < c + 1
    have hsub : ∀ (e' : KExpr) (d lo n : Nat), d ≤ lo → e'.looseBVarsBounded d = true →
        Decl.noLooseIn lo n e' = true := by
      intro e'
      induction e' with
      | bvar i =>
        intro d lo n hle hlbb
        simp only [Expr.looseBVarsBounded, decide_eq_true_eq] at hlbb
        simp only [Decl.noLooseIn, decide_eq_true_eq]
        exact Or.inl (by omega)
      | fvar _ _ | sort _ | const _ _ | lit _ => intro _ _ _ _ _; rfl
      | app f a ihf iha =>
        intro d lo n hle hlbb
        simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hlbb
        simp [Decl.noLooseIn, ihf d lo n hle hlbb.1, iha d lo n hle hlbb.2]
      | lam t bo _ iht ihb | forallE t bo _ iht ihb =>
        intro d lo n hle hlbb
        simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hlbb
        simp [Decl.noLooseIn, iht d lo n hle hlbb.1, ihb (d + 1) (lo + 1) n (by omega) hlbb.2]
      | letE t v bo _ iht ihv ihb =>
        intro d lo n hle hlbb
        simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hlbb
        simp [Decl.noLooseIn, iht d lo n hle hlbb.1.1, ihv d lo n hle hlbb.1.2,
          ihb (d + 1) (lo + 1) n (by omega) hlbb.2]
      | proj _ _ e' ihe =>
        intro d lo n hle hlbb
        exact ihe d lo n hle hlbb
    simp [Decl.noLooseIn, hsub ty 0 c k (Nat.zero_le _) h.1,
      hsub b 1 (c + 1) k (by omega) h.2]
  | .letE ty v b _, c, k, h => by
    have hsub : ∀ (e' : KExpr) (d lo n : Nat), d ≤ lo → e'.looseBVarsBounded d = true →
        Decl.noLooseIn lo n e' = true := by
      intro e'
      induction e' with
      | bvar i =>
        intro d lo n hle hlbb
        simp only [Expr.looseBVarsBounded, decide_eq_true_eq] at hlbb
        simp only [Decl.noLooseIn, decide_eq_true_eq]
        exact Or.inl (by omega)
      | fvar _ _ | sort _ | const _ _ | lit _ => intro _ _ _ _ _; rfl
      | app f a ihf iha =>
        intro d lo n hle hlbb
        simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hlbb
        simp [Decl.noLooseIn, ihf d lo n hle hlbb.1, iha d lo n hle hlbb.2]
      | lam t bo _ iht ihb | forallE t bo _ iht ihb =>
        intro d lo n hle hlbb
        simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hlbb
        simp [Decl.noLooseIn, iht d lo n hle hlbb.1, ihb (d + 1) (lo + 1) n (by omega) hlbb.2]
      | letE t v bo _ iht ihv ihb =>
        intro d lo n hle hlbb
        simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hlbb
        simp [Decl.noLooseIn, iht d lo n hle hlbb.1.1, ihv d lo n hle hlbb.1.2,
          ihb (d + 1) (lo + 1) n (by omega) hlbb.2]
      | proj _ _ e' ihe =>
        intro d lo n hle hlbb
        exact ihe d lo n hle hlbb
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at h
    simp [Decl.noLooseIn, hsub ty 0 c k (Nat.zero_le _) h.1.1,
      hsub v 0 c k (Nat.zero_le _) h.1.2, hsub b 1 (c + 1) k (by omega) h.2]
  | .proj _ _ e, c, k, h => noLooseIn_of_lbb0 e c k h

private theorem noLooseIn_instantiate1_ge {a : KExpr} (ha : a.looseBVarsBounded 0 = true) :
    ∀ (e : KExpr) (c k t : Nat), c + k ≤ t → Decl.noLooseIn c k e = true →
      Decl.noLooseIn c k (e.instantiate1 a t) = true
  | .bvar i, c, k, t, hle, hno => by
    simp only [Decl.noLooseIn, decide_eq_true_eq] at hno
    simp only [Expr.instantiate1]
    split
    · exact noLooseIn_of_lbb0 a c k ha
    · split
      · simp only [Decl.noLooseIn, decide_eq_true_eq]; exact Or.inr (by omega)
      · simp only [Decl.noLooseIn, decide_eq_true_eq]; exact hno
  | .fvar _ _, _, _, _, _, _ | .sort _, _, _, _, _, _ | .const _ _, _, _, _, _, _
  | .lit _, _, _, _, _, _ => rfl
  | .app f x, c, k, t, hle, hno => by
    simp only [Decl.noLooseIn, Bool.and_eq_true] at hno
    simp [Expr.instantiate1, Decl.noLooseIn,
      noLooseIn_instantiate1_ge ha f c k t hle hno.1,
      noLooseIn_instantiate1_ge ha x c k t hle hno.2]
  | .lam ty b _, c, k, t, hle, hno | .forallE ty b _, c, k, t, hle, hno => by
    simp only [Decl.noLooseIn, Bool.and_eq_true] at hno
    simp [Expr.instantiate1, Decl.noLooseIn,
      noLooseIn_instantiate1_ge ha ty c k t hle hno.1,
      noLooseIn_instantiate1_ge ha b (c + 1) k (t + 1) (by omega) hno.2]
  | .letE ty v b _, c, k, t, hle, hno => by
    simp only [Decl.noLooseIn, Bool.and_eq_true] at hno
    simp [Expr.instantiate1, Decl.noLooseIn,
      noLooseIn_instantiate1_ge ha ty c k t hle hno.1.1,
      noLooseIn_instantiate1_ge ha v c k t hle hno.1.2,
      noLooseIn_instantiate1_ge ha b (c + 1) k (t + 1) (by omega) hno.2]
  | .proj _ _ e, c, k, t, hle, hno => by
    simp [Expr.instantiate1, Decl.noLooseIn, noLooseIn_instantiate1_ge ha e c k t hle hno]

private theorem fvarLeaves_instantiate1_of_noLooseIn (a : KExpr) :
    ∀ (e : KExpr) (c k : Nat), Decl.noLooseIn c (k + 1) e = true →
      (e.instantiate1 a (c + k)).fvarLeaves = e.fvarLeaves ∧
      Decl.noLooseIn c k (e.instantiate1 a (c + k)) = true
  | .bvar i, c, k, hno => by
    simp only [Decl.noLooseIn, decide_eq_true_eq] at hno
    simp only [Expr.instantiate1]
    have hne : i ≠ c + k := by omega
    rw [ite_eq_right_iff.mpr fun hc => absurd hc hne]
    split
    · exact ⟨by simp [Expr.fvarLeaves], by simp only [Decl.noLooseIn, decide_eq_true_eq]; exact Or.inr (by omega)⟩
    · exact ⟨rfl, by simp only [Decl.noLooseIn, decide_eq_true_eq]; exact Or.inl (by omega)⟩
  | .fvar _ _, _, _, _ | .sort _, _, _, _ | .const _ _, _, _, _ | .lit _, _, _, _ => ⟨rfl, rfl⟩
  | .app f x, c, k, hno => by
    simp only [Decl.noLooseIn, Bool.and_eq_true] at hno
    obtain ⟨hf1, hf2⟩ := fvarLeaves_instantiate1_of_noLooseIn a f c k hno.1
    obtain ⟨hx1, hx2⟩ := fvarLeaves_instantiate1_of_noLooseIn a x c k hno.2
    exact ⟨by simp [Expr.instantiate1, Expr.fvarLeaves, hf1, hx1],
      by simp [Expr.instantiate1, Decl.noLooseIn, hf2, hx2]⟩
  | .lam ty b _, c, k, hno | .forallE ty b _, c, k, hno => by
    simp only [Decl.noLooseIn, Bool.and_eq_true] at hno
    obtain ⟨ht1, ht2⟩ := fvarLeaves_instantiate1_of_noLooseIn a ty c k hno.1
    have hb_raw := fvarLeaves_instantiate1_of_noLooseIn a b (c + 1) k hno.2
    rw [show c + 1 + k = c + k + 1 by omega] at hb_raw
    exact ⟨by simp [Expr.instantiate1, Expr.fvarLeaves, ht1, hb_raw.1],
      by simp [Expr.instantiate1, Decl.noLooseIn, ht2, hb_raw.2]⟩
  | .letE ty v b _, c, k, hno => by
    simp only [Decl.noLooseIn, Bool.and_eq_true] at hno
    obtain ⟨ht1, ht2⟩ := fvarLeaves_instantiate1_of_noLooseIn a ty c k hno.1.1
    obtain ⟨hv1, hv2⟩ := fvarLeaves_instantiate1_of_noLooseIn a v c k hno.1.2
    have hb_raw := fvarLeaves_instantiate1_of_noLooseIn a b (c + 1) k hno.2
    rw [show c + 1 + k = c + k + 1 by omega] at hb_raw
    exact ⟨by simp [Expr.instantiate1, Expr.fvarLeaves, ht1, hv1, hb_raw.1],
      by simp [Expr.instantiate1, Decl.noLooseIn, ht2, hv2, hb_raw.2]⟩
  | .proj _ _ e, c, k, hno => by
    obtain ⟨he1, he2⟩ := fvarLeaves_instantiate1_of_noLooseIn a e c k hno
    exact ⟨by simp [Expr.instantiate1, Expr.fvarLeaves, he1],
      by simp [Expr.instantiate1, Decl.noLooseIn, he2]⟩

private theorem instSpine_append (xs ys : List KExpr) :
    ∀ (t : Nat) (e : KExpr),
      Expr.instSpine (xs ++ ys) t e = Expr.instSpine ys (t - xs.length) (Expr.instSpine xs t e) := by
  induction xs with
  | nil => intro t e; simp [Expr.instSpine]
  | cons a as ih =>
    intro t e
    simp only [List.cons_append, Expr.instSpine, List.length_cons]
    rw [ih (t - 1) (e.instantiate1 a t), Nat.sub_sub, Nat.add_comm 1 as.length]

private theorem instSpine_drop_leavesFixed :
    ∀ (ys : List KExpr) (e : KExpr),
      Decl.noLooseIn 0 ys.length e = true →
      (Expr.instSpine ys (ys.length - 1) e).fvarLeaves = e.fvarLeaves
  | [], _, _ => rfl
  | a :: ys, e, hno => by
    simp only [List.length_cons, Nat.add_sub_cancel, Expr.instSpine] at hno ⊢
    obtain ⟨hfl, hno'⟩ := fvarLeaves_instantiate1_of_noLooseIn a e 0 ys.length hno
    rw [Nat.zero_add] at hfl hno'
    exact (instSpine_drop_leavesFixed ys (e.instantiate1 a ys.length) hno').trans hfl

private theorem instSpine_prefix_noLooseIn (k : Nat) :
    ∀ (xs : List KExpr) (e : KExpr),
      (∀ a ∈ xs, a.looseBVarsBounded 0 = true) →
      Decl.noLooseIn 0 k e = true →
      Decl.noLooseIn 0 k (Expr.instSpine xs (xs.length + k - 1) e) = true
  | [], _, _, hno => hno
  | a :: xs, e, hxs, hno => by
    simp only [List.length_cons, Expr.instSpine]
    have hidx : xs.length + 1 + k - 1 = xs.length + k := by omega
    rw [hidx]
    have h1 := noLooseIn_instantiate1_ge (hxs a List.mem_cons_self) e 0 k (xs.length + k)
      (by omega) hno
    have hsub : xs.length + k - 1 = xs.length + k - 1 := rfl
    exact instSpine_prefix_noLooseIn k xs (e.instantiate1 a (xs.length + k))
      (fun b hb => hxs b (List.mem_cons_of_mem _ hb)) h1

/-- If `xs.length = np + k`, every prefix entry in `xs.take np` is closed and fixed by `g`, and
`p` has no fvars and no loose bvars in `[0, k)`, then `Expr.instSpine xs (np + k - 1) p` has
`LeavesFixed g`. -/
theorem leavesFixed_instSpine_of_noLooseIn {g : KKey → KKey} {np k : Nat} {xs : List KExpr}
    {p : KExpr} (hlen : xs.length = np + k)
    (hpre : ∀ a ∈ xs.take np, a.looseBVarsBounded 0 = true ∧ LeavesFixed g a)
    (hpfv : p.hasFvar = false)
    (hno : Decl.noLooseIn 0 k p = true) :
    LeavesFixed g (Expr.instSpine xs (np + k - 1) p) := by
  have hsplit : xs = xs.take np ++ xs.drop np := (List.take_append_drop np xs).symm
  have hlen1 : (xs.take np).length = np := by rw [List.length_take, hlen]; omega
  have hlen2 : (xs.drop np).length = k := by rw [List.length_drop, hlen]; omega
  rw [hsplit, instSpine_append]
  have hp_lf : LeavesFixed g p := by
    intro l hl; rw [Expr.fvarLeaves_eq_nil_of_not_hasFvar hpfv] at hl; cases hl
  have hpre_lf : LeavesFixed g (Expr.instSpine (xs.take np) (np + k - 1) p) :=
    Decl.FamilyAlias.LeavesFixed.instSpine' hp_lf (fun a ha => (hpre a ha).2)
  have hpre_no : Decl.noLooseIn 0 k (Expr.instSpine (xs.take np) (np + k - 1) p) = true := by
    have h := instSpine_prefix_noLooseIn k (xs.take np) p (fun a ha => (hpre a ha).1) hno
    rwa [hlen1] at h
  cases k with
  | zero =>
    have hnil : xs.drop np = [] := List.eq_nil_of_length_eq_zero hlen2
    rw [hnil]; exact hpre_lf
  | succ k' =>
    have hrem : np + (k' + 1) - 1 - (xs.take np).length = (xs.drop np).length - 1 := by omega
    rw [hrem]
    intro l hl
    rw [instSpine_drop_leavesFixed (xs.drop np) _ (by rw [hlen2]; exact hpre_no)] at hl
    exact hpre_lf l hl

private theorem noLooseIn_instantiateLevelParams (lo n : Nat) (ks : List LevelParam)
    (us : List KLevel) :
    ∀ e : KExpr, Decl.noLooseIn lo n (e.instantiateLevelParams ks us) = Decl.noLooseIn lo n e
  | .bvar _ | .fvar _ _ | .sort _ | .const _ _ | .lit _ => rfl
  | .app f a => by
    simp [Expr.instantiateLevelParams, Decl.noLooseIn,
      noLooseIn_instantiateLevelParams lo n ks us f,
      noLooseIn_instantiateLevelParams lo n ks us a]
  | .lam t b _ | .forallE t b _ => by
    simp [Expr.instantiateLevelParams, Decl.noLooseIn,
      noLooseIn_instantiateLevelParams lo n ks us t,
      noLooseIn_instantiateLevelParams (lo + 1) n ks us b]
  | .letE t v b _ => by
    simp [Expr.instantiateLevelParams, Decl.noLooseIn,
      noLooseIn_instantiateLevelParams lo n ks us t,
      noLooseIn_instantiateLevelParams lo n ks us v,
      noLooseIn_instantiateLevelParams (lo + 1) n ks us b]
  | .proj _ _ e => noLooseIn_instantiateLevelParams lo n ks us e

private theorem noProjIn_stripPis_doms {bad : List KKey} :
    ∀ (m : Nat) {e : KExpr} {bs : List (KExpr × Ix.Kernel.BinderMeta)} {rem : KExpr},
      Decl.NoProjIn bad e = true → e.stripPis m = some (bs, rem) →
      ∀ d ∈ bs.map Prod.fst, Decl.NoProjIn bad d = true
  | 0, _, _, _, _, hs, _, hd => by
    injection hs with hp; injection hp with hbs _; subst hbs; exact nomatch hd
  | m + 1, .forallE T B _, _, _, hnp, hs, d, hd => by
    simp only [Decl.NoProjIn, Bool.and_eq_true] at hnp
    simp only [Expr.stripPis] at hs
    cases hsb : B.stripPis m with
    | none => simp [hsb] at hs
    | some p =>
      rw [hsb] at hs; injection hs with hp; injection hp with hbs _; subst hbs
      simp only [List.map_cons, List.mem_cons] at hd
      rcases hd with rfl | hd'
      · exact hnp.1
      · exact noProjIn_stripPis_doms m hnp.2 hsb d hd'
  | _ + 1, .bvar _, _, _, _, hs, _, _ | _ + 1, .fvar _ _, _, _, _, hs, _, _
  | _ + 1, .sort _, _, _, _, hs, _, _ | _ + 1, .const _ _, _, _, _, hs, _, _
  | _ + 1, .app _ _, _, _, _, hs, _, _ | _ + 1, .lam _ _ _, _, _, _, hs, _, _
  | _ + 1, .letE _ _ _ _, _, _, _, hs, _, _ | _ + 1, .lit _, _, _, _, hs, _, _
  | _ + 1, .proj _ _ _, _, _, _, hs, _, _ => nomatch hs

/-! ## `AddrIn` backward transport through `rec_major_pins` and `expr_lower` -/

private theorem addrIn_peel_n_foralls {h : Heap F} :
    ∀ {e n r : SourceValue F} {h' : Heap F} {cs : List (Call F)},
      ObsFn Obs.W "KernelCheck::peel_n_foralls" [e, n] h r h' cs →
      h' = h ∧ ∀ a, AddrIn h r a → AddrIn h e a := by
  have hmain : ∀ (fname : String) (args : List (SourceValue F)) (h : Heap F) (r : SourceValue F)
      (h' : Heap F) (cs : List (Call F)),
      ObsFn Obs.W fname args h r h' cs → fname = "KernelCheck::peel_n_foralls" →
      ∀ e n, args = [e, n] → h' = h ∧ ∀ a, AddrIn h r a → AddrIn h e a :=
    ObsFn.strong_induction (world := Obs.W)
      (fun fname args h r h' cs => fname = "KernelCheck::peel_n_foralls" →
        ∀ e n, args = [e, n] → h' = h ∧ ∀ a, AddrIn h r a → AddrIn h e a)
      (fun fname args h r h' cs ev ih hfn e n hargs => by
        subst hfn hargs
        match Obs.«KernelCheck::peel_n_foralls».obs ev with
        | .n0 (he16 := hr) (he17 := hh) .. => subst hr hh; exact ⟨rfl, fun _ ha => ha⟩
        | .other (w42 := w42) (x_body := xb) (w43 := w43) (cs62 := cs62) (ld34 := ld) (ev64 := evRec) (hc89 := hc) .. =>
          have hlt : cs62.length < cs.length := by rw [hc]; simp
          obtain ⟨hh, hsub⟩ := ih _ _ _ _ _ _ hlt evRec rfl xb _ rfl
          refine ⟨hh, fun a ha => ?_⟩
          cases e with
          | ptr ty addr =>
            simp only [loadValue] at ld
            cases hget : h[addr]? with
            | none => rw [hget] at ld; cases ld
            | some v =>
              rw [hget] at ld
              dsimp only at ld
              split at ld
              · cases ld
              · next hty =>
                have hv : v = .construct kexprEnum "Forall" [w42, xb, w43] :=
                  Except.ok.inj ld
                subst hv
                have hty' : ty = .enum kexprEnum := by
                  simp only [not_not, Value.type] at hty; exact hty.symm
                subst hty'
                exact .forallBody hget (hsub a ha)
          | field _ | tuple _ | construct _ _ _ => simp [loadValue] at ld)
  intro e n r h' cs ev
  exact hmain _ _ _ _ _ _ ev rfl e n rfl

private theorem addrIn_snoc_list {R : Heap F → SourceValue F → Prop}
    (hmono : ∀ {h₁ h₂ p}, Heap.Extends h₁ h₂ → R h₁ p → R h₂ p) :
    ∀ {xs : List (SourceValue F)} {lp xp r : SourceValue F} {h h' : Heap F} {cs : List (Call F)},
      ObsFn Obs.W Obs.Names.«Lists::snoc<&KernelTypes::KExprNode>» [lp, xp] h r h' cs →
      RepList kexprListEnum (fun h _ p => R h p) h xs lp →
      R h xp →
      RepList kexprListEnum (fun h _ p => R h p) h' (xs ++ [xp]) r := by
  intro xs
  induction xs with
  | nil =>
    intro lp xp r h h' cs ev hlp hxp
    have ev' : ObsFn Obs.W (Instance.mk "Lists::snoc" [(.ptr (.named "KernelTypes::KExprNode" []))]).symbol
        [lp, xp] h r h' cs := by
      rw [Obs.Names.«Lists::snoc<&KernelTypes::KExprNode>».symbol]; exact ev
    have hlp' : RepList (Instance.mk "Lists::Node" [(.ptr (.named "KernelTypes::KExprNode" []))]).symbol
        (fun h _ p => R h p) h ([] : List (SourceValue F)) lp := by
      rw [Obs.Names.«Lists::Node<&KernelTypes::KExprNode>».symbol]; exact hlp
    have hres := Lib.Lists.snoc_spec (R := fun h _ p => R h p)
      (fun _ _ _ _ ext r => hmono ext r) (x := xp) ev' hlp' hxp
    rwa [Obs.Names.«Lists::Node<&KernelTypes::KExprNode>».symbol] at hres
  | cons x xs _ =>
    intro lp xp r h h' cs ev hlp hxp
    have ev' : ObsFn Obs.W (Instance.mk "Lists::snoc" [(.ptr (.named "KernelTypes::KExprNode" []))]).symbol
        [lp, xp] h r h' cs := by
      rw [Obs.Names.«Lists::snoc<&KernelTypes::KExprNode>».symbol]; exact ev
    have hlp' : RepList (Instance.mk "Lists::Node" [(.ptr (.named "KernelTypes::KExprNode" []))]).symbol
        (fun h _ p => R h p) h (x :: xs) lp := by
      rw [Obs.Names.«Lists::Node<&KernelTypes::KExprNode>».symbol]; exact hlp
    have hres := Lib.Lists.snoc_spec (R := fun h _ p => R h p)
      (fun _ _ _ _ ext r => hmono ext r) (x := xp) ev' hlp' hxp
    rwa [Obs.Names.«Lists::Node<&KernelTypes::KExprNode>».symbol] at hres

/-- A `KernelTypes::KExprNode` pointer whose every reachable node and address cell lies in `h`.
Closedness transfers `AddrIn` backward across any heap extension without requiring `TmExact`. -/
private inductive KExprClosed (h : Heap F) : SourceValue F → Prop where
  | atom {idx : Nat} {tag : String} {xs : List (SourceValue F)} :
      h[idx]? = some (.construct kexprEnum tag xs) →
      tag ≠ "Const" → tag ≠ "Proj" → tag ≠ "App" → tag ≠ "Lam" → tag ≠ "Forall" → tag ≠ "Let" →
      KExprClosed h (.ptr (.enum kexprEnum) idx)
  | const {idx i : Nat} {ap lv v : SourceValue F} :
      h[idx]? = some (.construct kexprEnum "Const" [ap, lv]) →
      ap = .ptr addrTy i → h[i]? = some v →
      KExprClosed h (.ptr (.enum kexprEnum) idx)
  | proj {idx i : Nat} {ap ep v : SourceValue F} {fi : F} :
      h[idx]? = some (.construct kexprEnum "Proj" [ap, .field fi, ep]) →
      ap = .ptr addrTy i → h[i]? = some v → KExprClosed h ep →
      KExprClosed h (.ptr (.enum kexprEnum) idx)
  | app {idx : Nat} {fp ap : SourceValue F} :
      h[idx]? = some (.construct kexprEnum "App" [fp, ap]) →
      KExprClosed h fp → KExprClosed h ap →
      KExprClosed h (.ptr (.enum kexprEnum) idx)
  | lam {idx : Nat} {tp bp bl : SourceValue F} :
      h[idx]? = some (.construct kexprEnum "Lam" [tp, bp, bl]) →
      KExprClosed h tp → KExprClosed h bp →
      KExprClosed h (.ptr (.enum kexprEnum) idx)
  | forallE {idx : Nat} {tp bp bl : SourceValue F} :
      h[idx]? = some (.construct kexprEnum "Forall" [tp, bp, bl]) →
      KExprClosed h tp → KExprClosed h bp →
      KExprClosed h (.ptr (.enum kexprEnum) idx)
  | letE {idx : Nat} {tp vp bp : SourceValue F} :
      h[idx]? = some (.construct kexprEnum "Let" [tp, vp, bp]) →
      KExprClosed h tp → KExprClosed h vp → KExprClosed h bp →
      KExprClosed h (.ptr (.enum kexprEnum) idx)

private theorem KExprClosed.mono {h₁ h₂ : Heap F} (ext : Heap.Extends h₁ h₂) {p : SourceValue F}
    (hc : KExprClosed h₁ p) : KExprClosed h₂ p := by
  induction hc with
  | atom hg h1 h2 h3 h4 h5 h6 => exact .atom (ext.getElem?_eq hg) h1 h2 h3 h4 h5 h6
  | const hg hp hv => exact .const (ext.getElem?_eq hg) hp (ext.getElem?_eq hv)
  | proj hg hp hv _ ih => exact .proj (ext.getElem?_eq hg) hp (ext.getElem?_eq hv) ih
  | app hg _ _ ih1 ih2 => exact .app (ext.getElem?_eq hg) ih1 ih2
  | lam hg _ _ ih1 ih2 => exact .lam (ext.getElem?_eq hg) ih1 ih2
  | forallE hg _ _ ih1 ih2 => exact .forallE (ext.getElem?_eq hg) ih1 ih2
  | letE hg _ _ _ ih1 ih2 ih3 => exact .letE (ext.getElem?_eq hg) ih1 ih2 ih3

private theorem repAddr_back_of_cell {h₁ h₂ : Heap F} (ext : Heap.Extends h₁ h₂)
    {ap v : SourceValue F} {i : Nat} {a : Bytes.Address}
    (hp : ap = .ptr addrTy i) (hget₁ : h₁[i]? = some v)
    (hra : Bytes.RepAddressRef addrTy h₂ a ap) :
    Bytes.RepAddressRef addrTy h₁ a ap := by
  subst hp
  obtain ⟨i', cv, hptr, hget₂, hrep⟩ := hra
  injection hptr with _ hi; subst hi
  have hcv : cv = v := Option.some.inj (hget₂.symm.trans (ext.getElem?_eq hget₁))
  subst hcv
  exact ⟨i, cv, rfl, hget₁, hrep⟩

private theorem KExprClosed.addrIn_back {h₁ h₂ : Heap F} (ext : Heap.Extends h₁ h₂)
    {p : SourceValue F} (hc : KExprClosed h₁ p) :
    ∀ a, AddrIn h₂ p a → AddrIn h₁ p a := by
  induction hc with
  | atom hget h1 h2 h3 h4 h5 h6 =>
    intro a ha
    exact (Binding.addrIn_none (ext.getElem?_eq hget) ⟨h1, h2, h3, h4, h5, h6⟩ ha).elim
  | const hget hp hv =>
    intro a ha
    exact .const hget (repAddr_back_of_cell ext hp hv (Binding.addrIn_const_inv (ext.getElem?_eq hget) ha))
  | proj hget hp hv _ ih =>
    intro a ha
    rcases Binding.addrIn_proj_inv (ext.getElem?_eq hget) ha with hra | hsub
    · exact .projHead hget (repAddr_back_of_cell ext hp hv hra)
    · exact .projArg hget (ih a hsub)
  | app hget _ _ ih1 ih2 =>
    intro a ha
    rcases Binding.addrIn_app_inv (ext.getElem?_eq hget) ha with h1 | h2
    · exact .appFn hget (ih1 a h1)
    · exact .appArg hget (ih2 a h2)
  | lam hget _ _ ih1 ih2 =>
    intro a ha
    rcases Binding.addrIn_lam_inv (ext.getElem?_eq hget) ha with h1 | h2
    · exact .lamTy hget (ih1 a h1)
    · exact .lamBody hget (ih2 a h2)
  | forallE hget _ _ ih1 ih2 =>
    intro a ha
    rcases Binding.addrIn_forall_inv (ext.getElem?_eq hget) ha with h1 | h2
    · exact .forallTy hget (ih1 a h1)
    · exact .forallBody hget (ih2 a h2)
  | letE hget _ _ _ ih1 ih2 ih3 =>
    intro a ha
    rcases Binding.addrIn_let_inv (ext.getElem?_eq hget) ha with h1 | h2 | h3
    · exact .letTy hget (ih1 a h1)
    · exact .letVal hget (ih2 a h2)
    · exact .letBody hget (ih3 a h3)

private theorem KExprClosed.of_tmExact {κ : _root_.Address → KKey} {Γ : Nat → KExpr} {h : Heap F}
    {k : Nat} {E : KExpr} {p : SourceValue F} (rep : Decl.TmExact κ 0 Γ h k E p) :
    KExprClosed h p := by
  induction rep with
  | bvarLocal cell _ _ | bvarFree cell _ _ _ | sort cell _ | litNat cell _ _ | litStr cell _ _ =>
    exact .atom cell (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  | const cell ra _ =>
    obtain ⟨i, v, hp, hg, _⟩ := ra
    exact .const cell hp hg
  | proj cell ra _ ihe =>
    obtain ⟨i, v, hp, hg, _⟩ := ra
    exact .proj cell hp hg ihe
  | app cell _ _ ihf iha => exact .app cell ihf iha
  | lam cell _ _ _ iht ihb => exact .lam cell iht ihb
  | forallE cell _ _ _ iht ihb => exact .forallE cell iht ihb
  | letE cell _ _ _ iht ihv ihb => exact .letE cell iht ihv ihb

private theorem KExprClosed.load_const {h : Heap F} {p ap lv : SourceValue F}
    (hc : KExprClosed h p) (ld : loadValue h p = .ok (.construct kexprEnum "Const" [ap, lv])) :
    ∃ idx i v, p = .ptr (.enum kexprEnum) idx ∧
      h[idx]? = some (.construct kexprEnum "Const" [ap, lv]) ∧ ap = .ptr addrTy i ∧ h[i]? = some v := by
  cases hc with
  | const cell hp hv =>
    obtain ⟨_, hxs⟩ := load_cell cell ld
    injection hxs with h1 hxs; injection hxs with h2 _; subst h1 h2
    exact ⟨_, _, _, rfl, cell, hp, hv⟩
  | atom cell h1 _ _ _ _ _ => exact (load_cell_ne cell ld h1).elim
  | proj cell _ _ _ | app cell _ _ | lam cell _ _ | forallE cell _ _ | letE cell _ _ _ =>
    exact (load_cell_ne cell ld (by decide)).elim

private theorem KExprClosed.load_proj {h : Heap F} {p ap fi ep : SourceValue F}
    (hc : KExprClosed h p) (ld : loadValue h p = .ok (.construct kexprEnum "Proj" [ap, fi, ep])) :
    ∃ (idx i : Nat) (v : SourceValue F) (f : F), p = .ptr (.enum kexprEnum) idx ∧ fi = .field f ∧
      h[idx]? = some (.construct kexprEnum "Proj" [ap, .field f, ep]) ∧
      ap = .ptr addrTy i ∧ h[i]? = some v ∧ KExprClosed h ep := by
  cases hc with
  | proj cell hp hv hce =>
    obtain ⟨_, hxs⟩ := load_cell cell ld
    injection hxs with h1 hxs; injection hxs with h2 hxs; injection hxs with h3 _; subst h1 h2 h3
    exact ⟨_, _, _, _, rfl, rfl, cell, hp, hv, hce⟩
  | atom cell _ h2 _ _ _ _ => exact (load_cell_ne cell ld h2).elim
  | const cell _ _ | app cell _ _ | lam cell _ _ | forallE cell _ _ | letE cell _ _ _ =>
    exact (load_cell_ne cell ld (by decide)).elim

private theorem KExprClosed.load_app {h : Heap F} {p fp ap : SourceValue F}
    (hc : KExprClosed h p) (ld : loadValue h p = .ok (.construct kexprEnum "App" [fp, ap])) :
    ∃ idx, p = .ptr (.enum kexprEnum) idx ∧ h[idx]? = some (.construct kexprEnum "App" [fp, ap]) ∧
      KExprClosed h fp ∧ KExprClosed h ap := by
  cases hc with
  | app cell hcf hca =>
    obtain ⟨_, hxs⟩ := load_cell cell ld
    injection hxs with h1 hxs; injection hxs with h2 _; subst h1 h2
    exact ⟨_, rfl, cell, hcf, hca⟩
  | atom cell _ _ h3 _ _ _ => exact (load_cell_ne cell ld h3).elim
  | const cell _ _ | proj cell _ _ _ | lam cell _ _ | forallE cell _ _ | letE cell _ _ _ =>
    exact (load_cell_ne cell ld (by decide)).elim

private theorem KExprClosed.load_lam {h : Heap F} {p tp bp bl : SourceValue F}
    (hc : KExprClosed h p) (ld : loadValue h p = .ok (.construct kexprEnum "Lam" [tp, bp, bl])) :
    ∃ idx, p = .ptr (.enum kexprEnum) idx ∧ h[idx]? = some (.construct kexprEnum "Lam" [tp, bp, bl]) ∧
      KExprClosed h tp ∧ KExprClosed h bp := by
  cases hc with
  | lam cell hct hcb =>
    obtain ⟨_, hxs⟩ := load_cell cell ld
    injection hxs with h1 hxs; injection hxs with h2 hxs; injection hxs with h3 _; subst h1 h2 h3
    exact ⟨_, rfl, cell, hct, hcb⟩
  | atom cell _ _ _ h4 _ _ => exact (load_cell_ne cell ld h4).elim
  | const cell _ _ | proj cell _ _ _ | app cell _ _ | forallE cell _ _ | letE cell _ _ _ =>
    exact (load_cell_ne cell ld (by decide)).elim

private theorem KExprClosed.load_forall {h : Heap F} {p tp bp bl : SourceValue F}
    (hc : KExprClosed h p) (ld : loadValue h p = .ok (.construct kexprEnum "Forall" [tp, bp, bl])) :
    ∃ idx, p = .ptr (.enum kexprEnum) idx ∧ h[idx]? = some (.construct kexprEnum "Forall" [tp, bp, bl]) ∧
      KExprClosed h tp ∧ KExprClosed h bp := by
  cases hc with
  | forallE cell hct hcb =>
    obtain ⟨_, hxs⟩ := load_cell cell ld
    injection hxs with h1 hxs; injection hxs with h2 hxs; injection hxs with h3 _; subst h1 h2 h3
    exact ⟨_, rfl, cell, hct, hcb⟩
  | atom cell _ _ _ _ h5 _ => exact (load_cell_ne cell ld h5).elim
  | const cell _ _ | proj cell _ _ _ | app cell _ _ | lam cell _ _ | letE cell _ _ _ =>
    exact (load_cell_ne cell ld (by decide)).elim

private theorem KExprClosed.load_let {h : Heap F} {p tp vp bp : SourceValue F}
    (hc : KExprClosed h p) (ld : loadValue h p = .ok (.construct kexprEnum "Let" [tp, vp, bp])) :
    ∃ idx, p = .ptr (.enum kexprEnum) idx ∧ h[idx]? = some (.construct kexprEnum "Let" [tp, vp, bp]) ∧
      KExprClosed h tp ∧ KExprClosed h vp ∧ KExprClosed h bp := by
  cases hc with
  | letE cell hct hcv hcb =>
    obtain ⟨_, hxs⟩ := load_cell cell ld
    injection hxs with h1 hxs; injection hxs with h2 hxs; injection hxs with h3 _; subst h1 h2 h3
    exact ⟨_, rfl, cell, hct, hcv, hcb⟩
  | atom cell _ _ _ _ _ h6 => exact (load_cell_ne cell ld h6).elim
  | const cell _ _ | proj cell _ _ _ | app cell _ _ | lam cell _ _ | forallE cell _ _ =>
    exact (load_cell_ne cell ld (by decide)).elim

/-- Every `AddrIn` of an output of `KernelSubst::expr_lower` already occurs in its input, and
closedness is preserved. -/
private theorem addrIn_expr_lower_closed :
    ∀ {e s c r : SourceValue F} {h h' : Heap F} {cs : List (Call F)},
      ObsFn Obs.W "KernelSubst::expr_lower" [e, s, c] h r h' cs →
      KExprClosed h e →
      KExprClosed h' r ∧ ∀ a, AddrIn h' r a → AddrIn h e a := by
  let P : String → List (SourceValue F) → Heap F → SourceValue F → Heap F → List (Call F) → Prop :=
    fun fname args h r h' _ =>
      (fname = "KernelSubst::expr_lower" →
        ∀ e s c, args = [e, s, c] → KExprClosed h e →
          KExprClosed h' r ∧ ∀ a, AddrIn h' r a → AddrIn h e a) ∧
      (fname = "KernelSubst::expr_lower_walk" →
        ∀ e s c, args = [e, s, c] → KExprClosed h e →
          KExprClosed h' r ∧ ∀ a, AddrIn h' r a → AddrIn h e a) ∧
      (fname = "KernelSubst::expr_lower_let" →
        ∀ x_ty x_val x_body s c, args = [x_ty, x_val, x_body, s, c] →
          KExprClosed h x_ty → KExprClosed h x_val → KExprClosed h x_body →
          KExprClosed h' r ∧
            ∀ a, AddrIn h' r a → AddrIn h x_ty a ∨ AddrIn h x_val a ∨ AddrIn h x_body a)
  have hmain : ∀ fname args h r h' cs, ObsFn Obs.W fname args h r h' cs → P fname args h r h' cs :=
    ObsFn.strong_induction (world := Obs.W) P (fun fname args h r h' cs ev ih => by
      refine ⟨?_, ?_, ?_⟩
      · intro hfn e s c hargs hc
        subst hfn hargs
        match Obs.«KernelSubst::expr_lower».obs ev with
        | .n0 (he16 := hr) (he17 := hh) .. => subst hr hh; exact ⟨hc, fun _ ha => ha⟩
        | .other_n0 (ev36 := ev1) (ev59 := ev2) (he81 := hr) (he82 := hh) .. =>
          subst hr hh
          have ext := ev1.heap_extends.trans ev2.heap_extends
          exact ⟨hc.mono ext, fun a ha => hc.addrIn_back ext a ha⟩
        | .other_n1 (cs92 := cs92) (ev36 := ev1) (ev59 := ev2) (ev94 := evW) (hc119 := hc119) .. =>
          have ext := ev1.heap_extends.trans ev2.heap_extends
          have hlt : cs92.length < cs.length := by
            rw [hc119]; simp only [List.length_cons, List.length_append]; omega
          obtain ⟨hc', hsub⟩ := (ih _ _ _ _ _ _ hlt evW).2.1 rfl e s c rfl (hc.mono ext)
          exact ⟨hc', fun a ha => hc.addrIn_back ext a (hsub a ha)⟩
      · intro hfn e s c hargs hc
        subst hfn hargs
        match Obs.«KernelSubst::expr_lower_walk».obs ev with
        | .BVar (v33 := v33) (he29 := hr) (hm28 := hh) .. =>
          subst hr hh
          have hcell : (h ++ [.construct kexprEnum "BVar" [v33]])[h.length]? =
              some (.construct kexprEnum "BVar" [v33]) := by simp
          exact ⟨.atom hcell (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
            fun a ha => (Binding.addrIn_none hcell (by decide) ha).elim⟩
        | .Srt (x_l := xl) (he67 := hr) (hm66 := hh) .. =>
          subst hr hh
          have hcell : (h ++ [.construct kexprEnum "Srt" [xl]])[h.length]? =
              some (.construct kexprEnum "Srt" [xl]) := by simp
          exact ⟨.atom hcell (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
            fun a ha => (Binding.addrIn_none hcell (by decide) ha).elim⟩
        | .Lit (x_lit := xlit) (he549 := hr) (hm548 := hh) .. =>
          subst hr hh
          have hcell : (h ++ [.construct kexprEnum "Lit" [xlit]])[h.length]? =
              some (.construct kexprEnum "Lit" [xlit]) := by simp
          exact ⟨.atom hcell (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
            fun a ha => (Binding.addrIn_none hcell (by decide) ha).elim⟩
        | .Const (x_idx := x_idx) (x_lvls := x_lvls) (ld12 := ld) (he101 := hr) (hm100 := hh) .. =>
          subst hr hh
          obtain ⟨idx, i, v, rfl, hget, hp, hv⟩ := hc.load_const ld
          have ext := Heap.Extends.snoc h (.construct kexprEnum "Const" [x_idx, x_lvls])
          have hcell : (h ++ [.construct kexprEnum "Const" [x_idx, x_lvls]])[h.length]? =
              some (.construct kexprEnum "Const" [x_idx, x_lvls]) := by simp
          refine ⟨.const hcell hp (ext.getElem?_eq hv), fun a ha => ?_⟩
          exact .const hget (repAddr_back_of_cell ext hp hv (Binding.addrIn_const_inv hcell ha))
        | .App (x_f := xf) (x_a := xa) (v147 := vf) (v148 := va) (m150 := m1) (cs158 := cs1)
            (m186 := m2) (cs194 := cs2) (ld12 := ld) (he143 := hr) (hm142 := hh)
            (ev160 := ev1) (ev196 := ev2) (hc221 := hc221) .. =>
          subst hr hh
          obtain ⟨idx, rfl, hget, hcf, hca⟩ := hc.load_app ld
          have hlt1 : cs1.length < cs.length := by
            rw [hc221]; simp only [List.length_cons, List.length_append]; omega
          have hlt2 : cs2.length < cs.length := by
            rw [hc221]; simp only [List.length_cons, List.length_append]; omega
          obtain ⟨hcvf, hsubf⟩ := (ih _ _ _ _ _ _ hlt1 ev1).1 rfl xf s c rfl hcf
          obtain ⟨hcva, hsuba⟩ := (ih _ _ _ _ _ _ hlt2 ev2).1 rfl xa s c rfl (hca.mono ev1.heap_extends)
          have extS := Heap.Extends.snoc m2 (.construct kexprEnum "App" [vf, va])
          have ext1S := ev2.heap_extends.trans extS
          have hcell : (m2 ++ [.construct kexprEnum "App" [vf, va]])[m2.length]? =
              some (.construct kexprEnum "App" [vf, va]) := by simp
          refine ⟨.app hcell (hcvf.mono ext1S) (hcva.mono extS), fun a ha => ?_⟩
          rcases Binding.addrIn_app_inv hcell ha with hf | harg
          · exact .appFn hget (hsubf a (hcvf.addrIn_back ext1S a hf))
          · exact .appArg hget (hca.addrIn_back ev1.heap_extends a (hsuba a (hcva.addrIn_back extS a harg)))
        | .Lam (x_ty := xt) (x_body := xb) (x_bl := xbl) (v252 := vt) (v253 := vb) (m256 := m1)
            (cs264 := cs1) (m292 := m2) (cs300 := cs2) (v305 := c1) (ld12 := ld) (he248 := hr)
            (hm247 := hh) (ev266 := ev1) (ev302 := ev2) (hc342 := hc342) .. =>
          subst hr hh
          obtain ⟨idx, rfl, hget, hct, hcb⟩ := hc.load_lam ld
          have hlt1 : cs1.length < cs.length := by
            rw [hc342]; simp only [List.length_cons, List.length_append]; omega
          have hlt2 : cs2.length < cs.length := by
            rw [hc342]; simp only [List.length_cons, List.length_append]; omega
          obtain ⟨hcvt, hsubt⟩ := (ih _ _ _ _ _ _ hlt1 ev1).1 rfl xt s c rfl hct
          obtain ⟨hcvb, hsubb⟩ := (ih _ _ _ _ _ _ hlt2 ev2).1 rfl xb s c1 rfl (hcb.mono ev1.heap_extends)
          have extS := Heap.Extends.snoc m2 (.construct kexprEnum "Lam" [vt, vb, xbl])
          have ext1S := ev2.heap_extends.trans extS
          have hcell : (m2 ++ [.construct kexprEnum "Lam" [vt, vb, xbl]])[m2.length]? =
              some (.construct kexprEnum "Lam" [vt, vb, xbl]) := by simp
          refine ⟨.lam hcell (hcvt.mono ext1S) (hcvb.mono extS), fun a ha => ?_⟩
          rcases Binding.addrIn_lam_inv hcell ha with ht | hb
          · exact .lamTy hget (hsubt a (hcvt.addrIn_back ext1S a ht))
          · exact .lamBody hget (hcb.addrIn_back ev1.heap_extends a (hsubb a (hcvb.addrIn_back extS a hb)))
        | .Forall (x_ty := xt) (x_body := xb) (x_bl := xbl) (v373 := vt) (v374 := vb) (m377 := m1)
            (cs385 := cs1) (m413 := m2) (cs421 := cs2) (v426 := c1) (ld12 := ld) (he369 := hr)
            (hm368 := hh) (ev387 := ev1) (ev423 := ev2) (hc463 := hc463) .. =>
          subst hr hh
          obtain ⟨idx, rfl, hget, hct, hcb⟩ := hc.load_forall ld
          have hlt1 : cs1.length < cs.length := by
            rw [hc463]; simp only [List.length_cons, List.length_append]; omega
          have hlt2 : cs2.length < cs.length := by
            rw [hc463]; simp only [List.length_cons, List.length_append]; omega
          obtain ⟨hcvt, hsubt⟩ := (ih _ _ _ _ _ _ hlt1 ev1).1 rfl xt s c rfl hct
          obtain ⟨hcvb, hsubb⟩ := (ih _ _ _ _ _ _ hlt2 ev2).1 rfl xb s c1 rfl (hcb.mono ev1.heap_extends)
          have extS := Heap.Extends.snoc m2 (.construct kexprEnum "Forall" [vt, vb, xbl])
          have ext1S := ev2.heap_extends.trans extS
          have hcell : (m2 ++ [.construct kexprEnum "Forall" [vt, vb, xbl]])[m2.length]? =
              some (.construct kexprEnum "Forall" [vt, vb, xbl]) := by simp
          refine ⟨.forallE hcell (hcvt.mono ext1S) (hcvb.mono extS), fun a ha => ?_⟩
          rcases Binding.addrIn_forall_inv hcell ha with ht | hb
          · exact .forallTy hget (hsubt a (hcvt.addrIn_back ext1S a ht))
          · exact .forallBody hget (hcb.addrIn_back ev1.heap_extends a (hsubb a (hcvb.addrIn_back extS a hb)))
        | .Let (x_ty := xt) (x_val := xv) (x_body := xb) (cs489 := cs1) (ld12 := ld)
            (ev491 := evL) (hc532 := hc532) .. =>
          obtain ⟨idx, rfl, hget, hct, hcv, hcb⟩ := hc.load_let ld
          have hlt : cs1.length < cs.length := by rw [hc532]; simp
          obtain ⟨hc', hsub⟩ := (ih _ _ _ _ _ _ hlt evL).2.2 rfl xt xv xb s c rfl hct hcv hcb
          refine ⟨hc', fun a ha => ?_⟩
          rcases hsub a ha with ht | hv | hb
          · exact .letTy hget ht
          · exact .letVal hget hv
          · exact .letBody hget hb
        | .Proj (x_tidx := xti) (x_fidx := xfi) (x_e1 := xe) (v594 := ve) (m610 := m1)
            (cs618 := cs1) (ld12 := ld) (he588 := hr) (hm587 := hh) (ev620 := ev1) (hc645 := hc645) .. =>
          subst hr hh
          obtain ⟨idx, i, v, f, rfl, rfl, hget, hp, hv, hce⟩ := hc.load_proj ld
          have hlt : cs1.length < cs.length := by rw [hc645]; simp
          obtain ⟨hcve, hsube⟩ := (ih _ _ _ _ _ _ hlt ev1).1 rfl xe s c rfl hce
          have extS := Heap.Extends.snoc m1 (.construct kexprEnum "Proj" [xti, .field f, ve])
          have extAll := ev1.heap_extends.trans extS
          have hcell : (m1 ++ [.construct kexprEnum "Proj" [xti, .field f, ve]])[m1.length]? =
              some (.construct kexprEnum "Proj" [xti, .field f, ve]) := by simp
          refine ⟨.proj hcell hp (extAll.getElem?_eq hv) (hcve.mono extS), fun a ha => ?_⟩
          rcases Binding.addrIn_proj_inv hcell ha with hra | he
          · exact .projHead hget (repAddr_back_of_cell extAll hp hv hra)
          · exact .projArg hget (hsube a (hcve.addrIn_back extS a he))
      · intro hfn xt xv xb s c hargs hct hcv hcb
        subst hfn hargs
        match Obs.«KernelSubst::expr_lower_let».obs ev with
        | .run (v9 := vt) (v10 := vv) (v11 := vb) (m13 := m1) (cs21 := cs1) (m49 := m2)
            (cs57 := cs2) (m85 := m3) (cs93 := cs3) (v98 := c1) (he5 := hr) (hm4 := hh)
            (ev23 := ev1) (ev59 := ev2) (ev95 := ev3) (hc128 := hc128) .. =>
          subst hr hh
          have hlt1 : cs1.length < cs.length := by
            rw [hc128]; simp only [List.length_cons, List.length_append]; omega
          have hlt2 : cs2.length < cs.length := by
            rw [hc128]; simp only [List.length_cons, List.length_append]; omega
          have hlt3 : cs3.length < cs.length := by
            rw [hc128]; simp only [List.length_cons, List.length_append]; omega
          obtain ⟨hcvt, hsubt⟩ := (ih _ _ _ _ _ _ hlt1 ev1).1 rfl xt s c rfl hct
          obtain ⟨hcvv, hsubv⟩ := (ih _ _ _ _ _ _ hlt2 ev2).1 rfl xv s c rfl (hcv.mono ev1.heap_extends)
          have ext12 := ev1.heap_extends.trans ev2.heap_extends
          obtain ⟨hcvb, hsubb⟩ := (ih _ _ _ _ _ _ hlt3 ev3).1 rfl xb s c1 rfl (hcb.mono ext12)
          have extS := Heap.Extends.snoc m3 (.construct kexprEnum "Let" [vt, vv, vb])
          have ext2S := ev3.heap_extends.trans extS
          have ext1S := ev2.heap_extends.trans ext2S
          have hcell : (m3 ++ [.construct kexprEnum "Let" [vt, vv, vb]])[m3.length]? =
              some (.construct kexprEnum "Let" [vt, vv, vb]) := by simp
          refine ⟨.letE hcell (hcvt.mono ext1S) (hcvv.mono ext2S) (hcvb.mono extS), fun a ha => ?_⟩
          rcases Binding.addrIn_let_inv hcell ha with ht | hv | hb
          · exact Or.inl (hsubt a (hcvt.addrIn_back ext1S a ht))
          · exact Or.inr (Or.inl (hcv.addrIn_back ev1.heap_extends a (hsubv a (hcvv.addrIn_back ext2S a hv))))
          · exact Or.inr (Or.inr (hcb.addrIn_back ext12 a (hsubb a (hcvb.addrIn_back extS a hb))))
    )
  intro e s c r h h' cs ev hc
  exact (hmain _ _ _ _ _ _ ev).1 rfl e s c rfl hc

private theorem kExprClosed_peel_n_foralls :
    ∀ {e n r : SourceValue F} {h h' : Heap F} {cs : List (Call F)},
      ObsFn Obs.W "KernelCheck::peel_n_foralls" [e, n] h r h' cs →
      KExprClosed h e → KExprClosed h r := by
  have hmain : ∀ fname args h r h' cs, ObsFn Obs.W fname args h r h' cs →
      fname = "KernelCheck::peel_n_foralls" → ∀ e n, args = [e, n] →
        KExprClosed h e → KExprClosed h r :=
    ObsFn.strong_induction (world := Obs.W)
      (fun fname args h r _ _ => fname = "KernelCheck::peel_n_foralls" →
        ∀ e n, args = [e, n] → KExprClosed h e → KExprClosed h r)
      (fun fname args h r h' cs ev ih hfn e n hargs hc => by
        subst hfn hargs
        match Obs.«KernelCheck::peel_n_foralls».obs ev with
        | .n0 (he16 := hr) .. => subst hr; exact hc
        | .other (x_body := xb) (cs62 := cs62) (ld34 := ld) (ev64 := evRec) (hc89 := hc89) .. =>
          obtain ⟨_, _, _, _, hcb⟩ := hc.load_forall ld
          have hlt : cs62.length < cs.length := by rw [hc89]; simp
          exact ih _ _ _ _ _ _ hlt evRec rfl xb _ rfl hcb)
  intro e n r h h' cs ev hc
  exact hmain _ _ _ _ _ _ ev rfl e n rfl hc

private theorem addrIn_collect_spine {h0 : Heap F} {e0 : SourceValue F} :
    ∀ {e hd args : SourceValue F} {h h' : Heap F} {cs : List (Call F)},
      ObsFn Obs.W "KernelTypes::collect_spine" [e] h (.tuple [hd, args]) h' cs →
      KExprClosed h e →
      (∀ a, AddrIn h e a → AddrIn h0 e0 a) →
      ∃ xs : List (SourceValue F),
        RepList kexprListEnum
          (fun h _ p => KExprClosed h p ∧ ∀ a, AddrIn h p a → AddrIn h0 e0 a) h' xs args := by
  have hmono : ∀ {h₁ h₂ p}, Heap.Extends h₁ h₂ →
      (KExprClosed h₁ p ∧ ∀ a, AddrIn h₁ p a → AddrIn h0 e0 a) →
      (KExprClosed h₂ p ∧ ∀ a, AddrIn h₂ p a → AddrIn h0 e0 a) :=
    fun ext ⟨hc, hs⟩ => ⟨hc.mono ext, fun a ha => hs a (hc.addrIn_back ext a ha)⟩
  have hmain : ∀ fname args h r h' cs, ObsFn Obs.W fname args h r h' cs →
      fname = "KernelTypes::collect_spine" →
      ∀ e hd x_args, args = [e] → r = .tuple [hd, x_args] →
        KExprClosed h e → (∀ a, AddrIn h e a → AddrIn h0 e0 a) →
        ∃ xs : List (SourceValue F),
          RepList kexprListEnum
            (fun h _ p => KExprClosed h p ∧ ∀ a, AddrIn h p a → AddrIn h0 e0 a) h' xs x_args :=
    ObsFn.strong_induction (world := Obs.W)
      (fun fname args h r h' _ => fname = "KernelTypes::collect_spine" →
        ∀ e hd x_args, args = [e] → r = .tuple [hd, x_args] →
          KExprClosed h e → (∀ a, AddrIn h e a → AddrIn h0 e0 a) →
          ∃ xs : List (SourceValue F),
            RepList kexprListEnum
              (fun h _ p => KExprClosed h p ∧ ∀ a, AddrIn h p a → AddrIn h0 e0 a) h' xs x_args)
      (fun fname args h r h' cs ev ih hfn e hd x_args hargs hr hc hsub => by
        subst hfn hargs hr
        match Obs.«KernelTypes::collect_spine».obs ev with
        | .other (he115 := hr) (hm132 := hm) (he136 := hh) .. =>
          subst hh hm
          injection hr with hl; injection hl with _ hl; injection hl with h2 _; subst h2
          exact ⟨[], .nil (by simp)⟩
        | .App (x_f := xf) (x_a := xa) (m31 := m1) (cs41 := cs1) (x_head := xh)
            (x_args := xas) (v68 := v68) (ld12 := ld) (ev43 := evRec) (he69 := hr)
            (ev88 := evSnoc) (he105 := hh) (hc106 := hc106) .. =>
          subst hh
          injection hr with hl; injection hl with _ hl; injection hl with h2 _; subst h2
          obtain ⟨idx, rfl, hget, hcf, hca⟩ := hc.load_app ld
          have hlt : cs1.length < cs.length := by
            rw [hc106]; simp only [List.length_cons, List.length_append]; omega
          obtain ⟨xs, hxs⟩ := ih _ _ _ _ _ _ hlt evRec rfl xf xh xas rfl rfl hcf
            (fun a ha => hsub a (.appFn hget ha))
          have hxa_m1 := hmono evRec.heap_extends ⟨hca, fun a ha => hsub a (.appArg hget ha)⟩
          exact ⟨xs ++ [xa],
            addrIn_snoc_list (R := fun h p => KExprClosed h p ∧ ∀ a, AddrIn h p a → AddrIn h0 e0 a)
              (fun ext r => hmono ext r) evSnoc hxs hxa_m1⟩)
  intro e hd args h h' cs ev hc hsub
  exact hmain _ _ _ _ _ _ ev rfl e hd args rfl rfl hc hsub

private theorem addrIn_lower_pins {h0 : Heap F} {e0 : SourceValue F} :
    ∀ (xs : List (SourceValue F)) {ps_ptr ni r : SourceValue F} {h h' : Heap F} {cs : List (Call F)},
      ObsFn Obs.W "KernelModeled::lower_pins" [ps_ptr, ni] h r h' cs →
      RepList kexprListEnum
        (fun h _ p => KExprClosed h p ∧ ∀ a, AddrIn h p a → AddrIn h0 e0 a) h xs ps_ptr →
      ∃ ys : List (SourceValue F),
        RepList kexprListEnum
          (fun h _ p => KExprClosed h p ∧ ∀ a, AddrIn h p a → AddrIn h0 e0 a) h' ys r := by
  have hmono : ∀ {h₁ h₂ p}, Heap.Extends h₁ h₂ →
      (KExprClosed h₁ p ∧ ∀ a, AddrIn h₁ p a → AddrIn h0 e0 a) →
      (KExprClosed h₂ p ∧ ∀ a, AddrIn h₂ p a → AddrIn h0 e0 a) :=
    fun ext ⟨hc, hs⟩ => ⟨hc.mono ext, fun a ha => hs a (hc.addrIn_back ext a ha)⟩
  intro xs
  induction xs with
  | nil =>
    intro ps_ptr ni r h h' cs ev hrep
    match Obs.«KernelModeled::lower_pins».obs ev with
    | .Nil (he24 := hr) (hm23 := hh) .. => subst hr hh; exact ⟨[], .nil (by simp)⟩
    | .Cons (ld12 := ld) .. => obtain ⟨_, _, he, _, _⟩ := Lib.rep_cons_of_load hrep ld; cases he
  | cons x xs ih =>
    intro ps_ptr ni r h h' cs ev hrep
    match Obs.«KernelModeled::lower_pins».obs ev with
    | .Nil (ld12 := ld) .. => cases Lib.rep_nil_of_load hrep ld
    | .Cons (x_p := xp) (x_rest := xrest) (v109 := v109) (v110 := v110) (ld12 := ld)
        (ev70 := evHb) (he105 := hr) (hm104 := hh) (ev122 := evLow) (ev157 := evRec) .. =>
      subst hr hh
      obtain ⟨_, _, he, hpx, hrest⟩ := Lib.rep_cons_of_load hrep ld
      injection he with h1 h2; subst h1 h2
      have hpx60 := hmono evHb.heap_extends hpx
      obtain ⟨hcv, hsubv⟩ := addrIn_expr_lower_closed evLow hpx60.1
      have hv112 : KExprClosed _ v109 ∧ ∀ a, AddrIn _ v109 a → AddrIn h0 e0 a :=
        ⟨hcv, fun a ha => hpx60.2 a (hsubv a ha)⟩
      have ext_h_112 := evHb.heap_extends.trans evLow.heap_extends
      obtain ⟨ys, hys⟩ := ih evRec
        (RepLinkedList.mono (R := fun h (_ : SourceValue F) p =>
            KExprClosed h p ∧ ∀ a, AddrIn h p a → AddrIn h0 e0 a)
          (fun _ _ _ p ext r => hmono (p := p) ext r) ext_h_112 hrest)
      exact ⟨v109 :: ys,
        Lib.rep_store_cons (R := fun h (_ : SourceValue F) p =>
            KExprClosed h p ∧ ∀ a, AddrIn h p a → AddrIn h0 e0 a)
          (fun _ _ _ p ext r => hmono (p := p) ext r)
          (hmono evRec.heap_extends hv112) hys⟩

private theorem repList_zip_pred {en : String} {α β : Type}
    {R : Heap F → α → SourceValue F → Prop} {S : Heap F → β → SourceValue F → Prop} :
    ∀ {h : Heap F} {xs : List α} {ys : List β} {p : SourceValue F},
      RepList en R h xs p → RepList en S h ys p →
      RepList en (fun h a v => R h a v ∧ ∃ b, S h b v) h xs p
  | _, _, _, _, .nil c1, .nil _ => .nil c1
  | _, _, _, _, .nil c1, .cons c2 _ _ => by
    have h := Option.some.inj (c1.symm.trans c2)
    injection h with _ htag _; exact absurd htag (by decide)
  | _, _, _, _, .cons c1 _ _, .nil c2 => by
    have h := Option.some.inj (c1.symm.trans c2)
    injection h with _ htag _; exact absurd htag (by decide)
  | _, _, _, _, .cons c1 hx1 hr1, .cons c2 hx2 hr2 => by
    have h := Option.some.inj (c1.symm.trans c2)
    injection h with _ _ hargs
    injection hargs with h1 hargs; injection hargs with h2 _; subst h1 h2
    exact .cons c1 ⟨hx1, _, hx2⟩ (repList_zip_pred hr1 hr2)

/-- Every `AddrIn` of any lowered pin returned by `KernelModeled::rec_major_pins` already occurs
in the recursor's input type pointer `ty_ptr`. -/
theorem addrIn_rec_major_pins {κ : _root_.Address → KKey} {Γ : Nat → KExpr} {E : KExpr}
    {ty_ptr iaddr ilvls pins_ptr : SourceValue F} {rp ni : F} {h h' : Heap F}
    {cs : List (Call F)} {Ps : List KExpr}
    (ev : ObsFn Obs.W "KernelModeled::rec_major_pins" [ty_ptr, .field rp, .field ni] h
      (.tuple [iaddr, ilvls, pins_ptr]) h' cs)
    (hE : Decl.TmExact κ 0 Γ h 0 E ty_ptr)
    (hPs : RepList kexprListEnum (fun h P p => Decl.TmExact κ 0 Γ h (ZMod.val rp) P p) h' Ps pins_ptr) :
    RepList kexprListEnum
      (fun h P p => Decl.TmExact κ 0 Γ h (ZMod.val rp) P p ∧ ∀ a, AddrIn h p a → AddrIn h ty_ptr a)
      h' Ps pins_ptr := by
  have hmono : ∀ {h₁ h₂ p}, Heap.Extends h₁ h₂ →
      (KExprClosed h₁ p ∧ ∀ a, AddrIn h₁ p a → AddrIn h ty_ptr a) →
      (KExprClosed h₂ p ∧ ∀ a, AddrIn h₂ p a → AddrIn h ty_ptr a) :=
    fun ext ⟨hc, hs⟩ => ⟨hc.mono ext, fun a ha => hs a (hc.addrIn_back ext a ha)⟩
  match Obs.«KernelModeled::rec_major_pins».obs ev with
  | .run (x_dom := xdom) (w59 := w59) (w60 := w60) (x_h := xh) (x_args := xargs)
      (x_inp := xinp) (m297 := m297) (v386 := v386) (m389 := m389) (cs397 := cs397)
      (ev14 := evPeel) (ld51 := ldFa) (ev89 := evSp)
      (ev157 := evCi) (ev270 := evLen) (op292 := opAdd) (ev324 := evDrop) (ev309 := evIdx)
      (he359 := hr) (ev399 := evTake) (ev385 := evLow) (he423 := hh) .. =>
    subst hh
    injection hr with hl; injection hl with _ hl; injection hl with _ hl; injection hl with hp _
    subst hp
    have hcty : KExprClosed h ty_ptr := KExprClosed.of_tmExact hE
    obtain ⟨hm2, hsubPeel⟩ := addrIn_peel_n_foralls evPeel
    have hm2' := hm2.symm
    subst hm2'
    have hcv1 := kExprClosed_peel_n_foralls evPeel hcty
    obtain ⟨_, hptr1, hget1, hcdom, _⟩ := hcv1.load_forall ldFa
    obtain ⟨xs, hxs⟩ := addrIn_collect_spine evSp hcdom (fun a ha => by
      rw [hptr1] at hsubPeel
      exact hsubPeel a (.forallTy hget1 ha))
    have ext_77_297 := evCi.heap_extends.trans (evLen.heap_extends.trans
      (evDrop.heap_extends.trans evIdx.heap_extends))
    have hxs297 := RepLinkedList.mono (R := fun h1 (_ : SourceValue F) p =>
        KExprClosed h1 p ∧ ∀ a, AddrIn h1 p a → AddrIn h ty_ptr a)
      (fun _ _ _ p ext r => hmono (p := p) ext r) ext_77_297 hxs
    have hxinpf : ∃ inp : F, xinp = .field inp := by
      cases xinp with
      | field f => exact ⟨f, rfl⟩
      | _ => simp [evalBinOp] at opAdd
    obtain ⟨inp, rfl⟩ := hxinpf
    have evTake' : ObsFn Obs.W (Instance.mk "Lists::take" [(.ptr (.named "KernelTypes::KExprNode" []))]).symbol
        [xargs, .field inp] m297 v386 m389 cs397 := by
      rw [Obs.Names.«Lists::take<&KernelTypes::KExprNode>».symbol]; exact evTake
    have hxs297' : RepList (Instance.mk "Lists::Node" [(.ptr (.named "KernelTypes::KExprNode" []))]).symbol
        (fun h1 _ p => KExprClosed h1 p ∧ ∀ a, AddrIn h1 p a → AddrIn h ty_ptr a) m297 xs xargs := by
      rw [Obs.Names.«Lists::Node<&KernelTypes::KExprNode>».symbol]; exact hxs297
    have htake := (Lib.Lists.take_spec
      (R := fun h1 _ p => KExprClosed h1 p ∧ ∀ a, AddrIn h1 p a → AddrIn h ty_ptr a)
      (fun _ _ _ _ ext r => hmono ext r) evTake' hxs297').2
    rw [Obs.Names.«Lists::Node<&KernelTypes::KExprNode>».symbol] at htake
    obtain ⟨ys, hys⟩ := addrIn_lower_pins (xs.take inp.val) evLow htake
    have hzip := repList_zip_pred hPs hys
    have hfinal : ∀ {l : List KExpr} {p : SourceValue F},
        RepList kexprListEnum (fun h1 P p => Decl.TmExact κ 0 Γ h1 (ZMod.val rp) P p ∧
          ∃ _ : SourceValue F, KExprClosed h1 p ∧ ∀ a, AddrIn h1 p a → AddrIn h ty_ptr a) h' l p →
        RepList kexprListEnum (fun h1 P p => Decl.TmExact κ 0 Γ h1 (ZMod.val rp) P p ∧
          ∀ a, AddrIn h1 p a → AddrIn h1 ty_ptr a) h' l p := by
      intro l p hr
      induction hr with
      | nil c => exact .nil c
      | cons c hx _ ih =>
        exact .cons c ⟨hx.1, fun a ha => Binding.AddrIn.mono' ev.heap_extends (hx.2.choose_spec.2 a ha)⟩ ih
    exact hfinal hzip

/-! ## `LeavesFixed` for instantiated major pins from `CheckRecsCons` -/

private theorem stripPis_instantiateLevelParams (ks : List LevelParam) (us : List KLevel) :
    ∀ (m : Nat) (e : KExpr),
      (e.instantiateLevelParams ks us).stripPis m =
        (e.stripPis m).map fun (bs, rem) =>
          (bs.map fun (d, bm) => (d.instantiateLevelParams ks us,
            { pw := Level.substPW ks us bm.pw, display := bm.display }),
           rem.instantiateLevelParams ks us)
  | 0, e => rfl
  | m + 1, .forallE T B bm => by
    simp only [Expr.instantiateLevelParams, Expr.stripPis, stripPis_instantiateLevelParams ks us m B]
    cases B.stripPis m <;> rfl
  | _ + 1, .bvar _ | _ + 1, .fvar _ _ | _ + 1, .sort _ | _ + 1, .const _ _ | _ + 1, .app _ _
  | _ + 1, .lam _ _ _ | _ + 1, .letE _ _ _ _ | _ + 1, .lit _ | _ + 1, .proj _ _ _ => rfl

private theorem stripPis_renameConsts (g : KKey → KKey) :
    ∀ (m : Nat) (e : KExpr),
      (e.renameConsts g).stripPis m =
        (e.stripPis m).map fun (bs, rem) =>
          (bs.map fun (d, bm) => (d.renameConsts g, bm), rem.renameConsts g)
  | 0, e => rfl
  | m + 1, .forallE T B bm => by
    simp only [Expr.renameConsts, Expr.stripPis, stripPis_renameConsts g m B]
    cases B.stripPis m <;> rfl
  | _ + 1, .bvar _ | _ + 1, .fvar _ _ | _ + 1, .sort _ | _ + 1, .const _ _ | _ + 1, .app _ _
  | _ + 1, .lam _ _ _ | _ + 1, .letE _ _ _ _ | _ + 1, .lit _ | _ + 1, .proj _ _ _ => rfl

private theorem getAppFn_instantiateLevelParams (ks : List LevelParam) (us : List KLevel) :
    ∀ e : KExpr, (e.instantiateLevelParams ks us).getAppFn = (e.getAppFn).instantiateLevelParams ks us
  | .app f a => by
    simp only [Expr.instantiateLevelParams, Expr.getAppFn]
    exact getAppFn_instantiateLevelParams ks us f
  | .bvar _ | .fvar _ _ | .sort _ | .const _ _ | .lam _ _ _ | .forallE _ _ _
  | .letE _ _ _ _ | .lit _ | .proj _ _ _ => rfl

private theorem getAppArgs_instantiateLevelParams (ks : List LevelParam) (us : List KLevel) :
    ∀ e : KExpr,
      (e.instantiateLevelParams ks us).getAppArgs =
        e.getAppArgs.map (·.instantiateLevelParams ks us)
  | .app f a => by
    simp only [Expr.instantiateLevelParams, Expr.getAppArgs,
      getAppArgs_instantiateLevelParams ks us f, List.map_append, List.map_singleton]
  | .bvar _ | .fvar _ _ | .sort _ | .const _ _ | .lam _ _ _ | .forallE _ _ _
  | .letE _ _ _ _ | .lit _ | .proj _ _ _ => rfl

private theorem lowerBVars_instantiateLevelParams (ks : List LevelParam) (us : List KLevel)
    (s : Nat) :
    ∀ (c : Nat) (e : KExpr),
      (e.instantiateLevelParams ks us).lowerBVars s c =
        (e.lowerBVars s c).instantiateLevelParams ks us
  | c, .bvar i => by
    simp only [Expr.instantiateLevelParams, Expr.lowerBVars]
    split <;> rfl
  | _, .fvar _ _ | _, .sort _ | _, .const _ _ | _, .lit _ => rfl
  | c, .app f a => by
    simp [Expr.instantiateLevelParams, Expr.lowerBVars,
      lowerBVars_instantiateLevelParams ks us s c f,
      lowerBVars_instantiateLevelParams ks us s c a]
  | c, .lam t b _ | c, .forallE t b _ => by
    simp [Expr.instantiateLevelParams, Expr.lowerBVars,
      lowerBVars_instantiateLevelParams ks us s c t,
      lowerBVars_instantiateLevelParams ks us s (c + 1) b]
  | c, .letE t v b _ => by
    simp [Expr.instantiateLevelParams, Expr.lowerBVars,
      lowerBVars_instantiateLevelParams ks us s c t,
      lowerBVars_instantiateLevelParams ks us s c v,
      lowerBVars_instantiateLevelParams ks us s (c + 1) b]
  | c, .proj _ _ e => by
    simp [Expr.instantiateLevelParams, Expr.lowerBVars,
      lowerBVars_instantiateLevelParams ks us s c e]

private theorem hasFvar_stripPis :
    ∀ (m : Nat) {e : KExpr} {bs : List (KExpr × Ix.Kernel.BinderMeta)} {rem : KExpr},
      e.hasFvar = false → e.stripPis m = some (bs, rem) → rem.hasFvar = false
  | 0, _, _, _, hf, hs => by injection hs with hp; injection hp with _ h; subst h; exact hf
  | m + 1, .forallE T B _, _, _, hf, hs => by
    simp only [Expr.hasFvar, Bool.or_eq_false_iff] at hf
    simp only [Expr.stripPis] at hs
    cases hsb : B.stripPis m with
    | none => simp [hsb] at hs
    | some p =>
      rw [hsb] at hs; injection hs with hp; injection hp with _ h; subst h
      exact hasFvar_stripPis m hf.2 hsb
  | _ + 1, .bvar _, _, _, _, hs | _ + 1, .fvar _ _, _, _, _, hs | _ + 1, .sort _, _, _, _, hs
  | _ + 1, .const _ _, _, _, _, hs | _ + 1, .app _ _, _, _, _, hs | _ + 1, .lam _ _ _, _, _, _, hs
  | _ + 1, .letE _ _ _ _, _, _, _, hs | _ + 1, .lit _, _, _, _, hs | _ + 1, .proj _ _ _, _, _, _, hs =>
    nomatch hs

private theorem hasFvar_getAppArgs :
    ∀ (e : KExpr), e.hasFvar = false → ∀ a ∈ e.getAppArgs, a.hasFvar = false
  | .app f x, hf, a, ha => by
    simp only [Expr.hasFvar, Bool.or_eq_false_iff] at hf
    simp only [Expr.getAppArgs, List.mem_append, List.mem_singleton] at ha
    rcases ha with ha | rfl
    · exact hasFvar_getAppArgs f hf.1 a ha
    · exact hf.2
  | .bvar _, _, _, ha | .fvar _ _, _, _, ha | .sort _, _, _, ha | .const _ _, _, _, ha
  | .lam _ _ _, _, _, ha | .forallE _ _ _, _, _, ha | .letE _ _ _ _, _, _, ha | .lit _, _, _, ha
  | .proj _ _ _, _, _, ha => nomatch ha

private theorem hasFvar_lowerBVars (s : Nat) :
    ∀ (c : Nat) (e : KExpr), (e.lowerBVars s c).hasFvar = e.hasFvar
  | c, .bvar i => by simp only [Expr.lowerBVars]; split <;> rfl
  | _, .fvar _ _ | _, .sort _ | _, .const _ _ | _, .lit _ => rfl
  | c, .app f a => by simp [Expr.lowerBVars, Expr.hasFvar, hasFvar_lowerBVars s c f, hasFvar_lowerBVars s c a]
  | c, .lam t b _ | c, .forallE t b _ => by
    simp [Expr.lowerBVars, Expr.hasFvar, hasFvar_lowerBVars s c t, hasFvar_lowerBVars s (c + 1) b]
  | c, .letE t v b _ => by
    simp [Expr.lowerBVars, Expr.hasFvar, hasFvar_lowerBVars s c t, hasFvar_lowerBVars s c v,
      hasFvar_lowerBVars s (c + 1) b]
  | c, .proj _ _ e => by simp [Expr.lowerBVars, Expr.hasFvar, hasFvar_lowerBVars s c e]

private theorem leavesFixed_of_renameConsts_eq {g : KKey → KKey} :
    ∀ {e : KExpr}, e.renameConsts g = e → LeavesFixed g e
  | .bvar _, _, _, hl => by simp [Expr.fvarLeaves] at hl
  | .sort _, _, _, hl => by simp [Expr.fvarLeaves] at hl
  | .const _ _, _, _, hl => by simp [Expr.fvarLeaves] at hl
  | .lit _, _, _, hl => by simp [Expr.fvarLeaves] at hl
  | .fvar i ty, heq, l, hl => by
    simp only [Expr.renameConsts] at heq; injection heq with _ hty
    simp only [Expr.fvarLeaves, List.mem_cons] at hl
    rcases hl with rfl | hl'
    · exact hty
    · exact leavesFixed_of_renameConsts_eq hty l hl'
  | .app f a, heq, l, hl => by
    simp only [Expr.renameConsts] at heq; injection heq with hf ha
    simp only [Expr.fvarLeaves, List.mem_append] at hl
    rcases hl with hl | hl
    · exact leavesFixed_of_renameConsts_eq hf l hl
    · exact leavesFixed_of_renameConsts_eq ha l hl
  | .lam t b _, heq, l, hl | .forallE t b _, heq, l, hl => by
    simp only [Expr.renameConsts] at heq; injection heq with ht hb
    simp only [Expr.fvarLeaves, List.mem_append] at hl
    rcases hl with hl | hl
    · exact leavesFixed_of_renameConsts_eq ht l hl
    · exact leavesFixed_of_renameConsts_eq hb l hl
  | .letE t v b _, heq, l, hl => by
    simp only [Expr.renameConsts] at heq; injection heq with ht hv hb
    simp only [Expr.fvarLeaves, List.mem_append] at hl
    rcases hl with (hl | hl) | hl
    · exact leavesFixed_of_renameConsts_eq ht l hl
    · exact leavesFixed_of_renameConsts_eq hv l hl
    · exact leavesFixed_of_renameConsts_eq hb l hl
  | .proj _ _ e, heq, l, hl => by
    simp only [Expr.renameConsts] at heq; injection heq with _ _ he
    simp only [Expr.fvarLeaves] at hl
    exact leavesFixed_of_renameConsts_eq he l hl

private theorem noProjIn_instantiateLevelParams {bad : List KKey} (ks : List LevelParam)
    (us : List KLevel) :
    ∀ e : KExpr, Decl.NoProjIn bad (e.instantiateLevelParams ks us) = Decl.NoProjIn bad e
  | .bvar _ | .sort _ | .const _ _ | .lit _ => rfl
  | .fvar _ ty => noProjIn_instantiateLevelParams ks us ty
  | .app f a => by
    simp [Expr.instantiateLevelParams, Decl.NoProjIn,
      noProjIn_instantiateLevelParams ks us f, noProjIn_instantiateLevelParams ks us a]
  | .lam t b _ | .forallE t b _ => by
    simp [Expr.instantiateLevelParams, Decl.NoProjIn,
      noProjIn_instantiateLevelParams ks us t, noProjIn_instantiateLevelParams ks us b]
  | .letE t v b _ => by
    simp [Expr.instantiateLevelParams, Decl.NoProjIn,
      noProjIn_instantiateLevelParams ks us t, noProjIn_instantiateLevelParams ks us v,
      noProjIn_instantiateLevelParams ks us b]
  | .proj _ _ e => by
    simp [Expr.instantiateLevelParams, Decl.NoProjIn, noProjIn_instantiateLevelParams ks us e]

private theorem openPisAtFvars_mem_isFvar :
    ∀ (m : Nat) {e rem : KExpr} {i : Nat} {fvs : List KExpr},
      openPisAtFvars m e i = some (fvs, rem) →
      ∀ fv ∈ fvs, ∃ j T, fv = .fvar j T
  | 0, _, _, _, _, hop, _, hfv => by
    injection hop with hp; injection hp with hf _; subst hf; exact nomatch hfv
  | m + 1, .forallE T B _, _, i, _, hop, fv, hfv => by
    simp only [openPisAtFvars] at hop
    cases hb : openPisAtFvars m (B.instantiate1 (.fvar i T)) (i + 1) with
    | none => simp [hb] at hop
    | some p =>
      rw [hb] at hop; injection hop with hp; injection hp with hf _; subst hf
      rcases List.mem_cons.mp hfv with rfl | hfv'
      · exact ⟨i, T, rfl⟩
      · exact openPisAtFvars_mem_isFvar m hb fv hfv'
  | _ + 1, .bvar _, _, _, _, hop, _, _ | _ + 1, .fvar _ _, _, _, _, hop, _, _
  | _ + 1, .sort _, _, _, _, hop, _, _ | _ + 1, .const _ _, _, _, _, hop, _, _
  | _ + 1, .app _ _, _, _, _, hop, _, _ | _ + 1, .lam _ _ _, _, _, _, hop, _, _
  | _ + 1, .letE _ _ _ _, _, _, _, hop, _, _ | _ + 1, .lit _, _, _, _, hop, _, _
  | _ + 1, .proj _ _ _, _, _, _, hop, _, _ => nomatch hop

/-- **From `CheckRecsCons`'s parameter-domain comparison (`peel_collect` + `rename` +
`spec_params_ptr_eq`) and pin lowering (`rec_major_pins` + `lower_pins`), every instantiated
major-premise pin satisfies `LeavesFixed g`.** -/
theorem pinsP_leavesFixed {t : Ix.Kernel.RoleTable} {calls : List (Call F)}
    {rc tys recs models src dst aset s n k np uo bnl fam form r : SourceValue F}
    {h h' : Heap F}
    (ht : t.check = .ok ()) (hbd : Bounded calls)
    {srcAs dstAs : List Bytes.Address} (hlenSD : srcAs.length = dstAs.length)
    (C : CheckRecsCons rc tys recs models src dst aset s n k np uo bnl fam form r h h' calls)
    {nP nMot nMin nI cnP : Nat}
    (hnp_eq : np = .field (nP : F)) (hn_eq : n = .field (nMot : F))
    (hnmin_eq : C.nmin = .field (nMin : F)) (hni_eq : C.ni = .field (nI : F))
    (hnp_lt : nP < 72057594037927936) (hnmot_lt : nMot < 72057594037927936)
    (hnmin_lt : nMin < 72057594037927936) (hni_lt : nI < 72057594037927936)
    (hsrc : RepList addrListEnum (Bytes.RepAddressRef addrTy) h srcAs src)
    (hdst : RepList addrListEnum (Bytes.RepAddressRef addrTy) h dstAs dst)
    {ps : List LevelParam} (hperm : ps.Perm (List.range ps.length))
    {tyA : KExpr} {lvls : List Level} {pins : List KExpr}
    (htyA_fv : tyA.hasFvar = false)
    (hnp_ty : Decl.NoProjIn (srcAs.map fun b => Core.keyOf t (ixAddr b)) tyA = true)
    (htm_ty : Decl.TmExact (Core.keyOf t) 0 zeroGhost C.m67 0 (Core.posOf ps tyA) C.ty)
    (hmaj : majorShape tyA (nP + nMot + nMin + nI) (nP + nMot + nMin) cnP = some (lvls, pins)) :
    ∀ fvsP crest2, openPisAtFvars (nP + nMot + nMin) tyA 0 = some (fvsP, crest2) →
      ∀ p ∈ pins, LeavesFixed (aliasMap ((srcAs.map fun b => Core.keyOf t (ixAddr b)).zip
        (dstAs.map fun b => Core.keyOf t (ixAddr b))))
        (Expr.instSpine (fvsP.take (nP + nMot + nMin)) (nP + nMot + nMin - 1) p) := by
  have htwf : t.wf = true := by unfold Ix.Kernel.RoleTable.wf; rw [ht]; rfl
  have hmod : Aiur.Library.U32.Goldilocks.modulus = 18446744069414584321 := rfl
  let srcKeys := srcAs.map fun b => Core.keyOf t (ixAddr b)
  let dstKeys := dstAs.map fun b => Core.keyOf t (ixAddr b)
  let g := aliasMap (srcKeys.zip dstKeys)
  have eNil1 : Heap.Extends C.m561 C.mNil1 := by rw [C.hNil1]; exact Heap.Extends.snoc _ _
  have eNil2 : Heap.Extends C.mRen C.mNil2 := by rw [C.hNil2]; exact Heap.Extends.snoc _ _
  have ext_67_561 : Heap.Extends C.m67 C.m561 :=
    C.ext391.trans (C.evCarriers.extends.trans (C.evScope.extends.trans C.evNoMent.extends))
  have ext_67_Nil1 : Heap.Extends C.m67 C.mNil1 := ext_67_561.trans eNil1
  have ext_67_P1 : Heap.Extends C.m67 C.mP1 := ext_67_Nil1.trans C.evPeel1.extends
  have ext_h_P1 : Heap.Extends h C.mP1 := C.evGetRec.extends.trans ext_67_P1
  -- Step 1: `peel_collect` on `ty` and on `rename(ty)`, then `spec_params_ptr_eq = 1`.
  have hnp_val : ZMod.val (nP : F) = nP := SubstAux.val_natCast (by omega)
  have hnil1 : RepList kexprListEnum
      (fun h D p => Decl.TmExact (Core.keyOf t) 0 zeroGhost h (0 + nP) D p)
      C.mNil1 [] (.ptr (.enum kexprListEnum) C.m561.length) :=
    .nil (by rw [C.hNil1]; simp)
  have evP1 : ObsFn Obs.W "KernelModeled::peel_collect"
      [C.ty, .field (nP : F), .ptr (.enum kexprListEnum) C.m561.length]
      C.mNil1 (.tuple [C.wPeel1, C.pd]) C.mP1 C.evPeel1.cs := by
    rw [← hnp_eq]; exact C.evPeel1.obs
  obtain ⟨bs1, rem1, hstrip1, hpd⟩ :=
    peel_collect_doms_exact nP hnp_val evP1 (htm_ty.mono ext_67_Nil1) hnil1
  have hrenTm := rename_aliasMap (Γ₂ := zeroGhost) htwf C.evRen.obs hlenSD
    (RepLinkedList.mono (Bytes.repAddressRef_heapMono₂ addrTy) ext_h_P1 hsrc)
    (RepLinkedList.mono (Bytes.repAddressRef_heapMono₂ addrTy) ext_h_P1 hdst)
    (htm_ty.mono ext_67_P1)
  have hnil2 : RepList kexprListEnum
      (fun h D p => Decl.TmExact (Core.keyOf t) 0 zeroGhost h (0 + nP) D p)
      C.mNil2 [] (.ptr (.enum kexprListEnum) C.mRen.length) :=
    .nil (by rw [C.hNil2]; simp)
  have evP2 : ObsFn Obs.W "KernelModeled::peel_collect"
      [C.ren, .field (nP : F), .ptr (.enum kexprListEnum) C.mRen.length]
      C.mNil2 (.tuple [C.wPeel2, C.pdm]) C.mP2 C.evPeel2.cs := by
    rw [← hnp_eq]; exact C.evPeel2.obs
  obtain ⟨bs2, rem2, hstrip2, hpdm⟩ :=
    peel_collect_doms_exact nP hnp_val evP2 (hrenTm.mono eNil2) hnil2
  have hpd_P2 := RepLinkedList.mono (fun _ _ _ _ e x => x.mono e)
    (C.evRen.extends.trans (eNil2.trans C.evPeel2.extends)) hpd
  have hdoms_rev_eq : bs1.reverse.map Prod.fst ++ [] = bs2.reverse.map Prod.fst ++ [] :=
    Decl.spec_params_ptr_eq_one hpd_P2 hpdm C.evParamEq.obs
  simp only [List.append_nil] at hdoms_rev_eq
  -- Connect `renameAll g (posOf ps tyA)` to `(posOf ps tyA).renameConsts g`.
  have hg_out : ∀ k', srcKeys.contains k' = false → g k' = k' := fun k' hk' =>
    aliasMap_out_of_zip (ks := srcKeys) (ds := dstKeys) hk'
  have hrenAll_eq : Decl.renameAll g (Core.posOf ps tyA) = (Core.posOf ps tyA).renameConsts g := by
    refine Decl.renameAll_eq_renameConsts_of_noProjIn hg_out ?_
    unfold Core.posOf; rw [noProjIn_instantiateLevelParams]; exact hnp_ty
  rw [hrenAll_eq, stripPis_renameConsts, hstrip1] at hstrip2
  simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hstrip2
  obtain ⟨hbs2_eq, -⟩ := hstrip2
  subst hbs2_eq
  -- Deduce `d.renameConsts g = d` for every domain `d` of the first `nP` binders of `tyA`.
  have hstrip_orig : ∃ bs0 rem0, tyA.stripPis nP = some (bs0, rem0) ∧
      bs1.map Prod.fst = (bs0.map Prod.fst).map (Core.posOf ps) := by
    unfold Core.posOf at hstrip1
    rw [stripPis_instantiateLevelParams] at hstrip1
    cases hso : tyA.stripPis nP with
    | none => simp [hso] at hstrip1
    | some p =>
      rw [hso] at hstrip1
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hstrip1
      refine ⟨p.1, p.2, rfl, ?_⟩
      rw [← hstrip1.1, List.map_map, List.map_map]; rfl
  obtain ⟨bs0, rem0, hstrip0, hbs1_fst⟩ := hstrip_orig
  have hdoms_map_eq :
      (bs0.map Prod.fst).map (Core.posOf ps) =
        ((bs0.map Prod.fst).map (Core.posOf ps)).map (·.renameConsts g) := by
    have h1 := congrArg List.reverse hdoms_rev_eq
    simp only [← List.map_reverse, List.reverse_reverse, List.map_map] at h1
    have h2 : bs1.map Prod.fst = (bs1.map Prod.fst).map (·.renameConsts g) := by
      simpa [List.map_map, Function.comp] using h1
    rwa [hbs1_fst] at h2
  have hdoms_fixed : ∀ d ∈ bs0.map Prod.fst, d.renameConsts g = d := by
    intro d hd
    have hlen_l : ∀ (l : List KExpr), l = l.map (·.renameConsts g) →
        ∀ x ∈ l, x.renameConsts g = x := by
      intro l hl x hx
      induction l with
      | nil => cases hx
      | cons y ys ih =>
        simp only [List.map_cons, List.cons.injEq] at hl
        rcases List.mem_cons.mp hx with rfl | hx'
        · exact hl.1.symm
        · exact ih hl.2 hx'
    have hpos_eq := hlen_l _ hdoms_map_eq (Core.posOf ps d) (List.mem_map.mpr ⟨d, hd, rfl⟩)
    have hcomm : (Core.posOf ps d).renameConsts g = Core.posOf ps (d.renameConsts g) := by
      unfold Core.posOf
      exact (Decl.instantiateLevelParams_renameConsts ps (Core.posLevels ps) g d).symm
    rw [hcomm] at hpos_eq
    exact Decl.posOf_inj hperm hpos_eq
  -- Step 2: `rec_major_pins` + `lower_pins` proves `noLooseIn 0 (nMot + nMin) p = true` for `p ∈ pins`.
  have hrp_eq : C.rp = .field ((nP + nMot + nMin : Nat) : F) := by
    have hop1 : evalBinOp .add (.field (nP : F)) (.field (nMot : F)) = .ok C.xNpN := by
      rw [← hnp_eq, ← hn_eq]; exact C.opNpN
    have hx := SubstAux.add_ok hop1
    have hop2 : evalBinOp .add (.field ((nP : F) + (nMot : F))) (.field (nMin : F)) = .ok C.rp := by
      rw [← hx, ← hnmin_eq]; exact C.opRp
    rw [SubstAux.add_ok hop2]; push_cast; rfl
  have hnm_eq : C.nmotNmin = .field ((nMot + nMin : Nat) : F) := by
    have hop3 : evalBinOp .add (.field (nMot : F)) (.field (nMin : F)) = .ok C.nmotNmin := by
      rw [← hn_eq, ← hnmin_eq]; exact C.opNmotNmin
    rw [SubstAux.add_ok hop3]; push_cast; rfl
  have ext_67_Eq : Heap.Extends C.m67 C.mEq :=
    ext_67_P1.trans (C.evRen.extends.trans (eNil2.trans (C.evPeel2.extends.trans C.evParamEq.extends)))
  have evPins' : ObsFn Obs.W "KernelModeled::rec_major_pins"
      [C.ty, .field ((nP + nMot + nMin : Nat) : F), .field (nI : F)] C.mEq
      (.tuple [C.wP1, C.wP2, C.pins]) C.mPins C.evPins.cs := by
    rw [← hrp_eq, ← hni_eq]; exact C.evPins.obs
  have hrp_val : ZMod.val ((nP + nMot + nMin : Nat) : F) = nP + nMot + nMin :=
    SubstAux.val_natCast (by omega)
  have hni_val : ZMod.val (nI : F) = nI := SubstAux.val_natCast (by omega)
  obtain ⟨_, _, _, _, inpF, bsP, domP, bodyP, mMajP, lvlsP, AsP, htupP, _, _, hstripP,
      hfnP, hargsP, _, _, _, _, hpins_rep, hAsP_len⟩ :=
    Decl.rec_major_pins_spec_wide (bounded_sub C.evPins.sub hbd)
      (by rw [hrp_val]; omega) (by rw [hni_val]; omega) evPins' (htm_ty.mono ext_67_Eq)
  injection htupP with hl; injection hl with _ hl; injection hl with _ hl; injection hl with hpins_eq _
  subst hpins_eq
  have evLP' : ObsFn Obs.W "KernelModeled::lower_pins"
      [C.pins, .field ((nMot + nMin : Nat) : F)] C.mPins C.vLower C.mLP C.evLowerPins.cs := by
    rw [← hnm_eq]; exact C.evLowerPins.obs
  have hnm_val : ZMod.val ((nMot + nMin : Nat) : F) = nMot + nMin := SubstAux.val_natCast (by omega)
  rw [hrp_val, show nP + nMot + nMin = nP + ZMod.val ((nMot + nMin : Nat) : F) by omega] at hpins_rep
  obtain ⟨hnoLoose_pos, _⟩ :=
    Decl.lower_pins_spec (bounded_sub C.evLowerPins.sub hbd) (by rw [hnm_val]; omega) evLP' hpins_rep
  -- Relate `pins` (from `majorShape`) to `(AsP.take inpF.val).map (Expr.lowerBVars nI 0)`.
  unfold majorShape at hmaj
  rw [ite_eq_left_iff.mpr (fun hn => absurd (by omega) hn),
    show nP + nMot + nMin + nI - (nP + nMot + nMin) = nI by omega] at hmaj
  cases hsm : tyA.stripPis (nP + nMot + nMin + nI) with
  | none => simp [hsm] at hmaj
  | some q =>
    rw [hsm] at hmaj
    rcases q with ⟨bsM, remM⟩
    cases remM with
    | forallE domM bodyM bmM =>
      dsimp only at hmaj
      cases hfnM : domM.getAppFn with
      | const T lvlsM =>
        rw [hfnM] at hmaj
        dsimp only at hmaj
        split at hmaj
        · next hcond =>
          injection hmaj with hpair; injection hpair with hlvls_eq hpins_orig_eq
          subst hlvls_eq hpins_orig_eq
          -- Match `hstripP` with `hsm` under `posOf ps`
          rw [hrp_val, hni_val] at hstripP
          have hdom_eq : domP = Core.posOf ps domM := by
            have hsm_pos : (Core.posOf ps tyA).stripPis (nP + nMot + nMin + nI) =
                some (bsM.map (fun (d, bm) => (Core.posOf ps d,
                  { pw := Level.substPW ps (Core.posLevels ps) bm.pw, display := bm.display })),
                  .forallE (Core.posOf ps domM) (Core.posOf ps bodyM)
                    { pw := Level.substPW ps (Core.posLevels ps) bmM.pw, display := bmM.display }) := by
              unfold Core.posOf; rw [stripPis_instantiateLevelParams, hsm]; rfl
            have h := Option.some.inj (hstripP.symm.trans hsm_pos)
            exact (Expr.forallE.inj (Prod.mk.inj h).2).1
          have hAsP_eq : AsP = domM.getAppArgs.map (Core.posOf ps) := by
            rw [← hargsP, hdom_eq]; exact getAppArgs_instantiateLevelParams _ _ domM
          have hlen_As : domM.getAppArgs.length = cnP + nI := hcond.1
          have hinp_eq : ZMod.val inpF = cnP := by
            have h1 : AsP.length = domM.getAppArgs.length := by rw [hAsP_eq, List.length_map]
            rw [hni_val] at hAsP_len
            omega
          have hnoLoose_orig : ∀ p ∈ (domM.getAppArgs.take cnP).map (Expr.lowerBVars nI 0),
              Decl.noLooseIn 0 (nMot + nMin) p = true ∧ p.hasFvar = false := by
            intro p hp
            obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hp
            have hpos_mem : (Core.posOf ps a).lowerBVars nI 0 ∈
                (AsP.take (ZMod.val inpF)).map (Expr.lowerBVars (ZMod.val (nI : F)) 0) := by
              rw [hni_val, hinp_eq, hAsP_eq, ← List.map_take]
              exact List.mem_map.mpr ⟨Core.posOf ps a, List.mem_map.mpr ⟨a, ha, rfl⟩, rfl⟩
            have hnl := hnoLoose_pos _ hpos_mem
            rw [hnm_val] at hnl
            unfold Core.posOf at hnl
            rw [lowerBVars_instantiateLevelParams, noLooseIn_instantiateLevelParams] at hnl
            have hrem_fv := hasFvar_stripPis _ htyA_fv hsm
            simp only [Expr.hasFvar, Bool.or_eq_false_iff] at hrem_fv
            have ha_fv := hasFvar_getAppArgs domM hrem_fv.1 a (List.mem_of_mem_take ha)
            exact ⟨hnl, by rw [hasFvar_lowerBVars]; exact ha_fv⟩
          -- Step 3: conclude `LeavesFixed g` for every `openPisAtFvars (nP + nMot + nMin) tyA 0`.
          intro fvsP crest2 hopen p hp
          have hlen_fvs : fvsP.length = nP + nMot + nMin :=
            Decl.openPisAtFvars_len (nP + nMot + nMin) hopen
          have htake_eq : fvsP.take (nP + nMot + nMin) = fvsP := List.take_of_length_le (by omega)
          rw [htake_eq]
          have hsplit := Decl.openPisAtFvars_split nP (nMot + nMin) tyA 0
          rw [show nP + (nMot + nMin) = nP + nMot + nMin by omega, hopen] at hsplit
          cases hop1 : openPisAtFvars nP tyA 0 with
          | none => simp [hop1] at hsplit
          | some q1 =>
            rcases q1 with ⟨fvs1, r1⟩
            rw [hop1] at hsplit
            simp only [Nat.zero_add] at hsplit
            cases hop2 : openPisAtFvars (nMot + nMin) r1 nP with
            | none => simp [hop2] at hsplit
            | some q2 =>
              rcases q2 with ⟨fvs2, r2⟩
              simp [hop2] at hsplit
              have hfvs_eq : fvs1 ++ fvs2 = fvsP := hsplit.1.symm
              have hlen1 : fvs1.length = nP := Decl.openPisAtFvars_len nP hop1
              have htake_np : fvsP.take nP = fvs1 := by
                rw [← hfvs_eq, List.take_left' hlen1]
              obtain ⟨hno_p, hfv_p⟩ := hnoLoose_orig p hp
              rw [show nP + nMot + nMin = nP + (nMot + nMin) by omega]
              refine leavesFixed_instSpine_of_noLooseIn (np := nP) (k := nMot + nMin)
                (by omega) ?_ hfv_p hno_p
              intro fv hfv
              rw [htake_np] at hfv
              obtain ⟨j, T, rfl⟩ := openPisAtFvars_mem_isFvar nP hop1 fv hfv
              exact ⟨rfl, leavesFixed_of_renameConsts_eq
                (openPisAtFvars_fixed_of_doms_fixed nP tyA 0 hstrip0 hdoms_fixed hop1 _ hfv)⟩
        · simp at hmaj
      | _ => simp [hfnM] at hmaj
    | _ => simp at hmaj

/-! ## Inductive loads, rule scope calls, and the `check_rules_go` trace walk -/

/-- When `Ingress::get_ci` returns an `Induct` value, the loaded record is an `.iPrj` projection
record stored in `E₀`, whose parent block record is also stored in `E₀` with the inductive member
and exact field bounds. -/
theorem get_ci_induct_record {calls : List (Call F)} {E₀ : Ixon.Env}
    (hbd : Bounded calls) (hS : LoadedReads.RunStore calls E₀)
    (hH : LoadedReads.HashedRecordsStored calls E₀)
    {a : Bytes.Address} {xa ptr w1 w2 x_inp x_ini x_inct w3 x_iblk x_iidx : SourceValue F}
    {h h' : Heap F} {cs : List (Call F)}
    (hsub : CallSub cs calls)
    (ha : Bytes.RepAddressRef addrTy h a xa)
    (ev : ObsFn Obs.W "Ingress::get_ci" [xa] h ptr h' cs)
    (hld : loadValue h' ptr = .ok (.construct kciEnum "Induct"
      [w1, w2, x_inp, x_ini, x_inct, w3, x_iblk, x_iidx])) :
    ∃ (cm : Ixon.Constant) (ip : Ixon.InductiveProj) (cbM : Ixon.Constant)
      (msM : Array Ixon.MutConst) (indM : Ixon.Inductive) (bBlkM : Bytes.Address),
      recordOf E₀ (ixAddr a) = some cm ∧
      cm.info = .iPrj ip ∧
      cm = memberProjection ip.block ip.idx.toNat (.indc indM) ∧
      ixAddr a = memberAddr ip.block ip.idx.toNat (.indc indM) ∧
      recordOf E₀ ip.block = some cbM ∧
      cbM.info = .muts msM ∧
      msM[ip.idx.toNat]? = some (.indc indM) ∧
      ip.idx.toNat < 72057594037927936 ∧
      indM.params.toNat < 72057594037927936 ∧
      indM.indices.toNat < 72057594037927936 ∧
      indM.ctors.size < 72057594037927936 ∧
      x_inp = .field (indM.params.toNat : F) ∧
      x_ini = .field (indM.indices.toNat : F) ∧
      x_inct = .field (indM.ctors.size : F) ∧
      Bytes.RepAddressRef addrTy h' bBlkM x_iblk ∧
      ixAddr bBlkM = ip.block ∧
      x_iidx = .field (ip.idx.toNat : F) := by
  -- Step 1: `L1.get_ci_spec` identifies `c.info = .iPrj ip` from the `"Induct"` tag.
  obtain ⟨-, rawBytes, cm, blobs, hh, hba, hex, -, htv, -, hraw⟩ :=
    L1.get_ci_spec (bounded_sub hsub hbd) ha ev
  have hip : ∃ ip : Ixon.InductiveProj, cm.info = .iPrj ip := by
    unfold L1.GetCIRawResult at hraw
    cases hinfo : cm.info with
    | iPrj ip => exact ⟨ip, rfl⟩
    | defn d =>
      rw [hinfo] at hraw; obtain ⟨v, hldv, _, _, _, _, hv, _, _⟩ := hraw
      have he := Except.ok.inj (hld.symm.trans hldv); rw [hv] at he
      unfold L1.defnValShape at he
      cases hdk : d.kind <;> simp [hdk] at he
    | axio ax =>
      rw [hinfo] at hraw; obtain ⟨v, hldv, _, _, hv, _⟩ := hraw
      have he := Except.ok.inj (hld.symm.trans hldv); rw [hv] at he
      injection he with _ ht _; exact absurd ht (by decide)
    | quot q =>
      rw [hinfo] at hraw; obtain ⟨v, hldv, _, _, hv, _⟩ := hraw
      have he := Except.ok.inj (hld.symm.trans hldv); rw [hv] at he
      injection he with _ ht _; exact absurd ht (by decide)
    | recr rc =>
      rw [hinfo] at hraw; obtain ⟨v, hldv, _, _, _, _, _, _, _, _, _, _, _, _, hv, _, _⟩ := hraw
      have he := Except.ok.inj (hld.symm.trans hldv); rw [hv] at he
      injection he with _ ht _; exact absurd ht (by decide)
    | dPrj p =>
      rw [hinfo] at hraw
      obtain ⟨_, _, _, _, d, v, _, _, _, _, _, _, hldv, _, _, _, _, hv, _, _⟩ := hraw
      have he := Except.ok.inj (hld.symm.trans hldv); rw [hv] at he
      unfold L1.defnValShape at he
      cases hdk : d.kind <;> simp [hdk] at he
    | cPrj p =>
      rw [hinfo] at hraw
      obtain ⟨_, _, _, _, _, _, _, v, _, _, _, _, _, _, _, hldv, _, _, _, _, _, _, _, _, _, _, hv, _⟩ := hraw
      have he := Except.ok.inj (hld.symm.trans hldv); rw [hv] at he
      injection he with _ ht _; exact absurd ht (by decide)
    | rPrj p =>
      rw [hinfo] at hraw
      obtain ⟨_, _, _, _, _, _, v, _, _, _, _, _, hldv, _, _, _, _, _, _, _, _, _, _, _, _, hv, _, _⟩ := hraw
      have he := Except.ok.inj (hld.symm.trans hldv); rw [hv] at he
      injection he with _ ht _; exact absurd ht (by decide)
    | muts ms => rw [hinfo] at hraw; exact hraw.elim
  obtain ⟨ip, hinfo⟩ := hip
  -- Step 2: invert `Obs.«Ingress::get_ci».obs ev` to get `recordOf E₀ (ixAddr a) = some cm`
  -- and `recordOf E₀ ip.block = some cbM` via `Claim.load_verified_constant_de` + `recordOf_hashed`.
  have hrec_and_blk : recordOf E₀ (ixAddr a) = some cm ∧
      ∃ cbM, recordOf E₀ ip.block = some cbM := by
    have hcontra : ∀ {m2 : Heap F} {cs12 : List (Call F)} {wSh wRf wUn wBd : SourceValue F}
        {tag : String} {iargs : List (SourceValue F)},
        (∀ cl ∈ cs12, cl ∈ calls) →
        ObsFn Obs.W "Ingress::load_verified_constant" [xa] h
          (.construct "Ixon::Constant" "Mk"
            [.construct "Ixon::ConstantInfo" tag iargs, wSh, wRf, wUn, wBd]) m2 cs12 →
        tag ≠ "IPrj" → False := by
      intro m2 cs12 wSh wRf wUn wBd tag iargs hsub12 ev14 hne
      obtain ⟨-, bs1, c1, hsz1, hh1, hb1, hde1, hex1, hrep1, -⟩ :=
        Claim.load_verified_constant_de ⟨a, ha, rfl⟩ ev14
      have hrec1 : recordOf E₀ (ixAddr a) = some c1 := by
        rw [← hb1]
        exact Claim.recordOf_hashed hS hH (Core.hashed_mono hsub12 hh1) hsz1 hde1 hex1
      have hcm1 : cm = c1 := hS.record_eq ((hS.recordOf_eq_recordAt _).symm.trans hrec1)
        (Core.hashed_mono hsub hh) hba hex
      obtain ⟨iv, _, _, _, _, hvc, hciRep, -⟩ := hrep1
      injection hvc with _ _ hargs; injection hargs with hiv _; subst hiv
      rw [← hcm1, hinfo] at hciRep
      obtain ⟨_, hvc2, _⟩ := hciRep
      injection hvc2 with _ htag _; exact hne htag
    match Obs.«Ingress::get_ci».obs ev with
    | .Defn_n0 (cs12 := cs12) (ev14 := ev14) (hc302 := hc) .. =>
      exact (hcontra (fun cl hcl => hsub cl (by rw [hc]; simp [hcl])) ev14 (by decide)).elim
    | .Defn_other (cs12 := cs12) (ev14 := ev14) (hc423 := hc) .. =>
      exact (hcontra (fun cl hcl => hsub cl (by rw [hc]; simp [hcl])) ev14 (by decide)).elim
    | .Axio (cs12 := cs12) (ev14 := ev14) (hc515 := hc) .. =>
      exact (hcontra (fun cl hcl => hsub cl (by rw [hc]; simp [hcl])) ev14 (by decide)).elim
    | .Quot (cs12 := cs12) (ev14 := ev14) (hc606 := hc) .. =>
      exact (hcontra (fun cl hcl => hsub cl (by rw [hc]; simp [hcl])) ev14 (by decide)).elim
    | .DPrj (cs12 := cs12) (ev14 := ev14) (hc675 := hc) .. =>
      exact (hcontra (fun cl hcl => hsub cl (by rw [hc]; simp [hcl])) ev14 (by decide)).elim
    | .CPrj (cs12 := cs12) (ev14 := ev14) (hc851 := hc) .. =>
      exact (hcontra (fun cl hcl => hsub cl (by rw [hc]; simp [hcl])) ev14 (by decide)).elim
    | .RPrj (cs12 := cs12) (ev14 := ev14) (hc926 := hc) .. =>
      exact (hcontra (fun cl hcl => hsub cl (by rw [hc]; simp [hcl])) ev14 (by decide)).elim
    | .Recr (cs12 := cs12) (ev14 := ev14) (hc1071 := hc) .. =>
      exact (hcontra (fun cl hcl => hsub cl (by rw [hc]; simp [hcl])) ev14 (by decide)).elim
    | .IPrj (m2 := m2) (cs12 := cs12) (x_block_addr := xblk) (cs718 := cs718)
        (ev14 := ev14) (ev741 := ev741) (ev720 := evIprj) (hc750 := hc) .. =>
      have hsub12 : CallSub cs12 calls := fun cl hcl => hsub cl (by rw [hc]; simp [hcl])
      have hsub718 : CallSub cs718 calls := fun cl hcl => hsub cl (by rw [hc]; simp [hcl])
      obtain ⟨-, bs1, c1, hsz1, hh1, hb1, hde1, hex1, hrep1, -⟩ :=
        Claim.load_verified_constant_de ⟨a, ha, rfl⟩ ev14
      have hrec1 : recordOf E₀ (ixAddr a) = some c1 := by
        rw [← hb1]
        exact Claim.recordOf_hashed hS hH (Core.hashed_mono hsub12 hh1) hsz1 hde1 hex1
      have hcm1 : cm = c1 := hS.record_eq ((hS.recordOf_eq_recordAt _).symm.trans hrec1)
        (Core.hashed_mono hsub hh) hba hex
      obtain ⟨iv, _, _, _, _, hvc, hciRep, -⟩ := hrep1
      injection hvc with _ _ hargs; injection hargs with hiv _; subst hiv
      rw [← hcm1, hinfo] at hciRep
      obtain ⟨pv, hvc2, blkPtr, hpv, hblkAddr⟩ := hciRep
      injection hvc2 with _ _ hargs2; injection hargs2 with hmk _
      rw [hpv] at hmk
      injection hmk with _ _ hargs3
      injection hargs3 with _ hargs3; injection hargs3 with hxb _; subst hxb
      match Obs.«Ingress::get_ci_iprj».obs evIprj with
      | .run (cs12 := csB) (ev14 := evBlk) (hc283 := hcB) .. =>
        have hsubB : CallSub csB calls := fun cl hcl => hsub718 cl (by rw [hcB]; simp [hcl])
        have hblkRef731 : Core.S0.addr _ xblk ip.block :=
          Core.S0.addr_mono ev741.heap_extends hblkAddr
        obtain ⟨-, bsB, cbM, hszB, hhB, hbB, hdeB, hexB, -, -⟩ :=
          Claim.load_verified_constant_de hblkRef731 evBlk
        have hrecB : recordOf E₀ ip.block = some cbM := by
          rw [← hbB]
          exact Claim.recordOf_hashed hS hH (Core.hashed_mono hsubB hhB) hszB hdeB hexB
        exact ⟨by rwa [← hcm1] at hrec1, cbM, hrecB⟩
  obtain ⟨hrecM, cbM0, hrecB0⟩ := hrec_and_blk
  -- Step 3: unpack `hraw` at `.iPrj ip` and match `cbM0` with `cbM`.
  unfold L1.GetCIRawResult at hraw
  rw [hinfo] at hraw
  obtain ⟨hidx_lt, blkBytes, cbM, msM, indM, v, hhBlk, hbaBlk, hexBlk, -, hmutsM, hmsM, hldv,
      hrawInd⟩ := hraw
  have hcbM_eq : cbM = cbM0 :=
    hS.record_eq ((hS.recordOf_eq_recordAt ip.block).symm.trans hrecB0)
      (Core.hashed_mono hsub hhBlk) hbaBlk hexBlk
  subst hcbM_eq
  obtain ⟨_, hnp_lt, hni_lt, hnc_lt, _, tyPtr, blkPtr, bBlkM, hbBlkEq, hbBlkRef, hv_eq, _⟩ := hrawInd
  have hv_ld := Except.ok.inj (hld.symm.trans hldv)
  rw [hv_eq] at hv_ld
  injection hv_ld with _ _ ha_all
  injection ha_all with _ ha_all
  injection ha_all with _ ha_all
  injection ha_all with h_inp ha_all
  injection ha_all with h_ini ha_all
  injection ha_all with h_inct ha_all
  injection ha_all with _ ha_all
  injection ha_all with h_iblk ha_all
  injection ha_all with h_iidx _
  subst h_iblk
  obtain ⟨hcm_can, ha_can⟩ := LoadedReads.iprj_canonical indM hex htv hinfo
  rw [hba] at ha_can
  rw [Array.getElem?_toList] at hmsM
  exact ⟨cm, ip, cbM, msM, indM, bBlkM, hrecM, hinfo, hcm_can, ha_can, hrecB0, hmutsM, hmsM,
    hidx_lt, hnp_lt, hni_lt, hnc_lt, h_inp, h_ini, h_inct, hbBlkRef, hbBlkEq, h_iidx⟩

/-- Extracts the `KernelCheck::validate_expr_well_scoped` call (and its membership in `cs_iota`)
from the first four steps of `KernelModeled::check_iota_rule`. -/
private theorem check_iota_rule_scope_call
    {rc rm nl ty_r rp ni rhs cprj cty cnp cnf ilvls pins t_addr src dst aset r : SourceValue F}
    {h h' : Heap F} {cs_iota : List (Call F)}
    (ev : ObsFn Obs.W "KernelModeled::check_iota_rule"
      [rc, rm, nl, ty_r, rp, ni, rhs, cprj, cty, cnp, cnf, ilvls, pins, t_addr, src, dst, aset]
      h r h' cs_iota) :
    ∃ (h_plen v_sc : SourceValue F → Prop) (h1 h2 : Heap F) (v : SourceValue F)
      (cs_sc : List (Call F)),
      Heap.Extends h h1 ∧
      (⟨"KernelCheck::validate_expr_well_scoped", [rhs, .field 0, nl], h1⟩ : Call F) ∈ cs_iota ∧
      ObsFn Obs.W "KernelCheck::validate_expr_well_scoped" [rhs, .field 0, nl] h1 v h2 cs_sc := by
  have d0 := ObsFn.function_inv (s := IxVM.source) IxVM.KernelModeled.check_iota_rule.lookup
    (by simp [IxVM.KernelModeled.check_iota_rule, ControlLower.hasControl]) ev
  simp only [IxVM.KernelModeled.check_iota_rule] at d0
  -- 1. `let mi = rp + ni`
  obtain ⟨mi, _, _, c1a, c1b, d1, mt1, rest1, hc1⟩ := d0.letValue_inv; clear d0
  obtain ⟨_, _, _, _, _, dl1, dr1, _, _⟩ := d1.binary_inv
  obtain ⟨l1, rfl, _⟩ := dl1.var_inv; simp at l1; subst l1
  obtain ⟨l2, rfl, _⟩ := dr1.var_inv; simp at l2; subst l2
  obtain rfl := matchPattern_bind_inv mt1
  -- 2. `let d = rp + cnf`
  obtain ⟨d, _, _, c2a, c2b, d2, mt2, rest2, hc2⟩ := rest1.letValue_inv; clear rest1
  obtain ⟨_, _, _, _, _, dl2, dr2, _, _⟩ := d2.binary_inv
  obtain ⟨l3, rfl, _⟩ := dl2.var_inv; simp at l3; subst l3
  obtain ⟨l4, rfl, _⟩ := dr2.var_inv; simp at l4; subst l4
  obtain rfl := matchPattern_bind_inv mt2
  -- 3. `assert_eq!(Lists::length(pins), cnp)`
  obtain ⟨_, m3, _, c3a, c3b, d3, mt3, rest3, hc3⟩ := rest2.letValue_inv; clear rest2
  obtain ⟨_, a3, ap3⟩ := d3.builtin_inv
  obtain ⟨v3l, vs3, h1, _, _, rfl, d3l, a3r, _⟩ := a3.cons_inv
  obtain ⟨v3r, vs3', m3', _, _, rfl, d3r, a3nil, _⟩ := a3r.cons_inv
  obtain ⟨rfl, rfl, _⟩ := a3nil.nil_inv
  obtain ⟨_, _, _, _, a3la, ev_plen, _⟩ := d3l.call_inv
  obtain ⟨_, _, _, _, _, rfl, d3lv, a3lnil, _⟩ := a3la.cons_inv
  obtain ⟨rfl, rfl, _⟩ := a3lnil.nil_inv
  obtain ⟨l5, rfl, _⟩ := d3lv.var_inv; simp at l5; subst l5
  obtain ⟨l6, rfl, rfl⟩ := d3r.var_inv; simp at l6; subst l6
  obtain rfl := matchPattern_wildcard_inv mt3
  -- 4. `KernelCheck::validate_expr_well_scoped(rhs, 0, nl)`
  obtain ⟨v_sc, h_sc, _, c4a, c4b, d4, mt4, _, hc4⟩ := rest3.letValue_inv; clear rest3
  obtain ⟨_, m4, _, cs_sc, a4, ev_sc, hc_sc⟩ := d4.call_inv
  rw [instanceName_plain_some] at ev_sc hc_sc
  obtain ⟨_, _, m4_1, _, _, rfl, d4_1, a4_2, hc4_1⟩ := a4.cons_inv
  obtain ⟨_, _, m4_2, _, _, rfl, d4_2, a4_3, hc4_2⟩ := a4_2.cons_inv
  obtain ⟨_, _, m4_3, _, _, rfl, d4_3, a4_nil, hc4_3⟩ := a4_3.cons_inv
  obtain ⟨rfl, rfl, hc4_nil⟩ := a4_nil.nil_inv
  obtain ⟨l7, h1eq, rfl⟩ := d4_1.var_inv; simp at l7; subst l7
  obtain ⟨rfl, h2eq, rfl⟩ := d4_2.literal_inv
  obtain ⟨l8, h3eq, rfl⟩ := d4_3.var_inv; simp at l8; subst l8
  subst h1eq h2eq h3eq
  have hcall : (⟨"KernelCheck::validate_expr_well_scoped", [rhs, .field 0, nl], m4⟩ : Call F) ∈ cs_iota := by
    simp [hc1, hc2, hc3, hc4, hc_sc]
  exact ⟨fun _ => True, fun _ => True, _, h_sc, v_sc, cs_sc, ev_plen.heap_extends, hcall, ev_sc⟩

/-- Callback supplying block-constructor data (`nonrecsBlk`, `nonrecsTys`) for rules whose major
premise lies in the current block `B`. -/
abbrev CtorLookupFn (calls : List (Call F)) (bAddr : _root_.Address) (t : Ix.Kernel.RoleTable)
    (E₀ : Ixon.Env) (lim : Option Nat) (csFam : List (Call F))
    (B rb : _root_.Address) (cb crb : Ixon.Constant) (ms : Array Ixon.MutConst)
    (advAs srcAs dstAs : List Bytes.Address)
    (nonrecsBlk : List (ConstantInfo .anon)) (nonrecsTys : List KExpr) : Prop :=
  ∀ (im j : Nat) (ind : Ixon.Inductive) (ct : Ixon.Constructor),
    ms[im]? = some (.indc ind) → ind.ctors[j]? = some ct →
    ∃ (pos : Nat) (ty₀C tyAC : KExpr),
      pos < nonrecsBlk.length ∧
      nonrecsBlk[pos]? = some (.ctorInfo
        ⟨Core.keyOf t (cprjAddr B im j), List.range ct.lvls.toNat, ty₀C⟩
        ct.params.toNat ct.fields.toNat) ∧
      nonrecsTys[pos]? = some tyAC ∧
      (exprReader t (fun x => E₀.blobs.get? x) cb id (blockSelf t B ms)).read ct.typ = .ok ty₀C ∧
      ty₀C.looseBVarsBounded 0 = true ∧
      ty₀C.allLevelParamsDefined (List.range ct.lvls.toNat) = true ∧
      LoadedReads.canonAnn cb (List.range ct.lvls.toNat)
        (((L1.mutsRootOffset ms.toList im : Nat) : F) + 1 + ((j : Nat) : F)) ct.typ ty₀C =
          some tyAC ∧
      tyAC.allLevelParamsDefined (List.range ct.lvls.toNat) = true ∧
      ∀ {L : Ix.Kernel.Env .anon → NativeFam .anon → Prop}
        {adv : _root_.Address → Prop} {E : Ixon.Env} {env : Ix.Kernel.Env .anon},
        FamilyStepEnv.{u} L calls t E₀ lim B cb rb crb adv E env →
        ((∀ a, AdviceIn csFam a → adv a) ∨
          ∀ a, AdviceListedIn advAs a →
            adv a ∨ ∀ ca x, recordOf E₀ a = some ca → ¬ ConstAddrOf a ca x) →
        (∀ k' ∈ srcAs.map (fun b => Core.keyOf t (ixAddr b)),
          ∃ cvm mval hint, env.find? (aliasMap ((srcAs.map fun b => Core.keyOf t (ixAddr b)).zip
            (dstAs.map fun b => Core.keyOf t (ixAddr b))) k') = some (.defnInfo cvm mval hint)) →
        Decl.NoProjIn (srcAs.map fun b => Core.keyOf t (ixAddr b)) tyAC = true ∧
        ∀ ci_gc, env.find? (aliasMap ((srcAs.map fun b => Core.keyOf t (ixAddr b)).zip
          (dstAs.map fun b => Core.keyOf t (ixAddr b))) (Core.keyOf t (cprjAddr B im j))) =
            some ci_gc →
          ci_gc.toConstantVal.levelParams.length = ct.lvls.toNat

/-- Helper: `cprjAddr Bm im j` is not in `srcAs.map ixAddr` when `Bm ≠ B`, since every element
of `srcAs` has a distinct record in `E₀` (`iPrj`, `cPrj` at `B`, or `rPrj`). -/
private theorem cprjAddr_not_mem_src {E₀ : Ixon.Env} {B rb Bm : _root_.Address}
    {cb crb : Ixon.Constant} {ms rs : Array Ixon.MutConst}
    (hB : FamBlockRecord E₀ B cb ms) (hR : FamRecRecord E₀ rb crb rs)
    {typeAs ctorAs recAs : List Bytes.Address}
    (htypes : typeAs.map ixAddr =
      ms.toList.mapIdx fun i m => projAddr (Specs.Callees.memberProjInfo B i m))
    (hctors : ctorAs.map ixAddr = ctorAddrsFrom B ms.toList 0)
    (hrecs : recAs.map ixAddr =
      rs.toList.mapIdx fun i m => projAddr (Specs.Callees.memberProjInfo rb i m))
    {im j : Nat} (hne : Bm ≠ B)
    (hrecC : recordOf E₀ (cprjAddr Bm im j) =
      some ⟨.cPrj ⟨im.toUInt64, j.toUInt64, Bm⟩, #[], #[], #[], #[]⟩) :
    cprjAddr Bm im j ∉ (typeAs ++ ctorAs ++ recAs).map ixAddr := by
  intro hmem
  simp only [List.map_append, List.mem_append] at hmem
  rcases hmem with (hmemT | hmemC) | hmemR
  · rw [htypes] at hmemT
    obtain ⟨i, hi_lt, hi_eq⟩ := List.mem_mapIdx.mp hmemT
    have hm : ms[i]? = some ms[i] := Array.getElem?_eq_getElem (by simpa using hi_lt)
    obtain ⟨ind, hind⟩ := hB.indcs ms[i] (Array.mem_toList_iff.mpr (Array.getElem_mem _))
    have hmi : ms[i]? = some (.indc ind) := by rwa [hind] at hm
    have hproj : recordOf E₀ (iprjAddr B i) = some (memberProjection B i (.indc ind)) := by
      rw [← LoadedReads.memberAddr_indc]; exact hB.members i (.indc ind) hmi
    have hi_eq' : iprjAddr B i = cprjAddr Bm im j := by
      have h0 : projAddr (Specs.Callees.memberProjInfo B i (.indc ind)) = iprjAddr B i := rfl
      rw [← h0]; simpa [Array.getElem_toList, hind] using hi_eq
    rw [hi_eq', hrecC] at hproj
    have he := Option.some.inj hproj
    have hinfo := congrArg Ixon.Constant.info he
    simp [memberProjection] at hinfo
  · rw [hctors] at hmemC
    have hct : ∀ (l : List Ixon.MutConst) (p : Nat),
        cprjAddr Bm im j ∈ ctorAddrsFrom B l p →
        ∃ (i' : Nat) (ind' : Ixon.Inductive) (j' : Nat),
          l[i']? = some (.indc ind') ∧ j' < ind'.ctors.size ∧
          cprjAddr Bm im j = cprjAddr B (p + i') j' := by
      intro l
      induction l with
      | nil => intro p h; simp [ctorAddrsFrom] at h
      | cons m rest ih =>
        intro p h
        cases m with
        | indc ind =>
          simp only [ctorAddrsFrom, List.mem_append, List.mem_map, List.mem_range] at h
          rcases h with ⟨j', hj', heq⟩ | hrest
          · exact ⟨0, ind, j', rfl, hj', heq.symm⟩
          · obtain ⟨i', ind', j', hget, hj', heq⟩ := ih (p + 1) hrest
            exact ⟨i' + 1, ind', j', hget, hj', by rwa [show p + (i' + 1) = p + 1 + i' by omega]⟩
        | defn _ | recr _ =>
          simp only [ctorAddrsFrom] at h
          obtain ⟨i', ind', j', hget, hj', heq⟩ := ih (p + 1) h
          exact ⟨i' + 1, ind', j', hget, hj', by rwa [show p + (i' + 1) = p + 1 + i' by omega]⟩
    obtain ⟨i', ind', j', hget', hj', heq⟩ := hct ms.toList 0 hmemC
    rw [Array.getElem?_toList] at hget'
    rw [Nat.zero_add] at heq
    have hproj := hB.ctors i' ind' j' hget' hj'
    rw [LoadedReads.ctorAddr_eq_cprjAddr, ← heq, hrecC] at hproj
    have hinfo := congrArg Ixon.Constant.info (Option.some.inj hproj)
    simp [constructorProjection] at hinfo
    exact hne hinfo.2.2
  · rw [hrecs] at hmemR
    obtain ⟨k, hk_lt, hk_eq⟩ := List.mem_mapIdx.mp hmemR
    have hm : rs[k]? = some rs[k] := Array.getElem?_eq_getElem (by simpa using hk_lt)
    obtain ⟨rc', hrc'⟩ := hR.recrs rs[k] (Array.mem_toList_iff.mpr (Array.getElem_mem _))
    have hmk : rs[k]? = some (.recr rc') := by rwa [hrc'] at hm
    have hproj : recordOf E₀ (rprjAddr rb k) = some (memberProjection rb k (.recr rc')) := by
      rw [← LoadedReads.memberAddr_recr]; exact hR.members k (.recr rc') hmk
    have hk_eq' : rprjAddr rb k = cprjAddr Bm im j := by
      have h0 : projAddr (Specs.Callees.memberProjInfo rb k (.recr rc')) = rprjAddr rb k := rfl
      rw [← h0]; simpa [Array.getElem_toList, hrc'] using hk_eq
    rw [hk_eq', hrecC] at hproj
    have hinfo := congrArg Ixon.Constant.info (Option.some.inj hproj)
    simp [memberProjection] at hinfo

private theorem famAddr_mem_src_lists {E₀ : Ixon.Env} {B rb : _root_.Address} {cb crb : Ixon.Constant}
    {ms rs : Array Ixon.MutConst} (hB : FamBlockRecord E₀ B cb ms) (hR : FamRecRecord E₀ rb crb rs)
    {typeAs ctorAs recAs : List Bytes.Address}
    (htypes : typeAs.map ixAddr =
      ms.toList.mapIdx fun i m => projAddr (Specs.Callees.memberProjInfo B i m))
    (hctors : ctorAs.map ixAddr = ctorAddrsFrom B ms.toList 0)
    (hrecs : recAs.map ixAddr =
      rs.toList.mapIdx fun i m => projAddr (Specs.Callees.memberProjInfo rb i m))
    {x : _root_.Address} (hx : FamAddr B cb rb crb x) :
    x ∈ (typeAs ++ ctorAs ++ recAs).map ixAddr := by
  rw [List.map_append, List.map_append, htypes, hctors, hrecs]
  rcases hx with ⟨⟨-, hs⟩ | ⟨ms', i, m, hms, hm, hxm⟩⟩ | ⟨⟨-, hs⟩ | ⟨rs', i, m, hrs, hm, hxm⟩⟩
  · exact (standalone_not_block hs ⟨ms, hB.muts⟩).elim
  · have e : ms' = ms := Ixon.ConstantInfo.muts.inj (hms.symm.trans hB.muts)
    subst e
    have hm' : ms'.toList[i]? = some m := by rw [Array.getElem?_toList]; exact hm
    rcases hxm with rfl | ⟨ind, j, rfl, hj, rfl⟩
    · have hget : (ms'.toList.mapIdx fun i m =>
          projAddr (Specs.Callees.memberProjInfo B i m))[i]? = some (memberAddr B i m) := by
        rw [List.getElem?_mapIdx, hm']; simp [LoadedReads.memberAddr_eq_projAddr]
      exact List.mem_append_left _ (List.mem_append_left _ (List.mem_of_getElem? hget))
    · refine List.mem_append_left _ (List.mem_append_right _ ?_)
      have h := mem_ctorAddrsFrom B ms'.toList 0 i ind j hm' hj
      rw [Nat.zero_add, ← LoadedReads.ctorAddr_eq_cprjAddr] at h; exact h
  · exact (standalone_not_block hs ⟨rs, hR.muts⟩).elim
  · have e : rs' = rs := Ixon.ConstantInfo.muts.inj (hrs.symm.trans hR.muts)
    subst e
    have hm' : rs'.toList[i]? = some m := by rw [Array.getElem?_toList]; exact hm
    rcases hxm with rfl | ⟨ind, j, rfl, hj, rfl⟩
    · have hget : (rs'.toList.mapIdx fun i m =>
          projAddr (Specs.Callees.memberProjInfo rb i m))[i]? = some (memberAddr rb i m) := by
        rw [List.getElem?_mapIdx, hm']; simp [LoadedReads.memberAddr_eq_projAddr]
      exact List.mem_append_right _ (List.mem_of_getElem? hget)
    · obtain ⟨r', hr'⟩ := hR.recrs _ (List.mem_of_getElem? hm'); cases hr'

private theorem src_mem_famAddr {E₀ : Ixon.Env} {B rb : _root_.Address} {cb crb : Ixon.Constant}
    {ms rs : Array Ixon.MutConst} (hB : FamBlockRecord E₀ B cb ms) (hR : FamRecRecord E₀ rb crb rs)
    {typeAs ctorAs recAs : List Bytes.Address}
    (htypes : typeAs.map ixAddr =
      ms.toList.mapIdx fun i m => projAddr (Specs.Callees.memberProjInfo B i m))
    (hctors : ctorAs.map ixAddr = ctorAddrsFrom B ms.toList 0)
    (hrecs : recAs.map ixAddr =
      rs.toList.mapIdx fun i m => projAddr (Specs.Callees.memberProjInfo rb i m))
    {x : _root_.Address} (hx : x ∈ (typeAs ++ ctorAs ++ recAs).map ixAddr) :
    FamAddr B cb rb crb x := by
  rw [List.map_append, List.map_append, htypes, hctors, hrecs] at hx
  rcases List.mem_append.mp hx with htc | hr
  · rcases List.mem_append.mp htc with ht' | hc'
    · left; right
      obtain ⟨i, hi, heq⟩ := List.mem_iff_getElem.mp ht'
      simp only [List.length_mapIdx, Array.length_toList] at hi
      simp only [List.getElem_mapIdx] at heq
      refine ⟨ms, i, ms[i], hB.muts, Array.getElem?_eq_getElem hi, Or.inl ?_⟩
      rw [← heq, LoadedReads.memberAddr_eq_projAddr]; rfl
    · left; right
      have hgo : ∀ (l : List Ixon.MutConst) (p : Nat), x ∈ ctorAddrsFrom B l p →
          ∃ i ind j, l[i]? = some (.indc ind) ∧ j < ind.ctors.size ∧ x = cprjAddr B (p + i) j := by
        intro l; induction l with
        | nil => intro p h; simp [ctorAddrsFrom] at h
        | cons m rest ih =>
          intro p h
          cases m with
          | indc ind =>
            simp only [ctorAddrsFrom, List.mem_append, List.mem_map, List.mem_range] at h
            rcases h with ⟨j, hj, rfl⟩ | hrest
            · exact ⟨0, ind, j, rfl, hj, by simp⟩
            · obtain ⟨i, ind', j, hi, hj, hx'⟩ := ih (p + 1) hrest
              exact ⟨i + 1, ind', j, hi, hj, by simpa [Nat.add_assoc, Nat.add_comm 1 i] using hx'⟩
          | defn _ | recr _ =>
            simp only [ctorAddrsFrom] at h
            obtain ⟨i, ind', j, hi, hj, hx'⟩ := ih (p + 1) h
            exact ⟨i + 1, ind', j, hi, hj, by simpa [Nat.add_assoc, Nat.add_comm 1 i] using hx'⟩
      obtain ⟨i, ind, j, hi, hj, rfl⟩ := hgo ms.toList 0 hc'
      rw [Array.getElem?_toList] at hi
      exact ⟨ms, i, .indc ind, hB.muts, hi, Or.inr ⟨ind, j, rfl, hj, by
        simp [LoadedReads.ctorAddr_eq_cprjAddr]⟩⟩
  · right; right
    obtain ⟨i, hi, heq⟩ := List.mem_iff_getElem.mp hr
    simp only [List.length_mapIdx, Array.length_toList] at hi
    simp only [List.getElem_mapIdx] at heq
    refine ⟨rs, i, rs[i], hR.muts, Array.getElem?_eq_getElem hi, Or.inl ?_⟩
    rw [← heq, LoadedReads.memberAddr_eq_projAddr]; rfl

private theorem repList_map_pred {en : String} {α : Type}
    {R S : Heap F → α → SourceValue F → Prop} {h : Heap F} {xs : List α} {p : SourceValue F}
    (f : ∀ a v, R h a v → S h a v) (hr : RepList en R h xs p) : RepList en S h xs p := by
  induction hr with
  | nil c => exact .nil c
  | cons c hx _ ih => exact .cons c (f _ _ hx) ih

private theorem blockRecurAddrs_eq_mapIdx (B : _root_.Address) (ms : List Ixon.MutConst) :
    L1.blockRecurAddrs B ms =
      ms.mapIdx fun i m => projAddr (Specs.Callees.memberProjInfo B i m) := by
  unfold L1.blockRecurAddrs
  have hgo : ∀ (l : List Ixon.MutConst) (p : Nat),
      L1.blockRecurAddrsAux B p l =
        l.mapIdx fun i m => projAddr (Specs.Callees.memberProjInfo B (p + i) m) := by
    intro l; induction l with
    | nil => intro _; rfl
    | cons m rest ih' =>
      intro p
      simp only [L1.blockRecurAddrsAux, List.mapIdx_cons, Nat.add_zero]
      congr 1
      have h2 := ih' (p + 1)
      simpa [Nat.add_assoc, Nat.add_comm 1] using h2
  simpa using hgo ms 0

private theorem usedRef_stored_or_src_lists {L : Ix.Kernel.Env .anon → NativeFam .anon → Prop}
    {calls : List (Call F)} {t : Ix.Kernel.RoleTable} {E₀ : Ixon.Env} {lim : Option Nat}
    {B rb : _root_.Address} {cb crb : Ixon.Constant} {ms rs : Array Ixon.MutConst}
    {adv : _root_.Address → Prop} {E : Ixon.Env} {env : Ix.Kernel.Env .anon}
    {typeAs ctorAs recAs : List Bytes.Address}
    (hB : FamBlockRecord E₀ B cb ms) (hR : FamRecRecord E₀ rb crb rs)
    (htypes : typeAs.map ixAddr =
      ms.toList.mapIdx fun i m => projAddr (Specs.Callees.memberProjInfo B i m))
    (hctors : ctorAs.map ixAddr = ctorAddrsFrom B ms.toList 0)
    (hrecs : recAs.map ixAddr =
      rs.toList.mapIdx fun i m => projAddr (Specs.Callees.memberProjInfo rb i m))
    (hSE : FamilyStepEnv.{u} L calls t E₀ lim B cb rb crb adv E env)
    {x : _root_.Address} (hx : UsedRef E₀ B x ∨ UsedRef E₀ rb x)
    (hc : Claim.CoveredAt t lim x ∨ NeedOk E₀ x) :
    (∃ ci, env.find? (Core.keyOf t x) = some ci) ∨ x ∈ (typeAs ++ ctorAs ++ recAs).map ixAddr := by
  rcases hSE.refs x hx with hs | hf | hn
  · exact Or.inl (Option.isSome_iff_exists.mp hs)
  · exact Or.inr (famAddr_mem_src_lists hB hR htypes hctors hrecs hf)
  · rcases hc with hcov | hneed
    · exact Or.inl (Option.isSome_iff_exists.mp (hSE.covered x hcov))
    · exact absurd hneed hn

/-- Single-pass walk of `KernelModeled::check_rules_go` along `L1.RulesTraceRep`: builds the read
rules `rules₀`, their canonical right-hand sides `rhss`, their advice theorem keys `thms`, their
constructor-projection records in `E₀`, and `RulesFacts` at any `FamilyStepEnv`. -/
theorem rulesTrace_walk
    {calls : List (Call F)} {bAddr : _root_.Address} {t : Ix.Kernel.RoleTable}
    {E₀ : Ixon.Env} {lim : Option Nat} {csFam : List (Call F)}
    {B rb Bm : _root_.Address} {cb crb cbM : Ixon.Constant}
    {ms rs msM : Array Ixon.MutConst} {indM : Ixon.Inductive}
    (ht : t.check = .ok ()) (hbd : Bounded calls)
    (hS : LoadedReads.RunStore calls E₀) (hH : LoadedReads.HashedRecordsStored calls E₀)
    (hB : FamBlockRecord E₀ B cb ms) (hR : FamRecRecord E₀ rb crb rs)
    (hrecBM : recordOf E₀ Bm = some cbM) (hmutsM : cbM.info = .muts msM)
    {im : Nat} (him_lt : im < 72057594037927936) (hmsM : msM[im]? = some (.indc indM))
    {advAs typeAs ctorAs recAs dstAs : List Bytes.Address}
    (htypes : typeAs.map ixAddr =
      ms.toList.mapIdx fun i m => projAddr (Specs.Callees.memberProjInfo B i m))
    (hctors : ctorAs.map ixAddr = ctorAddrsFrom B ms.toList 0)
    (hrecs : recAs.map ixAddr =
      rs.toList.mapIdx fun i m => projAddr (Specs.Callees.memberProjInfo rb i m))
    (hlenSD : (typeAs ++ ctorAs ++ recAs).length = dstAs.length)
    {nonrecsBlk : List (ConstantInfo .anon)} {nonrecsTys : List KExpr}
    (hlenNR : nonrecsBlk.length = nonrecsTys.length)
    (hctorLookup : CtorLookupFn.{u} calls bAddr t E₀ lim csFam B rb cb crb ms advAs
      (typeAs ++ ctorAs ++ recAs) dstAs nonrecsBlk nonrecsTys)
    (hrecRefs : ∀ x, UsedRef E₀ rb x → Claim.CoveredAt t lim x ∨ NeedOk E₀ x)
    {recKey : KKey} {rc : Ixon.Recursor} {kRec : Nat} {ps : List LevelParam}
    {tyA : KExpr} {mI rP : Nat} {lvls : List Level} {pins : List KExpr}
    (hrk : rs[kRec]? = some (.recr rc))
    (hperm : ps.Perm (List.range ps.length))
    (hps_len : ps.length = rc.lvls.toNat) (hlvls_lt : rc.lvls.toNat < 4294967296)
    (hrp_le : rP ≤ mI) (hmi_lt : mI < 288230376151711744)
    (hcnp_lt : indM.params.toNat < 72057594037927936)
    (hmaj : majorShape tyA mI rP indM.params.toNat = some (lvls, pins))
    (hlvls_def : lvls.all (Level.allParamsDefined ps) = true)
    (hpins_ok : pins.all (fun p => !p.hasFvar && p.looseBVarsBounded rP &&
      p.allLevelParamsDefined ps) = true)
    {blobs : List (_root_.Address × ByteArray)} {tree : L1.BinderTreeData}
    (hblob : ∀ x bs, (x, bs) ∈ blobs → E₀.blobs.get? x = some bs)
    (built : L1.BinderTreeBuilt (L1.binderLeavesData crb.binders.toList) tree)
    {a_rm bBlkM : Bytes.Address}
    {rcV rm ty_r iblock ilvls pins_ptr src dst aset s_out : SourceValue F}
    (hbBlkM_eq : ixAddr bBlkM = Bm)
    (hrm_key : Core.keyOf t (ixAddr a_rm) =
      aliasMap (((typeAs ++ ctorAs ++ recAs).map fun b => Core.keyOf t (ixAddr b)).zip
        (dstAs.map fun b => Core.keyOf t (ixAddr b))) recKey)
    (hrm_in_dst : a_rm ∈ dstAs)
    {rus : List Ixon.RecursorRule} (hrus_sub : ∀ ru ∈ rus, ru ∈ rc.rules.toList) :
    ∀ {j : Nat} {root : F} {rules_ptr s_in : SourceValue F} {bytes : List UInt8}
      {h h' : Heap F} {cs_go : List (Call F)},
      j + rus.length = indM.ctors.size →
      indM.ctors.size < 72057594037927936 →
      CallSub cs_go calls →
      RCRep t lim h rcV →
      Bytes.RepAddressRef addrTy h a_rm rm →
      Bytes.RepAddressRef addrTy h bBlkM iblock →
      RepList addrListEnum (Bytes.RepAddressRef addrTy) h (typeAs ++ ctorAs ++ recAs) src →
      RepList addrListEnum (Bytes.RepAddressRef addrTy) h dstAs dst →
      AddrMapAll addrMapEnum (fun _ k _ => AdvChecked calls bAddr t lim csFam advAs k) h aset →
      Decl.TmCExact (Core.keyOf t) h (Core.posOf ps tyA) ty_r →
      (∀ a, AddrIn h ty_r a → UsedRef E₀ rb (ixAddr a)) →
      RepKLevelList h (lvls.map (Level.subst ps (Core.posLevels ps))) ilvls →
      RepList kexprListEnum
        (fun h P p => Decl.TmExact (Core.keyOf t) 0 zeroGhost h rP P p ∧
          ∀ a, AddrIn h p a → UsedRef E₀ rb (ixAddr a)) h
        (pins.map (Core.posOf ps)) pins_ptr →
      L1.RulesTraceRep crb.refs.toList (L1.blockRecurAddrs rb rs.toList) crb.univs.toList
        crb.sharing.toList blobs tree h j root rus rules_ptr →
      L1.Stream h bytes s_in →
      ObsFn Obs.W "KernelModeled::check_rules_go"
        [rcV, rm, .field (ps.length : F), ty_r, .field (rP : F), .field ((mI - rP : Nat) : F),
          rules_ptr, iblock, .field (im : F), .field (indM.params.toNat : F), ilvls, pins_ptr,
          src, dst, aset, s_in, .field (j : F)] h s_out h' cs_go →
      ∃ (rules₀ : List (RecRule .anon)) (rhss : List KExpr) (thms : List KKey)
        (rlsCan : List (RecRule .anon)) (remBytes : List UInt8),
        L1.Stream h' remBytes s_out ∧
        List.Forall₂ (RuleReads t (exprReader t (fun x => E₀.blobs.get? x) crb
          (Ix.Kernel.Reader.recParam ps) (blockSelf t rb rs)) Bm im) (rus.zipIdx j) rules₀ ∧
        (∀ rl ∈ rules₀, rl.rhs.looseBVarsBounded 0 = true ∧ rl.rhs.allLevelParamsDefined ps = true) ∧
        LoadedReads.canonRules crb ps rc.k rc.params.toNat root rus rules₀ = some rlsCan ∧
        List.Forall₂ (fun (rl : RecRule .anon) (rhsA : KExpr) => rl.rhs = rhsA) rlsCan rhss ∧
        (∀ idx, idx < rus.length →
          recordOf E₀ (cprjAddr Bm im (j + idx)) =
            some ⟨.cPrj ⟨im.toUInt64, (j + idx).toUInt64, Bm⟩, #[], #[], #[], #[]⟩) ∧
        (∀ {L : Ix.Kernel.Env .anon → NativeFam .anon → Prop}
          {adv : _root_.Address → Prop} {E : Ixon.Env} {env : Ix.Kernel.Env .anon}
          (recsBlk : List (ConstantInfo .anon)) (recsTys : List KExpr),
          FamilyStepEnv.{u} L calls t E₀ lim B cb rb crb adv E env →
          ((∀ a, AdviceIn csFam a → adv a) ∨
            ∀ a, AdviceListedIn advAs a →
              adv a ∨ ∀ ca x, recordOf E₀ a = some ca → ¬ ConstAddrOf a ca x) →
          (∀ k' ∈ (typeAs ++ ctorAs ++ recAs).map (fun b => Core.keyOf t (ixAddr b)),
            ∃ cvm mval hint, env.find? (aliasMap (((typeAs ++ ctorAs ++ recAs).map fun b =>
              Core.keyOf t (ixAddr b)).zip (dstAs.map fun b => Core.keyOf t (ixAddr b))) k') =
                some (.defnInfo cvm mval hint)) →
          (∀ b ∈ dstAs, ∃ ci, env.find? (Core.keyOf t (ixAddr b)) = some ci) →
          Decl.NoProjIn ((typeAs ++ ctorAs ++ recAs).map fun b => Core.keyOf t (ixAddr b)) tyA = true →
          (∀ fvsP crest2, openPisAtFvars rP tyA 0 = some (fvsP, crest2) →
            ∀ p ∈ pins, LeavesFixed (aliasMap (((typeAs ++ ctorAs ++ recAs).map fun b =>
              Core.keyOf t (ixAddr b)).zip (dstAs.map fun b => Core.keyOf t (ixAddr b))))
              (Expr.instSpine (fvsP.take rP) (rP - 1) p)) →
          RulesFacts env (aliasMap (((typeAs ++ ctorAs ++ recAs).map fun b =>
            Core.keyOf t (ixAddr b)).zip (dstAs.map fun b => Core.keyOf t (ixAddr b))))
            (nonrecsBlk ++ recsBlk) (nonrecsTys ++ recsTys) recKey ps tyA mI rP
            rules₀ rhss thms) := by
  have htwf : t.wf = true := by unfold Ix.Kernel.RoleTable.wf; rw [ht]; rfl
  have hmod : Aiur.Library.U32.Goldilocks.modulus = 18446744069414584321 := rfl
  let srcAs := typeAs ++ ctorAs ++ recAs
  let srcKeys := srcAs.map fun b => Core.keyOf t (ixAddr b)
  let dstKeys := dstAs.map fun b => Core.keyOf t (ixAddr b)
  let g := aliasMap (srcKeys.zip dstKeys)
  have hagree : L1.BlobReadAgreement (readCtx t (fun x => E₀.blobs.get? x)).blob blobs :=
    L1.BlobReadAgreement.of_mem hblob
  induction rus with
  | nil =>
    intro j root rules_ptr s_in bytes h h' cs_go _ _ _ _ _ _ _ _ _ _ _ _ _ hrls hstr ev
    match Obs.«KernelModeled::check_rules_go».obs ev with
    | .Nil (he21 := hr) (he22 := hh) .. =>
      subst hr hh
      exact ⟨[], [], [], [], bytes, hstr, List.Forall₂.nil, (fun _ hm => nomatch hm), rfl,
        List.Forall₂.nil, (fun _ hlt => nomatch hlt), fun _ _ _ _ _ _ _ _ => trivial⟩
    | .Cons (ld12 := ld) .. =>
      cases hrls with
      | nil cell => exact absurd ld (by simp [loadValue_enum_cell cell])
  | cons ru rus ih =>
    intro j root rules_ptr s_in bytes h h' cs_go hlen_j hctors_lt hsub hrc hrm hbBlkM hsrc hdst
      haset hty_rep hty_used hilvls hpins hrls hstr ev
    match Obs.«KernelModeled::check_rules_go».obs ev with
    | .Nil (ld12 := ld) .. =>
      cases hrls with
      | cons cell _ _ _ _ _ => exact absurd ld (by simp [loadValue_enum_cell cell])
    | .Cons (x_rest := x_rest) (m42 := m42) (cs52 := cs52) (x_t := x_t) (x_s2 := x_s2)
        (v76 := v76) (m77 := m77) (w100 := w100) (x_rnf := x_rnf) (x_rhs := x_rhs)
        (v116 := v_cprj) (m117 := m117) (cs127 := cs127) (m155 := m155) (p163 := p163)
        (cs169 := cs169) (w186 := w186) (x_cty := x_cty) (w187 := w187) (w188 := w188)
        (w189 := w189) (x_cnp := x_cnp) (x_cnf := x_cnf) (w190 := w190) (cs290 := cs290)
        (cs432 := cs432) (v451 := v451)
        (ld12 := ld) (ev54 := ev_ga) (ev129 := ev_cprj) (ev171 := ev_ci) (ld165 := ld_ci)
        (heq258 := heq_cnp) (heq286 := heq_rnf) (ev292 := ev_iota) (op577 := op_j1)
        (ev434 := ev_rec) (hc579 := hc) =>
      subst hc
      have hsub_ga : CallSub cs52 calls := fun cl hcl => hsub cl (by simp [hcl])
      have hsub_cprj : CallSub cs127 calls := fun cl hcl => hsub cl (by simp [hcl])
      have hsub_ci : CallSub cs169 calls := fun cl hcl => hsub cl (by simp [hcl])
      have hsub_iota : CallSub cs290 calls := fun cl hcl => hsub cl (by simp [hcl])
      have hcall_ci : (⟨"Ingress::get_ci", [v_cprj], m117⟩ : Call F) ∈ calls := hsub _ (by simp)
      have hsub_rec : CallSub cs432 calls := fun cl hcl => hsub cl (by simp [hcl])
      -- Unpack `hrls` cell
      cases hrls with
      | cons cell hru_nf hraw_rhs hplan_rhs hlev_rhs hrls_rest =>
        obtain ⟨_, heq_cons⟩ := load_cell cell ld
        injection heq_cons with hmk hrest_eq; injection hrest_eq with hrest_eq
        injection hmk with _ _ hmk_args
        injection hmk_args with _ hmk_args
        injection hmk_args with hrnf_eq hmk_args
        injection hmk_args with hrhs_eq _
        have hrhs_sym := hrhs_eq.symm
        subst hrest_eq hrnf_eq hrhs_sym
        -- 1. Advice theorem address from stream
        obtain ⟨a_t, rem1, xt', xs2', _, htup_ga, ha_t_m42, hstr_m42, ext_ga, _⟩ :=
          Decl.get_address_spec hstr ev_ga
        injection htup_ga with hl; injection hl with h1 hl; injection hl with h2 _; subst h1 h2
        -- 2. Constructor projection address `a_cprj` at `cprjAddr Bm im j`
        have hbBlkM_m42 := Bytes.repAddressRef_heapMono₂ addrTy ext_ga hbBlkM
        obtain ⟨a_cprj, ha_cprj_m117, ha_cprj_eq⟩ :=
          projection_addr_ctor_bounded ev_cprj (bounded_sub hsub_cprj hbd) hbBlkM_m42
        have him_val : ZMod.val (im : F) = im := SubstAux.val_natCast (by omega)
        have hj_val : ZMod.val (j : F) = j := SubstAux.val_natCast (by omega)
        rw [hbBlkM_eq, him_val, hj_val] at ha_cprj_eq
        -- Exact constructor-projection record in `E₀` (via `projection_addr_ctor_hashed` + `get_ci`)
        let c0 : ScopedCtx := ScopedCtx.unrestricted ⟨{}, .empty, default, none⟩
        have hhash_cprj := Core.hashed_mono hsub_cprj
          (projection_addr_ctor_hashed c0 ev_cprj hbBlkM_m42)
        rw [hbBlkM_eq, him_val, hj_val] at hhash_cprj
        have hrec_cprj : recordOf E₀ (cprjAddr Bm im j) =
            some ⟨.cPrj ⟨im.toUInt64, j.toUInt64, Bm⟩, #[], #[], #[], #[]⟩ := by
          have hload_rec : ∃ c_ld, recordOf E₀ (ixAddr a_cprj) = some c_ld := by
            have hof : ∀ {m2 : Heap F} {cs12 : List (Call F)} {vC : SourceValue F},
                CallSub cs12 calls →
                ObsFn Obs.W "Ingress::load_verified_constant" [v_cprj] m117 vC m2 cs12 →
                ∃ c_ld, recordOf E₀ (ixAddr a_cprj) = some c_ld := by
              intro m2 cs12 vC hsub12 ev14
              obtain ⟨-, bs1, c1, hsz1, hh1, hb1, hde1, hex1, -, -⟩ :=
                Claim.load_verified_constant_de ⟨a_cprj, ha_cprj_m117, rfl⟩ ev14
              exact ⟨c1, by
                rw [← hb1]
                exact Claim.recordOf_hashed hS hH (Core.hashed_mono hsub12 hh1) hsz1 hde1 hex1⟩
            match Obs.«Ingress::get_ci».obs ev_ci with
            | .Defn_n0 (cs12 := c12) (ev14 := e14) (hc302 := hci) .. =>
              exact hof (fun cl hcl => hsub_ci cl (by rw [hci]; simp [hcl])) e14
            | .Defn_other (cs12 := c12) (ev14 := e14) (hc423 := hci) .. =>
              exact hof (fun cl hcl => hsub_ci cl (by rw [hci]; simp [hcl])) e14
            | .Axio (cs12 := c12) (ev14 := e14) (hc515 := hci) .. =>
              exact hof (fun cl hcl => hsub_ci cl (by rw [hci]; simp [hcl])) e14
            | .Quot (cs12 := c12) (ev14 := e14) (hc606 := hci) .. =>
              exact hof (fun cl hcl => hsub_ci cl (by rw [hci]; simp [hcl])) e14
            | .DPrj (cs12 := c12) (ev14 := e14) (hc675 := hci) .. =>
              exact hof (fun cl hcl => hsub_ci cl (by rw [hci]; simp [hcl])) e14
            | .IPrj (cs12 := c12) (ev14 := e14) (hc750 := hci) .. =>
              exact hof (fun cl hcl => hsub_ci cl (by rw [hci]; simp [hcl])) e14
            | .CPrj (cs12 := c12) (ev14 := e14) (hc851 := hci) .. =>
              exact hof (fun cl hcl => hsub_ci cl (by rw [hci]; simp [hcl])) e14
            | .RPrj (cs12 := c12) (ev14 := e14) (hc926 := hci) .. =>
              exact hof (fun cl hcl => hsub_ci cl (by rw [hci]; simp [hcl])) e14
            | .Recr (cs12 := c12) (ev14 := e14) (hc1071 := hci) .. =>
              exact hof (fun cl hcl => hsub_ci cl (by rw [hci]; simp [hcl])) e14
          obtain ⟨c_ld, hrec_ld⟩ := hload_rec
          rw [ha_cprj_eq] at hrec_ld
          have hwfC := L1.projConstant_wireWF_cPrj im.toUInt64 j.toUInt64 bBlkM
          rw [hbBlkM_eq] at hwfC
          have hc_eq : (⟨.cPrj ⟨im.toUInt64, j.toUInt64, Bm⟩, #[], #[], #[], #[]⟩ : Ixon.Constant) = c_ld :=
            hS.record_eq ((hS.recordOf_eq_recordAt _).symm.trans hrec_ld) hhash_cprj rfl
              (Ixon.Verify.deConstantExact_serConstant _ hwfC)
          rwa [← hc_eq] at hrec_ld
        -- 3. Read `ru.rhs` under `id` and `recParam ps`, and get scope + canonical annotation.
        have hself_ok : ∀ i x, (L1.blockRecurAddrs rb rs.toList)[i]? = some x →
            ∃ m k, blockSelf t rb rs i = some m ∧ m = .ok k := LoadedReads.blockSelf_ok t rb rs
        obtain ⟨rhsP, hreadP⟩ := LoadedReads.exprReader_read_ok ht hraw_rhs hself_ok hblob
        obtain ⟨rhs₀, hread₀⟩ := LoadedReads.exprReader_read_ok ht (param := Ix.Kernel.Reader.recParam ps)
          hraw_rhs hself_ok hblob
        -- Extract `validate_expr_well_scoped` from `ev_iota`
        have ext_h_m155 : Heap.Extends h m155 :=
          ext_ga.trans (ev_cprj.heap_extends.trans ev_ci.heap_extends)
        obtain ⟨_, _, h_sc_in, h_sc_out, v_sc, cs_sc, ext_sc_in, hcall_sc_in, ev_sc⟩ :=
          check_iota_rule_scope_call ev_iota
        have hcall_sc : (⟨"KernelCheck::validate_expr_well_scoped",
            [x_rhs, .field 0, .field (ps.length : F)], h_sc_in⟩ : Call F) ∈ calls :=
          hsub_iota _ hcall_sc_in
        obtain ⟨_, hrhsP_lbb, hrhsP_def⟩ :=
          Assembly.validate_expr_well_scoped_spec hbd (by rw [hps_len]; exact hlvls_lt)
            hraw_rhs (ext_h_m155.trans ext_sc_in) hreadP ev_sc hcall_sc
        obtain ⟨hrhs₀_lbb, hrhs₀_def⟩ :=
          Typing.read_recParam_scoped hperm hread₀ hreadP hrhsP_lbb hrhsP_def
        have hrhs₀_nofvar : rhs₀.hasFvar = false := Assembly.memberReader_read_noFvar hread₀
        obtain ⟨rhsA, hcanon_rhs, hann_rhs, htm_rhs⟩ :=
          annotation_canon_gen_exact ht hperm (by rw [hps_len]; exact hlvls_lt)
            (LoadedReads.blockSelf_key t rb rs) hagree hraw_rhs built hplan_rhs hlev_rhs
            hread₀ hrhs₀_lbb hrhs₀_def
        let rl₀ : RecRule .anon :=
          Ix.Kernel.RecRule.mk (Core.keyOf t (ctorAddr Bm im j)) ru.fields.toNat 0 .inert rhs₀
            false false false
        have hrl_ctor : rl₀.ctor = Core.keyOf t (ixAddr a_cprj) := by
          simp only [rl₀, ha_cprj_eq, LoadedReads.ctorAddr_eq_cprjAddr]
        -- 4. Invert `ev_iota` for `RuleFacts`
        obtain ⟨inv⟩ := Decl.check_iota_rule_invR ev_iota
        -- 5. Recursive call on `rus`
        have hj1_eq : v451 = .field ((j + 1 : Nat) : F) := by
          rw [SubstAux.add_ok op_j1, Nat.cast_add, Nat.cast_one]
        rw [hj1_eq] at ev_rec
        have ext_h_m77 : Heap.Extends h m77 := ext_h_m155.trans ev_iota.heap_extends
        have ext_m42_m77 : Heap.Extends m42 m77 :=
          ev_cprj.heap_extends.trans (ev_ci.heap_extends.trans ev_iota.heap_extends)
        have hpins_mono : RepList kexprListEnum
            (fun h P p => Decl.TmExact (Core.keyOf t) 0 zeroGhost h rP P p ∧
              ∀ a, AddrIn h p a → UsedRef E₀ rb (ixAddr a)) m77
            (pins.map (Core.posOf ps)) pins_ptr :=
          RepLinkedList.mono (fun _ _ _ _ ext ⟨ht', hu'⟩ =>
            ⟨ht'.mono ext, fun a ha => hu' a (Binding.TmExact.addrIn_back ht' ext a ha)⟩)
            ext_h_m77 hpins
        have hty_used_m77 : ∀ a, AddrIn m77 ty_r a → UsedRef E₀ rb (ixAddr a) :=
          fun a ha => hty_used a (Binding.TmExact.addrIn_back (hty_rep 0 zeroGhost) ext_h_m77 a ha)
        obtain ⟨rules_rest, rhss_rest, thms_rest, rlsCan_rest, remBytes, hstr_out, hrr_rest,
            hsc_rest, hcan_rest, hf2_rest, hcprj_rest, hfacts_rest⟩ :=
          ih (fun ru' hru' => hrus_sub ru' (List.mem_cons_of_mem _ hru'))
            (j := j + 1) (root := root + 1) (by simp at hlen_j; omega) hctors_lt hsub_rec
            (RCRep.mono ext_h_m77 hrc) (Bytes.repAddressRef_heapMono₂ addrTy ext_h_m77 hrm)
            (Bytes.repAddressRef_heapMono₂ addrTy ext_h_m77 hbBlkM)
            (RepLinkedList.mono (Bytes.repAddressRef_heapMono₂ addrTy) ext_h_m77 hsrc)
            (RepLinkedList.mono (Bytes.repAddressRef_heapMono₂ addrTy) ext_h_m77 hdst)
            (AddrMapAll.mono (fun _ _ _ _ _ x => x) ext_h_m77 haset)
            (hty_rep.mono ext_h_m77) hty_used_m77 (hilvls.mono ext_h_m77) hpins_mono
            (hrls_rest.mono ext_h_m77 (fun _ hm => hm)) (hstr_m42.mono ext_m42_m77) ev_rec
        -- 6. Assemble canonical rules and outputs
        let rlCan : RecRule .anon := { rl₀ with rhs := rhsA, k := rc.k, ctorParams := rc.params.toNat }
        refine ⟨rl₀ :: rules_rest, rhsA :: rhss_rest, Core.keyOf t (ixAddr a_t) :: thms_rest,
          rlCan :: rlsCan_rest, remBytes, hstr_out, ?_, ?_, ?_, .cons rfl hf2_rest, ?_, ?_⟩
        · show List.Forall₂ _ ((ru, j) :: rus.zipIdx (j + 1)) (rl₀ :: rules_rest)
          exact .cons ⟨rhs₀, hread₀, rfl⟩ hrr_rest
        · intro rl hrl
          rcases List.mem_cons.mp hrl with rfl | hrl'
          · exact ⟨hrhs₀_lbb, hrhs₀_def⟩
          · exact hsc_rest rl hrl'
        · unfold LoadedReads.canonRules
          rw [show rl₀.rhs = rhs₀ from rfl, hcanon_rhs, Option.bind_some, hcan_rest]
          rfl
        · intro idx hlt
          cases idx with
          | zero => simpa using hrec_cprj
          | succ idx' =>
            have hlt' : idx' < rus.length := by simp at hlt; omega
            simpa [Nat.add_assoc, Nat.add_comm 1 idx'] using hcprj_rest idx' hlt'
        · -- Discharge `RulesFacts` at any `FamilyStepEnv`
          intro L adv E env recsBlk recsTys hSE hadvHyp hdefSrc hmodels hnp_ty hleaves
          refine ⟨?_, hfacts_rest recsBlk recsTys hSE hadvHyp hdefSrc hmodels hnp_ty hleaves⟩
          -- `hty_cells` and `hrhs_cells` and `hpins_rep` at `m155`
          have hused_rb : ∀ x, UsedRef E₀ rb x →
              (∃ ci, env.find? (Core.keyOf t x) = some ci) ∨ x ∈ srcAs.map ixAddr := fun x hx =>
            usedRef_stored_or_src_lists hB hR htypes hctors hrecs hSE (Or.inr hx) (hrecRefs x hx)
          have hty_cells_m155 : ∀ a, AddrIn m155 ty_r a →
              (∃ ci, env.find? (Core.keyOf t (ixAddr a)) = some ci) ∨ ixAddr a ∈ srcAs.map ixAddr :=
            fun a ha => hused_rb _ (hty_used a
              (Binding.TmExact.addrIn_back (hty_rep 0 zeroGhost) ext_h_m155 a ha))
          have hrhs_cells_m155 : ∀ a, AddrIn m155 x_rhs a →
              (∃ ci, env.find? (Core.keyOf t (ixAddr a)) = some ci) ∨ ixAddr a ∈ srcAs.map ixAddr := by
            intro a ha
            have ha_h := Binding.TmExact.addrIn_back (htm_rhs 0 zeroGhost) ext_h_m155 a ha
            rcases L1.RawConvExpr.addrIn_used hraw_rhs a ha_h with ⟨i, hi_used, hi_ref⟩ | hrec_mem
            · have hu : UsedRef E₀ rb (ixAddr a) := by
                refine ⟨crb, i, hR.record, ?_, by rw [← Array.getElem?_toList]; exact hi_ref⟩
                unfold usedRefIdxs; rw [hR.muts]
                rcases hi_used with hi_e | ⟨s_sh, hs_sh, hi_s⟩
                · have hmem_rs : Ixon.MutConst.recr rc ∈ rs.toList :=
                    List.mem_of_getElem? (by rw [Array.getElem?_toList]; exact hrk)
                  exact List.mem_append_right _ (List.mem_flatMap.mpr
                    ⟨.recr rc, hmem_rs, List.mem_append_right _
                      (List.mem_flatMap.mpr ⟨ru, hrus_sub ru List.mem_cons_self, hi_e⟩)⟩)
                · exact List.mem_append_left _ (List.mem_flatMap.mpr ⟨s_sh, hs_sh, hi_s⟩)
              exact hused_rb _ hu
            · right
              have hmem_recAs : ixAddr a ∈ recAs.map ixAddr := by
                rw [hrecs, ← blockRecurAddrs_eq_mapIdx]; exact hrec_mem
              simp only [srcAs, List.map_append, List.mem_append]
              exact Or.inr hmem_recAs
          have hpins_m155 : RepList kexprListEnum
              (fun h P p => Decl.TmExact (Core.keyOf t) 0 zeroGhost h rP P p ∧
                ∀ a, AddrIn h p a →
                  (∃ ci, env.find? (Core.keyOf t (ixAddr a)) = some ci) ∨ ixAddr a ∈ srcAs.map ixAddr)
              m155 (pins.map (Core.posOf ps)) pins_ptr :=
            repList_map_pred (fun _ _ ⟨ht', hu'⟩ => ⟨ht', fun a ha => hused_rb _ (hu' a ha)⟩)
              (RepLinkedList.mono (fun _ _ _ _ ext ⟨ht', hu'⟩ =>
                ⟨ht'.mono ext, fun a ha => hu' a (Binding.TmExact.addrIn_back ht' ext a ha)⟩)
                ext_h_m155 hpins)
          -- Build `hcty_of_find` by splitting `Bm = B` vs `Bm ≠ B`.
          have hcty_of_find : ∀ ci_gc, env.find? (g rl₀.ctor) = some ci_gc →
              ∃ cvj : ConstantVal .anon,
                RuleCtor env (nonrecsBlk ++ recsBlk) (nonrecsTys ++ recsTys) rl₀.ctor cvj
                  indM.params.toNat ru.fields.toNat ∧
                ci_gc.toConstantVal.levelParams.length = cvj.levelParams.length ∧
                cvj.type.allLevelParamsDefined cvj.levelParams = true ∧
                Decl.NoProjIn srcKeys cvj.type = true ∧
                Tm (famKey t env srcAs) 0 zeroGhost m155 0 (Core.posOf cvj.levelParams cvj.type) x_cty := by
            intro ci_gc hfind_gc
            by_cases hBmB : Bm = B
            · -- Case 1: constructor of this block `B`
              have hrecBM' : recordOf E₀ B = some cbM := hBmB ▸ hrecBM
              have hrec_cprj' : recordOf E₀ (cprjAddr B im j) =
                  some ⟨.cPrj ⟨im.toUInt64, j.toUInt64, B⟩, #[], #[], #[], #[]⟩ := hBmB ▸ hrec_cprj
              have ha_cprj_eq' : ixAddr a_cprj = cprjAddr B im j := hBmB ▸ ha_cprj_eq
              have hcb_eq : cbM = cb := Option.some.inj (hrecBM'.symm.trans hB.record)
              subst cbM
              have hms_eq : msM = ms := Ixon.ConstantInfo.muts.inj (hmutsM.symm.trans hB.muts)
              subst msM
              have hj_lt_ctors : j < indM.ctors.size := by simp at hlen_j; omega
              have hct_get : indM.ctors[j]? = some indM.ctors[j] := Array.getElem?_eq_getElem hj_lt_ctors
              obtain ⟨pos, ty₀C, tyAC, hpos_lt, hblk_pos, htys_pos, hreadC, hlbbC, hdefC, hcanC,
                  hA_defC, hstepC⟩ := hctorLookup im j indM indM.ctors[j] hmsM hct_get
              obtain ⟨hnpC, hlvls_gc⟩ := hstepC hSE hadvHyp hdefSrc
              -- Load `ev_ci` via `L1.get_ci_block_trace_spec` to obtain `TmExact` for `x_cty`
              obtain ⟨_, cC, hhC, hbaC, hexC, -, htrC⟩ :=
                L1.get_ci_block_trace_spec (bounded_sub hsub_ci hbd) ha_cprj_m117 ev_ci
              have hrecAtC : Ix.Cert.recordAt E₀ (ixAddr a_cprj) =
                  some ⟨.cPrj ⟨im.toUInt64, j.toUInt64, B⟩, #[], #[], #[], #[]⟩ := by
                rw [← hS.recordOf_eq_recordAt, ha_cprj_eq']; exact hrec_cprj'
              have hcC_eq : cC = ⟨.cPrj ⟨im.toUInt64, j.toUInt64, B⟩, #[], #[], #[], #[]⟩ :=
                hS.record_eq hrecAtC (Core.hashed_mono hsub_ci hhC) hbaC hexC
              subst hcC_eq
              unfold L1.GetCIBlockTraceResult at htrC
              simp only at htrC
              obtain ⟨_, _, blkBytesC, cb', ms', ind', ct', blobsC, treeC, planC, vC, hhBlkC,
                  hbaBlkC, hexBlkC, hmuts', hmi', hct', hhpC, builtC, hplanC, hldvC, hrawC, hlevC⟩ := htrC
              have hcb'_eq : cb' = cb :=
                hS.record_eq ((hS.recordOf_eq_recordAt B).symm.trans hB.record)
                  (Core.hashed_mono hsub_ci hhBlkC) hbaBlkC hexBlkC
              subst cb'
              have hms'_eq : ms' = ms := Ixon.ConstantInfo.muts.inj (hmuts'.symm.trans hB.muts)
              subst ms'
              have him_toNat : im.toUInt64.toNat = im :=
                toNat_toUInt64_lt_r (Nat.lt_trans him_lt (by decide))
              have hj_toNat : j.toUInt64.toNat = j :=
                toNat_toUInt64_lt_r (Nat.lt_trans (m := 72057594037927936) (by omega) (by decide))
              rw [him_toNat, Array.getElem?_toList, hmsM] at hmi'
              have hind'_eq : ind' = indM := Ixon.MutConst.indc.inj (Option.some.inj hmi').symm
              subst ind'
              rw [hj_toNat, Array.getElem?_toList, hct_get] at hct'
              have hct'_eq : ct' = indM.ctors[j] := (Option.some.inj hct').symm
              subst ct'
              rw [him_toNat, hj_toNat] at hplanC
              rw [him_toNat] at hrawC
              obtain ⟨hct_lvls_lt, _, hct_np_lt, hct_nf_lt, _, tyPtrC, _, _, _, _, hvC_eq, rtyC⟩ := hrawC
              have hvC_ld := Except.ok.inj (ld_ci.symm.trans hldvC)
              rw [hvC_eq] at hvC_ld
              injection hvC_ld with _ _ hca
              injection hca with _ hca
              injection hca with hcty_eq hca
              injection hca with _ hca; injection hca with _ hca; injection hca with _ hca
              injection hca with hcnp_eq hca
              injection hca with hcnf_eq _
              subst hcty_eq
              have hnp_match : indM.ctors[j].params.toNat = indM.params.toNat :=
                nat_eq_of_field_eq_u56_r hct_np_lt hcnp_lt
                  (Value.field.inj (hcnp_eq.symm.trans heq_cnp))
              have hnf_match : indM.ctors[j].fields.toNat = ru.fields.toNat :=
                nat_eq_of_field_eq_u56_r hct_nf_lt hru_nf
                  (Value.field.inj (hcnf_eq.symm.trans heq_rnf.symm))
              have hblobC : ∀ x bs, (x, bs) ∈ blobsC → E₀.blobs.get? x = some bs := by
                intro x bs hm
                obtain ⟨hhx, hxa⟩ := hhpC (x, bs) hm
                have hrun := hS.blobs bs (Core.hashed_mono hsub_ci hhx)
                rwa [hxa] at hrun
              obtain ⟨_, tyPtrC', _, hvcC, hblC⟩ := hlevC
              rw [hvC_eq] at hvcC
              injection hvcC with _ _ hca'; injection hca' with _ hca'; injection hca' with htp' _
              subst htp'
              obtain ⟨tyAC', hcanC', _, htmC'⟩ :=
                annotation_canon_range_exact ht hct_lvls_lt (LoadedReads.blockSelf_key t B ms)
                  (L1.BlobReadAgreement.of_mem hblobC) rtyC builtC hplanC hblC hreadC hlbbC hdefC
              have htyAC_eq : tyAC' = tyAC := Option.some.inj (hcanC'.symm.trans hcanC)
              subst tyAC'
              have htmC_pos : Decl.TmExact (Core.keyOf t) 0 zeroGhost m155 0
                  (Core.posOf (List.range indM.ctors[j].lvls.toNat) tyAC) x_cty := by
                rw [Decl.posOf_range]; exact htmC' 0 zeroGhost
              -- Cells of `x_cty` are either stored in `env` or in `srcAs`
              have hcty_cells : ∀ a, AddrIn m155 x_cty a →
                  (∃ ci, env.find? (Core.keyOf t (ixAddr a)) = some ci) ∨ ixAddr a ∈ srcAs.map ixAddr := by
                intro a ha
                rcases L1.RawConvExpr.addrIn_used rtyC a ha with ⟨i_r, hi_u, hi_ref⟩ | hrec_mem
                · have huB : UsedRef E₀ B (ixAddr a) := by
                    refine ⟨cb, i_r, hB.record, ?_, by rw [← Array.getElem?_toList]; exact hi_ref⟩
                    unfold usedRefIdxs; rw [hB.muts]
                    rcases hi_u with hi_e | ⟨s_sh, hs_sh, hi_s⟩
                    · have hmem_ms : Ixon.MutConst.indc indM ∈ ms.toList :=
                        List.mem_of_getElem? (by rw [Array.getElem?_toList]; exact hmsM)
                      have hmem_ct : indM.ctors[j] ∈ indM.ctors.toList :=
                        Array.mem_toList_iff.mpr (Array.getElem_mem hj_lt_ctors)
                      exact List.mem_append_right _ (List.mem_flatMap.mpr
                        ⟨.indc indM, hmem_ms, List.mem_append_right _
                          (List.mem_flatMap.mpr ⟨indM.ctors[j], hmem_ct, hi_e⟩)⟩)
                    · exact List.mem_append_left _ (List.mem_flatMap.mpr ⟨s_sh, hs_sh, hi_s⟩)
                  rcases hSE.blockRefs (ixAddr a) huB with hst | hnd
                  · left; exact Option.isSome_iff_exists.mp hst
                  · exact usedRef_stored_or_src_lists hB hR htypes hctors hrecs hSE (Or.inl huB) (Or.inr hnd)
                · right
                  have hmem_typeAs : ixAddr a ∈ typeAs.map ixAddr := by
                    rw [htypes, ← blockRecurAddrs_eq_mapIdx]; exact hrec_mem
                  simp only [srcAs, List.map_append, List.mem_append]
                  exact Or.inl (Or.inl hmem_typeAs)
              let cvj : ConstantVal .anon :=
                ⟨Core.keyOf t (cprjAddr B im j), List.range indM.ctors[j].lvls.toNat, tyAC⟩
              have hrc_eq : rl₀.ctor = Core.keyOf t (cprjAddr B im j) := by
                simp [rl₀, hBmB, LoadedReads.ctorAddr_eq_cprjAddr]
              refine ⟨cvj, ?_, ?_, hA_defC, hnpC, ?_⟩
              · right
                refine ⟨pos, ⟨Core.keyOf t (cprjAddr B im j), List.range indM.ctors[j].lvls.toNat, ty₀C⟩,
                  tyAC, ?_, ?_, hrc_eq.symm, rfl⟩
                · rw [List.getElem?_append_left hpos_lt, hblk_pos, hnp_match, hnf_match]
                · rw [List.getElem?_append_left (by omega), htys_pos]
              · rw [hrc_eq] at hfind_gc
                simpa [cvj] using hlvls_gc ci_gc hfind_gc
              · exact tm_famKey_of_cells htmC_pos.toTm hcty_cells
            · -- Case 2: external constructor (`Bm ≠ B`), already stored in `env`
              have hnot_src : cprjAddr Bm im j ∉ srcAs.map ixAddr :=
                cprjAddr_not_mem_src hB hR htypes hctors hrecs hBmB hrec_cprj
              have hnot_srcK : rl₀.ctor ∉ srcKeys := by
                intro hmem
                obtain ⟨b, hb, hkeq⟩ := List.mem_map.mp hmem
                have hax : ixAddr b = cprjAddr Bm im j := by
                  apply Core.keyOf_inj htwf
                  simpa [rl₀, LoadedReads.ctorAddr_eq_cprjAddr] using hkeq
                exact hnot_src (List.mem_map.mpr ⟨b, hb, hax⟩)
              have hg_fix : g rl₀.ctor = rl₀.ctor :=
                aliasMap_out_of_zip (ks := srcKeys) (ds := dstKeys) (by
                  cases hc : srcKeys.contains rl₀.ctor with
                  | false => rfl
                  | true => exact absurd (by simpa using hc) hnot_srcK)
              rw [hg_fix] at hfind_gc
              have hfind_a : env.find? (Core.keyOf t (ixAddr a_cprj)) = some ci_gc := by
                rwa [← hrl_ctor]
              let sc : ScopedCtx := Core.Ctx.stored ⟨E, env, t, lim⟩
              have hκa : sc.κ (ixAddr a_cprj) = Core.keyOf t (ixAddr a_cprj) :=
                Ctx.stored_key_of_find (c := ⟨E, env, t, lim⟩) hfind_a
              have hne_a : sc.κ (ixAddr a_cprj) ≠ unresolvedKey := by
                rw [hκa]; exact Resolved.ne
              have hgood_ci : Core.Good ⟨E, env, t, lim⟩ cs169 :=
                (hSE.store.good env lim).sub hsub_ci
              obtain ⟨ci2, hfind2, v_ci, hld_ci', hciRep⟩ :=
                hSE.prefixInv.loads.getCI v_cprj p163 m117 m155 cs169 a_cprj ev_ci trivial hne_a
                  (CoreGood.ofRaw hgood_ci (fun _ _ => trivial)) ha_cprj_m117
              rw [hκa] at hfind2
              have hci2_eq : ci2 = ci_gc := Option.some.inj (hfind2.symm.trans hfind_a)
              subst hci2_eq
              have hv_eq : v_ci = .construct kciEnum "Ctor"
                  [w186, x_cty, w187, w188, w189, x_cnp, x_cnf, w190] :=
                Except.ok.inj (hld_ci'.symm.trans ld_ci)
              cases hciRep with
              | @ctor _ _ _ _ _ _ _ _ cvj cnP' cnF' hv_c hnp_eq_c hnf_eq_c hcounts_c _ =>
                injection hv_eq with _ _ hargs_c
                injection hargs_c with _ hargs_c
                injection hargs_c with hcty_eq hargs_c
                injection hargs_c with _ hargs_c
                injection hargs_c with _ hargs_c
                injection hargs_c with _ hargs_c
                injection hargs_c with hcnp_eq hargs_c
                injection hargs_c with hcnf_eq _
                subst hcty_eq
                have hnp_match : cnP' = indM.params.toNat :=
                  nat_eq_of_field_eq_u56_r hcounts_c.1 hcnp_lt
                    (Value.field.inj (hnp_eq_c.symm.trans (hcnp_eq.trans heq_cnp)))
                have hnf_match : cnF' = ru.fields.toNat :=
                  nat_eq_of_field_eq_u56_r hcounts_c.2 hru_nf
                    (Value.field.inj (hnf_eq_c.symm.trans (hcnf_eq.trans heq_rnf.symm)))
                subst hnp_match hnf_match
                have hcwf := hSE.prefixInv.store.store.wf _ (List.mem_of_find?_eq_some hfind_gc)
                have hdef_c : cvj.type.allLevelParamsDefined cvj.levelParams = true := hcwf.2.1
                have hres_c : cvj.type.constsResolve env = true := hcwf.2.2.1
                have hnp_c : Decl.NoProjIn srcKeys cvj.type = true :=
                  noProjIn_of_constsResolve_fresh (fun k hk => by
                    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hk
                    exact hSE.fresh (ixAddr b) (src_mem_famAddr hB hR htypes hctors hrecs
                      (List.mem_map.mpr ⟨b, hb, rfl⟩))) cvj.type hres_c
                exact ⟨cvj, Or.inl hfind_gc, rfl, hdef_c, hnp_c,
                  tm_famKey_of_stored (hv_c.2.2.2 0 zeroGhost)⟩
              | axio _ | opaq _ | defn _ _ | thm _ _ | quot _ _ | induct _ _ _
              | recr _ _ _ _ _ _ _ _ _ _ _ =>
                injection hv_eq with _ ht _; exact absurd ht (by decide)
          -- Invoke `CallIotaRule.check_iota_rule_facts`!
          have hrm_stored : ∃ ci, env.find? (Core.keyOf t (ixAddr a_rm)) = some ci :=
            hmodels a_rm hrm_in_dst
          have inv' : Decl.CheckIotaRuleInvR rcV rm (.field (ps.length : F)) ty_r (.field (rP : F))
              (.field ((mI - rP : Nat) : F)) x_rhs v_cprj x_cty
              (.field (indM.params.toNat : F)) (.field (ru.fields.toNat : F))
              ilvls pins_ptr x_t src dst aset m155 cs290 := by
            rw [← heq_cnp, heq_rnf]; exact inv
          exact check_iota_rule_facts ht hbd hS hH hSE hlenSD hadvHyp hdefSrc hmodels
            (by rw [hps_len]; exact hlvls_lt) hperm hrp_le hmi_lt hcnp_lt hru_nf rfl
            hrhs₀_lbb hrhs₀_nofvar hann_rhs hmaj hlvls_def hpins_ok hnp_ty hleaves
            hsub_iota (RCRep.mono ext_h_m155 hrc)
            (Bytes.repAddressRef_heapMono₂ addrTy ext_h_m155 hrm) hrm_key hrm_stored
            (Bytes.repAddressRef_heapMono₂ addrTy ev_ci.heap_extends ha_cprj_m117) hrl_ctor.symm
            (Bytes.repAddressRef_heapMono₂ addrTy (ev_cprj.heap_extends.trans ev_ci.heap_extends) ha_t_m42)
            (RepLinkedList.mono (Bytes.repAddressRef_heapMono₂ addrTy) ext_h_m155 hsrc)
            (RepLinkedList.mono (Bytes.repAddressRef_heapMono₂ addrTy) ext_h_m155 hdst)
            (AddrMapAll.mono (fun _ _ _ _ _ x => x) ext_h_m155 haset)
            (hty_rep.mono ext_h_m155) hty_cells_m155
            (htm_rhs.mono ext_h_m155) hrhs_cells_m155
            hcty_of_find (hilvls.mono ext_h_m155) hpins_m155 inv'

/-! ## Per-recursor data and the `check_recs` walk -/

private theorem piDomAt_eq_of_stripPis :
    ∀ (n : Nat) {ty : KExpr} {bs : List (KExpr × Ix.Kernel.BinderMeta)} {d b : KExpr}
      {m : Ix.Kernel.BinderMeta},
      ty.stripPis n = some (bs, .forallE d b m) → Core.piDomAt n ty = some d
  | 0, .forallE d b m, _, _, _, _, hs => by
    simp only [Expr.stripPis, Option.some.injEq, Prod.mk.injEq, Expr.forallE.injEq] at hs
    obtain ⟨_, rfl, _, _⟩ := hs; rfl
  | n + 1, .forallE T B _, _, _, _, _, hs => by
    simp only [Expr.stripPis] at hs
    cases hsb : B.stripPis n with
    | none => simp [hsb] at hs
    | some p =>
      rcases p with ⟨bs', rem'⟩
      rw [hsb] at hs
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hs
      obtain ⟨_, rfl⟩ := hs
      exact piDomAt_eq_of_stripPis n hsb
  | 0, .bvar _, _, _, _, _, hs | 0, .fvar _ _, _, _, _, _, hs | 0, .sort _, _, _, _, _, hs
  | 0, .const _ _, _, _, _, _, hs | 0, .app _ _, _, _, _, _, hs | 0, .lam _ _ _, _, _, _, _, hs
  | 0, .letE _ _ _ _, _, _, _, _, hs | 0, .lit _, _, _, _, _, hs | 0, .proj _ _ _, _, _, _, _, hs => by
    simp [Expr.stripPis] at hs
  | _ + 1, .bvar _, _, _, _, _, hs | _ + 1, .fvar _ _, _, _, _, _, hs | _ + 1, .sort _, _, _, _, _, hs
  | _ + 1, .const _ _, _, _, _, _, hs | _ + 1, .app _ _, _, _, _, _, hs | _ + 1, .lam _ _ _, _, _, _, _, hs
  | _ + 1, .letE _ _ _ _, _, _, _, _, hs | _ + 1, .lit _, _, _, _, _, hs | _ + 1, .proj _ _ _, _, _, _, _, hs =>
    nomatch hs

/-- **All semantic facts for one recursor `k` of the family record `rb`**, produced from one
iteration of `KernelModeled::check_recs` paired with its `MemberValItem` from `evRecsVal`. -/
structure RecMemberData (calls : List (Call F)) (bAddr : _root_.Address)
    (t : Ix.Kernel.RoleTable) (E₀ : Ixon.Env) (lim : Option Nat) (csFam : List (Call F))
    (B rb : _root_.Address) (cb crb : Ixon.Constant) (ms rs : Array Ixon.MutConst)
    (advAs srcAs dstAs recAs : List Bytes.Address)
    (nonrecsBlk : List (ConstantInfo .anon)) (nonrecsTys : List KExpr)
    (k : Nat) (rc : Ixon.Recursor) (aRec aMd : Bytes.Address) where
  ps : List LevelParam
  ty₀ : KExpr
  tyA : KExpr
  rules₀ : List (RecRule .anon)
  rhss : List KExpr
  thms : List KKey
  -- Major-premise inductive data
  aIndM : Bytes.Address
  cmM : Ixon.Constant
  ipM : Ixon.InductiveProj
  cbM : Ixon.Constant
  msM : Array Ixon.MutConst
  indM : Ixon.Inductive
  hrecM : recordOf E₀ (ixAddr aIndM) = some cmM
  hinfoM : cmM.info = .iPrj ipM
  hcmM_can : cmM = memberProjection ipM.block ipM.idx.toNat (.indc indM)
  haIndM_can : ixAddr aIndM = memberAddr ipM.block ipM.idx.toNat (.indc indM)
  hrecBM : recordOf E₀ ipM.block = some cbM
  hmutsM : cbM.info = .muts msM
  hmsM : msM[ipM.idx.toNat]? = some (.indc indM)
  husedIndM : UsedRef E₀ rb (ixAddr aIndM)
  hcntRules : rc.rules.size = indM.ctors.size
  hcntLt : indM.ctors.size < 72057594037927936
  -- Canonical reading & FamRecCanon
  hnotK : rc.k = false
  hps_len : ps.length = rc.lvls.toNat
  hty_lbb : ty₀.looseBVarsBounded 0 = true
  hty_def : ty₀.allLevelParamsDefined ps = true
  hrules_sc : ∀ rl ∈ rules₀, rl.rhs.looseBVarsBounded 0 = true ∧ rl.rhs.allLevelParamsDefined ps = true
  hcanon_ty : LoadedReads.canonAnn crb ps ((L1.mutsRootOffset rs.toList k : Nat) : F) rc.typ ty₀ = some tyA
  hcanon_rules : ∃ rlsCan,
    LoadedReads.canonRules crb ps rc.k rc.params.toNat
      (((L1.mutsRootOffset rs.toList k : Nat) : F) + 1) rc.rules.toList rules₀ = some rlsCan ∧
    List.Forall₂ (fun (rl : RecRule .anon) (rhsA : KExpr) => rl.rhs = rhsA) rlsCan rhss
  -- Scoping (`typesScoped`)
  hment : ∀ b ∈ recAs, tyA.mentionsConst (Core.keyOf t (ixAddr b)) = false
  -- Major-premise head & rules' constructors (for `MajorRefs` and `FamRecCompanion`)
  hhead : ∃ D lvls pins,
    Core.piDomAt (rc.params.toNat + rc.motives.toNat + rc.minors.toNat + rc.indices.toNat) tyA = some D ∧
    D.getAppFn = .const (Core.keyOf t (ixAddr aIndM)) lvls ∧
    majorShape tyA (rc.params.toNat + rc.motives.toNat + rc.minors.toNat + rc.indices.toNat)
      (rc.params.toNat + rc.motives.toNat + rc.minors.toNat) indM.params.toNat = some (lvls, pins)
  hrules_len : rules₀.length = rc.rules.size
  hrules_ctor : ∀ j rl, rules₀[j]? = some rl →
    rl.ctor = Core.keyOf t (cprjAddr ipM.block ipM.idx.toNat j)
  hrules_recCprj : ∀ j, j < rules₀.length →
    recordOf E₀ (cprjAddr ipM.block ipM.idx.toNat j) =
      some ⟨.cPrj ⟨ipM.idx.toNat.toUInt64, j.toUInt64, ipM.block⟩, #[], #[], #[], #[]⟩
  -- `ReadsIn` once `InLogic cbM` is known (from `hrecRefs` + `hcovLogic` / `NeedOk`)
  hreads : InLogic cbM →
    ReadsIn t (recordOf E₀) (fun x => E₀.blobs.get? x) (memberAddr rb k (.recr rc))
      (.recInfo ⟨Core.keyOf t (rprjAddr rb k), ps, ty₀⟩
        (rc.params.toNat + rc.motives.toNat + rc.minors.toNat + rc.indices.toNat)
        (rc.params.toNat + rc.motives.toNat + rc.minors.toNat) rules₀)
  -- `MemberFacts` and `RulesFacts` at any `FamilyStepEnv`
  hmemFacts : ∀ {L : Ix.Kernel.Env .anon → NativeFam .anon → Prop}
    {adv : _root_.Address → Prop} {E : Ixon.Env} {env : Ix.Kernel.Env .anon},
    FamilyStepEnv.{u} L calls t E₀ lim B cb rb crb adv E env →
    adv (ixAddr aMd) →
    (∀ k' ∈ srcAs.map (fun b => Core.keyOf t (ixAddr b)),
      ∃ cvm mval hint, env.find? (aliasMap ((srcAs.map fun b => Core.keyOf t (ixAddr b)).zip
        (dstAs.map fun b => Core.keyOf t (ixAddr b))) k') = some (.defnInfo cvm mval hint)) →
    MemberFacts env (aliasMap ((srcAs.map fun b => Core.keyOf t (ixAddr b)).zip
      (dstAs.map fun b => Core.keyOf t (ixAddr b))))
      (.recInfo ⟨Core.keyOf t (rprjAddr rb k), ps, ty₀⟩
        (rc.params.toNat + rc.motives.toNat + rc.minors.toNat + rc.indices.toNat)
        (rc.params.toNat + rc.motives.toNat + rc.minors.toNat) rules₀) tyA
  hrulesFacts : ∀ {L : Ix.Kernel.Env .anon → NativeFam .anon → Prop}
    {adv : _root_.Address → Prop} {E : Ixon.Env} {env : Ix.Kernel.Env .anon}
    (recsBlk : List (ConstantInfo .anon)) (recsTys : List KExpr),
    FamilyStepEnv.{u} L calls t E₀ lim B cb rb crb adv E env →
    adv (ixAddr aMd) →
    ((∀ a, AdviceIn csFam a → adv a) ∨
      ∀ a, AdviceListedIn advAs a →
        adv a ∨ ∀ ca x, recordOf E₀ a = some ca → ¬ ConstAddrOf a ca x) →
    (∀ k' ∈ srcAs.map (fun b => Core.keyOf t (ixAddr b)),
      ∃ cvm mval hint, env.find? (aliasMap ((srcAs.map fun b => Core.keyOf t (ixAddr b)).zip
        (dstAs.map fun b => Core.keyOf t (ixAddr b))) k') = some (.defnInfo cvm mval hint)) →
    (∀ b ∈ dstAs, ∃ ci, env.find? (Core.keyOf t (ixAddr b)) = some ci) →
    RulesFacts env (aliasMap ((srcAs.map fun b => Core.keyOf t (ixAddr b)).zip
      (dstAs.map fun b => Core.keyOf t (ixAddr b))))
      (nonrecsBlk ++ recsBlk) (nonrecsTys ++ recsTys)
      (Core.keyOf t (rprjAddr rb k)) ps tyA
      (rc.params.toNat + rc.motives.toNat + rc.minors.toNat + rc.indices.toNat)
      (rc.params.toNat + rc.motives.toNat + rc.minors.toNat)
      rules₀ rhss thms

/-- The `ConstantInfo` read for a recursor entry `RecMemberData`. -/
def RecMemberData.recInfo {calls bAddr t E₀ lim csFam B rb cb crb ms rs advAs srcAs dstAs recAs
    nonrecsBlk nonrecsTys k rc aRec aMd}
    (D : RecMemberData.{u} calls bAddr t E₀ lim csFam B rb cb crb ms rs advAs srcAs dstAs recAs
      nonrecsBlk nonrecsTys k rc aRec aMd) : ConstantInfo .anon :=
  .recInfo ⟨Core.keyOf t (rprjAddr rb k), D.ps, D.ty₀⟩
    (rc.params.toNat + rc.motives.toNat + rc.minors.toNat + rc.indices.toNat)
    (rc.params.toNat + rc.motives.toNat + rc.minors.toNat) D.rules₀

/-- **Constructs `FamRecCompanion` from `RecMemberData` and `RulesFacts`** for any full block
`(blk, tys)` whose names are distinct and fresh in `env`. -/
theorem famRecCompanion_of_data
    {calls : List (Call F)} {bAddr : _root_.Address} {t : Ix.Kernel.RoleTable}
    {E₀ : Ixon.Env} {lim : Option Nat} {csFam : List (Call F)}
    {B rb : _root_.Address} {cb crb : Ixon.Constant} {ms rs : Array Ixon.MutConst}
    {advAs srcAs dstAs recAs : List Bytes.Address}
    {nonrecsBlk : List (ConstantInfo .anon)} {nonrecsTys : List KExpr}
    {k : Nat} {rc : Ixon.Recursor} {aRec aMd : Bytes.Address}
    (ht : t.check = .ok ()) (hS : LoadedReads.RunStore calls E₀)
    (D : RecMemberData.{u} calls bAddr t E₀ lim csFam B rb cb crb ms rs advAs srcAs dstAs recAs
      nonrecsBlk nonrecsTys k rc aRec aMd)
    {env : Ix.Kernel.Env .anon} {g : KKey → KKey}
    {blk : List (ConstantInfo .anon)} {tys : List KExpr}
    (hblk_nd : (blk.map (·.name)).Nodup)
    (hblk_fresh : ∀ ci ∈ blk, env.find? ci.name = none)
    (hrulesF : RulesFacts env g blk tys (Core.keyOf t (rprjAddr rb k)) D.ps D.tyA
      (rc.params.toNat + rc.motives.toNat + rc.minors.toNat + rc.indices.toNat)
      (rc.params.toNat + rc.motives.toNat + rc.minors.toNat)
      D.rules₀ D.rhss D.thms) :
    FamRecCompanion E₀ t env blk tys D.tyA
      (rc.params.toNat + rc.motives.toNat + rc.minors.toNat + rc.indices.toNat)
      (rc.params.toNat + rc.motives.toNat + rc.minors.toNat) D.rules₀ := by
  have htwf : t.wf = true := by unfold Ix.Kernel.RoleTable.wf; rw [ht]; rfl
  let mI := rc.params.toNat + rc.motives.toNat + rc.minors.toNat + rc.indices.toNat
  let rP := rc.params.toNat + rc.motives.toNat + rc.minors.toNat
  obtain ⟨DM, lvlsM, pinsM, hpiM, hfnM, hmajM⟩ := D.hhead
  have hhead_uniq : ∀ (p : _root_.Address) (us : List Core.KLevel),
      (Core.piDomAt mI D.tyA).map (·.getAppFn) = some (.const (Core.keyOf t p) us) →
      p = ixAddr D.aIndM := by
    intro p us hhd
    rw [hpiM, Option.map_some, hfnM] at hhd
    injection hhd with hce; injection hce with hk _
    exact (Core.keyOf_inj htwf hk).symm
  refine ⟨?_, ⟨?_, ?_⟩, ?_⟩
  · -- `major`
    intro p us _ hhd
    rw [hhead_uniq p us hhd]
    exact ⟨D.cmM, (hS.recordOf_eq_recordAt _).symm.trans D.hrecM⟩
  · -- `rules.1`: `(D.rules₀.map (·.ctor)).Nodup`
    refine List.nodup_iff_injective_getElem.mpr fun ⟨i₁, hi₁⟩ ⟨i₂, hi₂⟩ heq => ?_
    simp only [List.length_map] at hi₁ hi₂
    simp only [List.getElem_map] at heq
    have hc1 := D.hrules_ctor i₁ D.rules₀[i₁] (List.getElem?_eq_getElem hi₁)
    have hc2 := D.hrules_ctor i₂ D.rules₀[i₂] (List.getElem?_eq_getElem hi₂)
    rw [hc1, hc2] at heq
    have ha_eq : cprjAddr D.ipM.block D.ipM.idx.toNat i₁ = cprjAddr D.ipM.block D.ipM.idx.toNat i₂ :=
      Core.keyOf_inj htwf heq
    have hr1 := D.hrules_recCprj i₁ hi₁
    have hr2 := D.hrules_recCprj i₂ hi₂
    rw [ha_eq] at hr1
    have hinfo := congrArg Ixon.Constant.info (Option.some.inj (hr1.symm.trans hr2))
    simp only [Ixon.ConstantInfo.cPrj.injEq, Ixon.ConstructorProj.mk.injEq] at hinfo
    have hsz : D.rules₀.length < 72057594037927936 := by
      rw [D.hrules_len, D.hcntRules]; exact D.hcntLt
    have hu64 : 72057594037927936 < UInt64.size := by decide
    have hi1_u64 : i₁.toUInt64.toNat = i₁ := toNat_toUInt64_lt_r (by omega)
    have hi2_u64 : i₂.toUInt64.toNat = i₂ := toNat_toUInt64_lt_r (by omega)
    have hi_eq : i₁ = i₂ := by rw [← hi1_u64, ← hi2_u64, hinfo.2.1]
    exact Fin.ext hi_eq
  · -- `rules.2`: `rl.ctor = Core.keyOf t (cprjAddr ip.block ip.idx.toNat j)`
    intro p cm ip us hhd hcm hip j rl hj
    have hp := hhead_uniq p us hhd
    subst hp
    have hcm_eq : cm = D.cmM := Option.some.inj (hcm.symm.trans ((hS.recordOf_eq_recordAt _).symm.trans D.hrecM))
    subst hcm_eq
    have hip_eq : ip = D.ipM := Ixon.ConstantInfo.iPrj.inj (hip.symm.trans D.hinfoM)
    subst hip_eq
    exact D.hrules_ctor j rl hj
  · -- `plain`
    intro rl cvj nP nF hrl hrc hplain
    -- Extract `RuleFacts` for `rl` from `hrulesF`
    have hrf_mem : ∀ {rls : List (RecRule .anon)} {rhss' : List KExpr} {thms' : List KKey},
        RulesFacts env g blk tys (Core.keyOf t (rprjAddr rb k)) D.ps D.tyA mI rP rls rhss' thms' →
        rl ∈ rls → ∃ rhsA thm, RuleFacts env g blk tys (Core.keyOf t (rprjAddr rb k)) D.ps D.tyA
          mI rP rl rhsA thm := by
      intro rls
      induction rls with
      | nil => intro _ _ _ hm; cases hm
      | cons r rs ih =>
        intro rhss' thms' hrf hm
        cases rhss' with
        | nil => cases hrf
        | cons rhsA rhss' =>
          cases thms' with
          | nil => cases hrf
          | cons thm thms' =>
            rcases List.mem_cons.mp hm with rfl | hm'
            · exact ⟨rhsA, thm, hrf.1⟩
            · exact ih hrf.2 hm'
    obtain ⟨rhsA, thm, cvj', cnP', cnF', lvls', pins', hrc', _, _, _, _, _, _, _, hmaj', _⟩ :=
      hrf_mem hrulesF hrl
    -- Uniqueness of `nP = cnP'` from `RuleCtor`
    have hnP_eq : nP = cnP' := by
      rcases hrc with hf1 | ⟨i1, cv1, tyC1, hb1, _, hn1, _⟩
      · rcases hrc' with hf2 | ⟨i2, cv2, tyC2, hb2, _, hn2, _⟩
        · have he := Option.some.inj (hf1.symm.trans hf2); injection he with _ hnp _
        · have hmem2 := List.mem_of_getElem? hb2
          have hfr := hblk_fresh _ hmem2
          simp only [ConstantInfo.name, ConstantInfo.toConstantVal] at hfr
          rw [hn2, hf1] at hfr; cases hfr
      · rcases hrc' with hf2 | ⟨i2, cv2, tyC2, hb2, _, hn2, _⟩
        · have hmem1 := List.mem_of_getElem? hb1
          have hfr := hblk_fresh _ hmem1
          simp only [ConstantInfo.name, ConstantInfo.toConstantVal] at hfr
          rw [hn1, hf2] at hfr; cases hfr
        · have hi1_lt : i1 < blk.length := (List.getElem?_eq_some_iff.mp hb1).1
          have hi2_lt : i2 < blk.length := (List.getElem?_eq_some_iff.mp hb2).1
          have heq_name : (blk.map (·.name))[i1]'(by simp [hi1_lt]) =
              (blk.map (·.name))[i2]'(by simp [hi2_lt]) := by
            simp only [List.getElem_map]
            have hg1 : blk[i1] = .ctorInfo cv1 nP nF :=
              Option.some.inj ((List.getElem?_eq_getElem hi1_lt).symm.trans hb1)
            have hg2 : blk[i2] = .ctorInfo cv2 cnP' cnF' :=
              Option.some.inj ((List.getElem?_eq_getElem hi2_lt).symm.trans hb2)
            rw [hg1, hg2]; exact hn1.trans hn2.symm
          have hi_eq : i1 = i2 :=
            @Fin.mk.inj _ i1 _ i2 _
              (List.nodup_iff_injective_getElem.mp hblk_nd
                (a₁ := ⟨i1, by simp [hi1_lt]⟩) (a₂ := ⟨i2, by simp [hi2_lt]⟩) heq_name)
          subst hi_eq
          have he := Option.some.inj (hb1.symm.trans hb2)
          injection he with _ hnp _
    subst hnP_eq
    -- Unfold `majorShape` and `Expr.recRulePlain`
    unfold majorShape at hmaj'
    rw [ite_eq_left_iff.mpr fun hn => absurd (by omega) hn] at hmaj'
    cases hsm : D.tyA.stripPis mI with
    | none => simp [hsm] at hmaj'
    | some q =>
      rw [hsm] at hmaj'
      rcases q with ⟨bs, rem⟩
      cases rem with
      | forallE dom body bm =>
        dsimp only at hmaj'
        cases hfn : dom.getAppFn with
        | const T ls =>
          rw [hfn] at hmaj'
          dsimp only at hmaj'
          split at hmaj'
          · next hcond =>
            unfold Expr.recRulePlain at hplain
            rw [hsm] at hplain
            dsimp only at hplain
            rw [hfn] at hplain
            simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hplain
            obtain ⟨⟨_, _⟩, hlvls_eq, htake_eq⟩ := hplain
            refine ⟨dom, T, piDomAt_eq_of_stripPis mI hsm, ?_, htake_eq, hcond.2.2⟩
            rw [hfn, hlvls_eq]
          · simp at hmaj'
        | _ => simp [hfn] at hmaj'
      | _ => simp at hmaj'

private theorem liftLooseBVars_lowerBVars_of_noLooseIn (k : Nat) :
    ∀ (c : Nat) (e : KExpr), Decl.noLooseIn c k e = true →
      (e.lowerBVars k c).liftLooseBVars k c = e
  | c, .bvar i, hno => by
    simp only [Decl.noLooseIn, decide_eq_true_eq] at hno
    simp only [Expr.lowerBVars]
    split
    · next hge =>
      simp only [Expr.liftLooseBVars]
      split
      · congr 1; omega
      · omega
    · next hlt =>
      simp only [Expr.liftLooseBVars]
      split
      · omega
      · rfl
  | _, .fvar _ _, _ | _, .sort _, _ | _, .const _ _, _ | _, .lit _, _ => rfl
  | c, .app f a, hno => by
    simp only [Decl.noLooseIn, Bool.and_eq_true] at hno
    simp [Expr.lowerBVars, Expr.liftLooseBVars,
      liftLooseBVars_lowerBVars_of_noLooseIn k c f hno.1,
      liftLooseBVars_lowerBVars_of_noLooseIn k c a hno.2]
  | c, .lam t b _, hno | c, .forallE t b _, hno => by
    simp only [Decl.noLooseIn, Bool.and_eq_true] at hno
    simp [Expr.lowerBVars, Expr.liftLooseBVars,
      liftLooseBVars_lowerBVars_of_noLooseIn k c t hno.1,
      liftLooseBVars_lowerBVars_of_noLooseIn k (c + 1) b hno.2]
  | c, .letE t v b _, hno => by
    simp only [Decl.noLooseIn, Bool.and_eq_true] at hno
    simp [Expr.lowerBVars, Expr.liftLooseBVars,
      liftLooseBVars_lowerBVars_of_noLooseIn k c t hno.1.1,
      liftLooseBVars_lowerBVars_of_noLooseIn k c v hno.1.2,
      liftLooseBVars_lowerBVars_of_noLooseIn k (c + 1) b hno.2]
  | c, .proj _ _ e, hno => by
    simp [Expr.lowerBVars, Expr.liftLooseBVars, liftLooseBVars_lowerBVars_of_noLooseIn k c e hno]

private theorem looseBVarsBounded_lowerBVars_of_noLooseIn (rP nI : Nat) :
    ∀ (c : Nat) (e : KExpr),
      e.looseBVarsBounded (rP + nI + c) = true → Decl.noLooseIn c nI e = true →
      (e.lowerBVars nI c).looseBVarsBounded (rP + c) = true
  | c, .bvar i, hlbb, hno => by
    simp only [Expr.looseBVarsBounded, decide_eq_true_eq] at hlbb
    simp only [Decl.noLooseIn, decide_eq_true_eq] at hno
    simp only [Expr.lowerBVars]
    split
    · simp only [Expr.looseBVarsBounded, decide_eq_true_eq]; omega
    · simp only [Expr.looseBVarsBounded, decide_eq_true_eq]; omega
  | _, .fvar _ _, _, _ | _, .sort _, _, _ | _, .const _ _, _, _ | _, .lit _, _, _ => rfl
  | c, .app f a, hlbb, hno => by
    simp only [Expr.looseBVarsBounded, Decl.noLooseIn, Bool.and_eq_true] at hlbb hno
    simp [Expr.lowerBVars, Expr.looseBVarsBounded,
      looseBVarsBounded_lowerBVars_of_noLooseIn rP nI c f hlbb.1 hno.1,
      looseBVarsBounded_lowerBVars_of_noLooseIn rP nI c a hlbb.2 hno.2]
  | c, .lam t b _, hlbb, hno | c, .forallE t b _, hlbb, hno => by
    simp only [Expr.looseBVarsBounded, Decl.noLooseIn, Bool.and_eq_true] at hlbb hno
    have hb := looseBVarsBounded_lowerBVars_of_noLooseIn rP nI (c + 1) b
      (by rw [show rP + nI + (c + 1) = rP + nI + c + 1 by omega]; exact hlbb.2) hno.2
    rw [show rP + (c + 1) = rP + c + 1 by omega] at hb
    simp [Expr.lowerBVars, Expr.looseBVarsBounded,
      looseBVarsBounded_lowerBVars_of_noLooseIn rP nI c t hlbb.1 hno.1, hb]
  | c, .letE t v b _, hlbb, hno => by
    simp only [Expr.looseBVarsBounded, Decl.noLooseIn, Bool.and_eq_true] at hlbb hno
    have hb := looseBVarsBounded_lowerBVars_of_noLooseIn rP nI (c + 1) b
      (by rw [show rP + nI + (c + 1) = rP + nI + c + 1 by omega]; exact hlbb.2) hno.2
    rw [show rP + (c + 1) = rP + c + 1 by omega] at hb
    simp [Expr.lowerBVars, Expr.looseBVarsBounded,
      looseBVarsBounded_lowerBVars_of_noLooseIn rP nI c t hlbb.1.1 hno.1.1,
      looseBVarsBounded_lowerBVars_of_noLooseIn rP nI c v hlbb.1.2 hno.1.2, hb]
  | c, .proj _ _ e, hlbb, hno =>
    looseBVarsBounded_lowerBVars_of_noLooseIn rP nI c e hlbb hno

private theorem allLevelParamsDefined_stripPis {ps : List LevelParam} :
    ∀ (m : Nat) {e : KExpr} {bs : List (KExpr × Ix.Kernel.BinderMeta)} {rem : KExpr},
      e.allLevelParamsDefined ps = true → e.stripPis m = some (bs, rem) →
      rem.allLevelParamsDefined ps = true
  | 0, _, _, _, hd, hs => by injection hs with hp; injection hp with _ h; subst h; exact hd
  | m + 1, .forallE T B _, _, _, hd, hs => by
    simp only [Expr.allLevelParamsDefined, Bool.and_eq_true] at hd
    simp only [Expr.stripPis] at hs
    cases hsb : B.stripPis m with
    | none => simp [hsb] at hs
    | some p =>
      rw [hsb] at hs; injection hs with hp; injection hp with _ h; subst h
      exact allLevelParamsDefined_stripPis m hd.1.2 hsb
  | _ + 1, .bvar _, _, _, _, hs | _ + 1, .fvar _ _, _, _, _, hs | _ + 1, .sort _, _, _, _, hs
  | _ + 1, .const _ _, _, _, _, hs | _ + 1, .app _ _, _, _, _, hs | _ + 1, .lam _ _ _, _, _, _, hs
  | _ + 1, .letE _ _ _ _, _, _, _, hs | _ + 1, .lit _, _, _, _, hs | _ + 1, .proj _ _ _, _, _, _, hs =>
    nomatch hs

private theorem allLevelParamsDefined_getAppFn {ps : List LevelParam} :
    ∀ (e : KExpr), e.allLevelParamsDefined ps = true → e.getAppFn.allLevelParamsDefined ps = true
  | .app f _, hd => by
    simp only [Expr.allLevelParamsDefined, Bool.and_eq_true] at hd
    exact allLevelParamsDefined_getAppFn f hd.1
  | .bvar _, hd | .fvar _ _, hd | .sort _, hd | .const _ _, hd | .lam _ _ _, hd
  | .forallE _ _ _, hd | .letE _ _ _ _, hd | .lit _, hd | .proj _ _ _, hd => hd

private theorem allLevelParamsDefined_getAppArgs {ps : List LevelParam} :
    ∀ (e : KExpr), e.allLevelParamsDefined ps = true →
      ∀ a ∈ e.getAppArgs, a.allLevelParamsDefined ps = true
  | .app f x, hd, a, ha => by
    simp only [Expr.allLevelParamsDefined, Bool.and_eq_true] at hd
    simp only [Expr.getAppArgs, List.mem_append, List.mem_singleton] at ha
    rcases ha with ha | rfl
    · exact allLevelParamsDefined_getAppArgs f hd.1 a ha
    · exact hd.2
  | .bvar _, _, _, ha | .fvar _ _, _, _, ha | .sort _, _, _, ha | .const _ _, _, _, ha
  | .lam _ _ _, _, _, ha | .forallE _ _ _, _, _, ha | .letE _ _ _ _, _, _, ha | .lit _, _, _, ha
  | .proj _ _ _, _, _, ha => nomatch ha

private theorem allLevelParamsDefined_lowerBVars (ps : List LevelParam) (s : Nat) :
    ∀ (c : Nat) (e : KExpr),
      (e.lowerBVars s c).allLevelParamsDefined ps = e.allLevelParamsDefined ps
  | c, .bvar i => by simp only [Expr.lowerBVars]; split <;> rfl
  | _, .fvar _ _ | _, .sort _ | _, .const _ _ | _, .lit _ => rfl
  | c, .app f a => by
    simp [Expr.lowerBVars, Expr.allLevelParamsDefined,
      allLevelParamsDefined_lowerBVars ps s c f, allLevelParamsDefined_lowerBVars ps s c a]
  | c, .lam t b _ | c, .forallE t b _ => by
    simp [Expr.lowerBVars, Expr.allLevelParamsDefined,
      allLevelParamsDefined_lowerBVars ps s c t, allLevelParamsDefined_lowerBVars ps s (c + 1) b]
  | c, .letE t v b _ => by
    simp [Expr.lowerBVars, Expr.allLevelParamsDefined,
      allLevelParamsDefined_lowerBVars ps s c t, allLevelParamsDefined_lowerBVars ps s c v,
      allLevelParamsDefined_lowerBVars ps s (c + 1) b]
  | c, .proj _ _ e => allLevelParamsDefined_lowerBVars ps s c e

private theorem looseBVarsBounded_stripPis :
    ∀ (m d : Nat) {e : KExpr} {bs : List (KExpr × Ix.Kernel.BinderMeta)} {rem : KExpr},
      e.looseBVarsBounded d = true → e.stripPis m = some (bs, rem) →
      rem.looseBVarsBounded (d + m) = true
  | 0, d, _, _, _, hl, hs => by injection hs with hp; injection hp with _ h; subst h; simpa using hl
  | m + 1, d, .forallE T B _, _, _, hl, hs => by
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hl
    simp only [Expr.stripPis] at hs
    cases hsb : B.stripPis m with
    | none => simp [hsb] at hs
    | some p =>
      rw [hsb] at hs; injection hs with hp; injection hp with _ h; subst h
      rw [show d + (m + 1) = (d + 1) + m by omega]
      exact looseBVarsBounded_stripPis m (d + 1) hl.2 hsb
  | _ + 1, _, .bvar _, _, _, _, hs | _ + 1, _, .fvar _ _, _, _, _, hs | _ + 1, _, .sort _, _, _, _, hs
  | _ + 1, _, .const _ _, _, _, _, hs | _ + 1, _, .app _ _, _, _, _, hs | _ + 1, _, .lam _ _ _, _, _, _, hs
  | _ + 1, _, .letE _ _ _ _, _, _, _, hs | _ + 1, _, .lit _, _, _, _, hs | _ + 1, _, .proj _ _ _, _, _, _, hs =>
    nomatch hs

private theorem looseBVarsBounded_getAppArgs (d : Nat) :
    ∀ (e : KExpr), e.looseBVarsBounded d = true → ∀ a ∈ e.getAppArgs, a.looseBVarsBounded d = true
  | .app f x, hl, a, ha => by
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hl
    simp only [Expr.getAppArgs, List.mem_append, List.mem_singleton] at ha
    rcases ha with ha | rfl
    · exact looseBVarsBounded_getAppArgs d f hl.1 a ha
    · exact hl.2
  | .bvar _, _, _, ha | .fvar _ _, _, _, ha | .sort _, _, _, ha | .const _ _, _, _, ha
  | .lam _ _ _, _, _, ha | .forallE _ _ _, _, _, ha | .letE _ _ _ _, _, _, ha | .lit _, _, _, ha
  | .proj _ _ _, _, _, ha => nomatch ha

private theorem rules_length_eq
    {refs recurAddrs : List _root_.Address} {univs : List Ixon.Univ} {sharing : List Ixon.Expr}
    {blobs : List (_root_.Address × ByteArray)} {tree : L1.BinderTreeData}
    {j : Nat} {root : F} {rus : List Ixon.RecursorRule} {p r : SourceValue F}
    {h h' : Heap F} {cs : List (Call F)}
    (hr : L1.RulesTraceRep refs recurAddrs univs sharing blobs tree h j root rus p)
    (ev : ObsFn Obs.W Obs.Names.«Lists::length<KernelTypes::KRecRule>» [p] h r h' cs) :
    r = .field (rus.length : F) ∧ h' = h := by
  have htoRep : ∀ {j' : Nat} {root' : F} {l : List Ixon.RecursorRule} {q : SourceValue F},
      L1.RulesTraceRep refs recurAddrs univs sharing blobs tree h j' root' l q →
      RepList krrListEnum (fun _ _ _ => True) h l q := by
    intro j' root' l q htr
    induction htr with
    | nil c => exact .nil c
    | cons c _ _ _ _ _ ih' => exact .cons c trivial ih'
  have ev' : ObsFn Obs.W (Instance.mk "Lists::length" [(.named "KernelTypes::KRecRule" [])]).symbol
      [p] h r h' cs := by rw [Obs.Names.«Lists::length<KernelTypes::KRecRule>».symbol]; exact ev
  have hrep : RepList (Instance.mk "Lists::Node" [(.named "KernelTypes::KRecRule" [])]).symbol
      (fun _ _ _ => True) h rus p := by
    rw [Obs.Names.«Lists::Node<KernelTypes::KRecRule>».symbol]; exact htoRep hr
  exact Lib.Lists.length_spec ev' hrep

/-- **One iteration of `KernelModeled::check_recs`** paired with its `MemberValItem` from
`evRecsVal` produces `RecMemberData` for recursor `k`. -/
theorem recMember_of_cons
    {calls : List (Call F)} {bAddr : _root_.Address} {t : Ix.Kernel.RoleTable}
    {E₀ : Ixon.Env} {lim : Option Nat} {csFam : List (Call F)}
    {B rb : _root_.Address} {cb crb : Ixon.Constant} {ms rs : Array Ixon.MutConst}
    (ht : t.check = .ok ()) (hbd : Bounded calls)
    (hS : LoadedReads.RunStore calls E₀) (hH : LoadedReads.HashedRecordsStored calls E₀)
    (hB : FamBlockRecord E₀ B cb ms) (hR : FamRecRecord E₀ rb crb rs)
    {advAs typeAs ctorAs recAs dstAs : List Bytes.Address}
    (htypes : typeAs.map ixAddr =
      ms.toList.mapIdx fun i m => projAddr (Specs.Callees.memberProjInfo B i m))
    (hctors : ctorAs.map ixAddr = ctorAddrsFrom B ms.toList 0)
    (hrecs : recAs.map ixAddr =
      rs.toList.mapIdx fun i m => projAddr (Specs.Callees.memberProjInfo rb i m))
    (hlenSD : (typeAs ++ ctorAs ++ recAs).length = dstAs.length)
    {nonrecsBlk : List (ConstantInfo .anon)} {nonrecsTys : List KExpr}
    (hlenNR : nonrecsBlk.length = nonrecsTys.length)
    (hctorLookup : CtorLookupFn.{u} calls bAddr t E₀ lim csFam B rb cb crb ms advAs
      (typeAs ++ ctorAs ++ recAs) dstAs nonrecsBlk nonrecsTys)
    (hrecRefs : ∀ x, UsedRef E₀ rb x → Claim.CoveredAt t lim x ∨ NeedOk E₀ x)
    {a0 : Bytes.Address} {restTypeAs : List Bytes.Address} {ind0 : Ixon.Inductive}
    (htypeAs_cons : typeAs = a0 :: restTypeAs) (ha0_eq : ixAddr a0 = iprjAddr B 0)
    (hms0 : ms[0]? = some (.indc ind0)) (hind0_lvls_lt : ind0.lvls.toNat < 4294967296)
    {rcV tys recs models src dst aset s n kV np uo bnl fam form r : SourceValue F}
    {h h' : Heap F} {cs_rec : List (Call F)}
    (hsub : CallSub cs_rec calls)
    (C : CheckRecsCons rcV tys recs models src dst aset s n kV np uo bnl fam form r h h' cs_rec)
    {k : Nat} {rc : Ixon.Recursor} {aRec aMd : Bytes.Address}
    (hk_u64 : k < UInt64.size) (hrk : rs[k]? = some (.recr rc))
    (hk_eq : kV = .field (k : F)) (hbnl_eq : bnl = .field (ind0.lvls.toNat : F))
    (huo : uo = .field 0 ∨ uo = .field 1)
    (haRec_eq : ixAddr aRec = rprjAddr rb k)
    (hg_eq : aliasMap (((typeAs ++ ctorAs ++ recAs).map fun b => Core.keyOf t (ixAddr b)).zip
      (dstAs.map fun b => Core.keyOf t (ixAddr b))) (Core.keyOf t (rprjAddr rb k)) =
      Core.keyOf t (ixAddr aMd))
    (haMd_in_dst : aMd ∈ dstAs)
    (hrc : RCRep t lim h rcV)
    (htys_rep : RepList addrListEnum (Bytes.RepAddressRef addrTy) h typeAs tys)
    (haRec_rep : Bytes.RepAddressRef addrTy h aRec C.x)
    (haMd_rep : Bytes.RepAddressRef addrTy h aMd C.rm)
    (hsrc_rep : RepList addrListEnum (Bytes.RepAddressRef addrTy) h (typeAs ++ ctorAs ++ recAs) src)
    (hdst_rep : RepList addrListEnum (Bytes.RepAddressRef addrTy) h dstAs dst)
    (haset_rep : AddrMapAll addrMapEnum (fun _ k _ => AdvChecked calls bAddr t lim csFam advAs k) h aset)
    {bytes : List UInt8} (hstr_s : L1.Stream h bytes s)
    (hvalItem : MemberValItem calls bAddr t E₀ lim csFam advAs
      (typeAs ++ ctorAs ++ recAs) dstAs recAs aRec aMd) :
    Nonempty (RecMemberData.{u} calls bAddr t E₀ lim csFam B rb cb crb ms rs advAs
      (typeAs ++ ctorAs ++ recAs) dstAs recAs nonrecsBlk nonrecsTys k rc aRec aMd) ∧
    ∃ remBytes, L1.Stream C.m892 remBytes C.s' := by
  have htwf : t.wf = true := by unfold Ix.Kernel.RoleTable.wf; rw [ht]; rfl
  have hmod : Aiur.Library.U32.Goldilocks.modulus = 18446744069414584321 := rfl
  let srcAs := typeAs ++ ctorAs ++ recAs
  -- 1. Unpack `C.evGetRec` (`Ingress::get_ci [C.x]`)
  have hsub_getRec : CallSub C.evGetRec.cs calls := fun cl hcl => hsub cl (C.evGetRec.sub cl hcl)
  obtain ⟨_, cRec, hhRec, hbaRec, hexRec, -, htrRec⟩ :=
    L1.get_ci_block_trace_spec (bounded_sub hsub_getRec hbd) haRec_rep C.evGetRec.obs
  have hrecAtRec : Ix.Cert.recordAt E₀ (ixAddr aRec) = some (memberProjection rb k (.recr rc)) := by
    rw [← hS.recordOf_eq_recordAt, haRec_eq, ← LoadedReads.memberAddr_recr]
    exact hR.members k (.recr rc) hrk
  have hcRec_eq : cRec = memberProjection rb k (.recr rc) :=
    hS.record_eq hrecAtRec (Core.hashed_mono hsub_getRec hhRec) hbaRec hexRec
  subst hcRec_eq
  unfold L1.GetCIBlockTraceResult at htrRec
  simp only [memberProjection] at htrRec
  obtain ⟨_, _, crb', rs', rc', blobs, tree, vRec, hhBlk, hbaBlk, hexBlk, hmuts', hrk', hhp,
      built, hldv, hrepRec⟩ := htrRec
  have hcrb_eq : crb' = crb :=
    hS.record_eq ((hS.recordOf_eq_recordAt rb).symm.trans hR.record)
      (Core.hashed_mono hsub_getRec hhBlk) hbaBlk hexBlk
  subst crb'
  have hrs_eq : rs' = rs := Ixon.ConstantInfo.muts.inj (hmuts'.symm.trans hR.muts)
  subst rs'
  have hk_toNat : k.toUInt64.toNat = k := toNat_toUInt64_lt_r hk_u64
  rw [hk_toNat, Array.getElem?_toList, hrk] at hrk'
  have hrc_eq : rc' = rc := Ixon.MutConst.recr.inj (Option.some.inj hrk').symm
  subst rc'
  rw [hk_toNat] at hrepRec
  obtain ⟨hlvls_lt, hnp_lt, hni_lt, hnmot_lt, hnmin_lt, hk_lt, tyPtr, rulesPtr, blkPtr, bBlk,
      planT, hbBlk_eq, hbBlk_ref, hvRec_eq, rty, hpT, hlT, hrlsTrace⟩ := hrepRec
  have hvRec_ld := Except.ok.inj (C.ldRec.symm.trans hldv)
  rw [hvRec_eq] at hvRec_ld
  injection hvRec_ld with _ _ hargs_r
  injection hargs_r with hnl_eq hargs_r
  injection hargs_r with hty_eq hargs_r
  injection hargs_r with hnp_eq hargs_r
  injection hargs_r with hni_eq hargs_r
  injection hargs_r with hn_eq hargs_r
  injection hargs_r with hnmin_eq hargs_r
  injection hargs_r with hrules_eq hargs_r
  injection hargs_r with hkf_eq _
  subst hty_eq hrules_eq
  have hnotK : rc.k = false := by
    cases hk_b : rc.k with
    | false => rfl
    | true => rw [hk_b] at hkf_eq; simp [L1.repBoolField] at hkf_eq
  have hblob : ∀ x bs, (x, bs) ∈ blobs → E₀.blobs.get? x = some bs := by
    intro x bs hm
    obtain ⟨hhx, hxa⟩ := hhp (x, bs) hm
    have hrun := hS.blobs bs (Core.hashed_mono hsub_getRec hhx)
    rwa [hxa] at hrun
  have hagree : L1.BlobReadAgreement (readCtx t (fun x => E₀.blobs.get? x)).blob blobs :=
    L1.BlobReadAgreement.of_mem hblob
  let rP := rc.params.toNat + rc.motives.toNat + rc.minors.toNat
  let mI := rP + rc.indices.toNat
  have hrp_eq : C.rp = .field (rP : F) := by
    have hop1 : evalBinOp .add (.field (rc.params.toNat : F)) (.field (rc.motives.toNat : F)) =
        .ok C.xNpN := by
      rw [← hnp_eq, ← hn_eq]; exact C.opNpN
    have hx := SubstAux.add_ok hop1
    have hop2 : evalBinOp .add (.field ((rc.params.toNat : F) + (rc.motives.toNat : F)))
        (.field (rc.minors.toNat : F)) = .ok C.rp := by
      rw [← hx, ← hnmin_eq]; exact C.opRp
    rw [SubstAux.add_ok hop2]; simp only [rP, Nat.cast_add]
  -- 2. Read `rc.typ` under `id` (`tyP`), scope via `C.evScope`, `familyKey` via `C.evCarriers`,
  --    `majorKey` via `C.evParent`.
  have hself0 : ∀ i x, ([] : List _root_.Address)[i]? = some x →
      ∃ m k, blockSelf t rb rs i = some m ∧ m = .ok k := fun _ _ hx => by simp at hx
  obtain ⟨tyP, hreadP⟩ := LoadedReads.exprReader_read_ok ht rty hself0 hblob
  have hcall_scope : (⟨"KernelCheck::validate_expr_well_scoped",
      [C.ty, .field 0, .field (rc.lvls.toNat : F)], C.m473⟩ : Call F) ∈ calls := by
    rw [← hnl_eq]; exact hsub _ C.evScope.mem
  have evScope' : ObsFn Obs.W "KernelCheck::validate_expr_well_scoped"
      [C.ty, .field 0, .field (rc.lvls.toNat : F)] C.m473 C.vScope C.m511 C.evScope.cs := by
    rw [← hnl_eq]; exact C.evScope.obs
  obtain ⟨_, htyP_lbb, htyP_def⟩ :=
    Assembly.validate_expr_well_scoped_spec hbd hlvls_lt rty
      (C.ext391.trans C.evCarriers.extends) hreadP evScope' hcall_scope
  have hrdP : (Ix.Kernel.Reader.MemberReader.mk' (readCtx t (fun x => E₀.blobs.get? x)) crb
      (Ix.Kernel.Reader.recParam (List.range rc.lvls.toNat)) (blockSelf t rb rs)).read rc.typ =
      .ok tyP := by
    rw [Assembly.recParam_range]; exact hreadP
  obtain ⟨R', _, -, hrawP, -, htraceP⟩ := rty.toRawTmCExactTrace (κ := Core.keyOf t)
    (ps := List.range rc.lvls.toNat) (by simp) (by simpa using hlvls_lt)
    (LoadedReads.readCtx_keyAt_inv ht _) (fun _ _ _ _ hx => by simp at hx) hblob hrdP htyP_lbb htyP_def
  have hshapeP : RawShape tyP R' := rawShape_of_rawTrace tyP (htraceP planT hlT [])
  have hraw0 := hrawP 0 zeroGhost
  simp only [Decl.posOf_range] at hraw0
  have hrawTm := hraw0.toRawTm
  have evCarriers' : ObsFn Obs.W "KernelModeled::check_carriers"
      [C.ty, .field (rc.params.toNat : F), tys] C.m391 C.vCarriers C.m473 C.evCarriers.cs := by
    rw [← hnp_eq]; exact C.evCarriers.obs
  have htys_391 : RepList addrListEnum (Bytes.RepAddressRef addrTy) C.m391 (a0 :: restTypeAs) tys := by
    rw [← htypeAs_cons]
    exact RepLinkedList.mono (Bytes.repAddressRef_heapMono₂ addrTy)
      (C.evGetRec.extends.trans C.ext391) htys_rep
  have hfamKey : familyKey rc tyP = some (Core.keyOf t (iprjAddr B 0)) :=
    check_carriers_familyKey hnp_lt hshapeP (hrawTm.mono C.ext391) htys_391 ha0_eq evCarriers'
  have ext_67_669 : Heap.Extends C.m67 C.m669 := by
    have e1 : Heap.Extends C.m561 C.mNil1 := by rw [C.hNil1]; exact Heap.Extends.snoc _ _
    have e2 : Heap.Extends C.mRen C.mNil2 := by rw [C.hNil2]; exact Heap.Extends.snoc _ _
    have e3 : Heap.Extends C.mLP C.mNilSort := by rw [C.hNilSort]; exact Heap.Extends.snoc _ _
    exact C.ext391.trans (C.evCarriers.extends.trans (C.evScope.extends.trans (C.evNoMent.extends.trans
      (e1.trans (C.evPeel1.extends.trans (C.evRen.extends.trans (e2.trans (C.evPeel2.extends.trans
        (C.evParamEq.extends.trans (C.evPins.extends.trans (C.evLowerPins.extends.trans
          (e3.trans (C.evSort.extends.trans C.ext669)))))))))))))
  have ext_67_838 : Heap.Extends C.m67 C.m838 :=
    ext_67_669.trans (C.evParent.extends.trans (C.evGetParent.extends.trans
      (C.evCanon.extends.trans C.evHeaderLets.extends)))
  have evPar' : ObsFn Obs.W "KernelCheck::rec_to_parent_addr"
      [C.ty, .field (rc.params.toNat : F), .field (rc.motives.toNat : F),
        .field (rc.minors.toNat : F), .field (rc.indices.toNat : F)]
      C.m669 C.parAddr C.m698 C.evParent.cs := by
    rw [← hnp_eq, ← hn_eq, ← hnmin_eq, ← hni_eq]; exact C.evParent.obs
  obtain ⟨aPar, haPar_ref, hmajKey⟩ :=
    rec_to_parent_addr_rawTm_full hnp_lt hnmot_lt hnmin_lt hni_lt hshapeP
      (hrawTm.mono ext_67_669) evPar'
  -- 3. Unpack `C.evRules` (`Obs.«KernelModeled::check_rules».obs`) first to identify the major
  --    inductive `aIndM`, prove `ixAddr aPar = ixAddr aIndM`, and deduce `C.parCi` is `Induct`!
  have hsub_rules : CallSub C.evRules.cs calls := fun cl hcl => hsub cl (C.evRules.sub cl hcl)
  match Obs.«KernelModeled::check_rules».obs C.evRules.obs with
  | .run (m2 := mRmp) (cs12 := csRmp) (x_iaddr := x_iaddr) (x_ilvls := x_ilvls)
      (x_pins := x_pins) (m58 := mInd) (p66 := pInd) (cs72 := csInd)
      (w89 := w89) (w90 := w90) (x_inp := x_inp) (w91 := w91) (x_inct := x_inct) (w92 := w92)
      (x_iblock := x_iblock) (x_iidx := x_iidx)
      (v144 := v144) (m147 := mLen) (cs155 := csLen) (cs177 := csGo)
      (ev14 := evRmp) (ev74 := evGetInd) (ld68 := ldInd) (ev157 := evRlen)
      (heq173 := heqInct) (ev179 := evGo) (hc315 := hcRules) .. =>
    have hsub_rmp : CallSub csRmp calls := fun cl hcl => hsub_rules cl (by rw [hcRules]; simp [hcl])
    have hsub_ind : CallSub csInd calls := fun cl hcl => hsub_rules cl (by rw [hcRules]; simp [hcl])
    have hsub_go : CallSub csGo calls := fun cl hcl => hsub_rules cl (by rw [hcRules]; simp [hcl])
    -- Check `rc.indices.toNat < 4294967296` from `evRmp` (`rec_major_pins` has `ev157` loading `Induct`
    -- with `ni = indM.indices.toNat`, or wait: `rec_major_pins` only needs `hni_lt : rc.indices.toNat < 4294967296`?
    -- Actually `rc.indices.toNat < 72057594037927936`, wait: `Decl.rec_major_pins_spec` asks `< 4294967296`!
    -- Wait: let's check `rc.indices.toNat < 4294967296` from `rty` or `indM.indices.toNat`?
    -- No! `C.ty` represents `tyP`, whose `stripPis` depth `rP + rc.indices.toNat` is bounded by `tyP`'s size,
    -- which is `< 2^39`? Even better: `evRmp`'s `ev14` is `peel_n_foralls [C.ty, rP + nI]`, wait:
    -- `C.evGetParent` loaded `aPar` as `Induct` and `C.ldParent` gives `parCi`! Wait: let's check
    -- `evRmp` directly for `x_iaddr`, `aIndM`, and `rc.indices.toNat < 4294967296`!)
    -- Actually, look at `rty`: `rc.indices.toNat` is bounded by `C.ty`'s height, which is `< C.m67.length < 2^39`?
    -- Even better: `rc.indices.toNat ≤ tyP`'s AST size? Let's get `rc.indices.toNat < 4294967296` cleanly
    -- from `rc.indices.toNat` via `evGetInd` (`hrawInd`)? Wait: `rec_major_pins` ALSO has `ev309` (`assert_index_vars`)
    -- and `ev14` (`peel_n_foralls`). Let's check: does `C.evGetParent` load `Induct`?
    -- Look! `Obs.«KernelCheck::check_recursor_canonical_at».obs` on `C.evCanon` checks `C.parCi`!
    -- Wait: in `Obs.«KernelModeled::rec_major_pins».obs evRmp`, `ev14` peels `rP + nI` foralls and `ld51` loads
    -- `Forall [x_dom, ...]`, `ev89` collects spine `(x_h, x_args)`, `ld122` loads `Const [x_iaddr, x_ilvls]`,
    -- `ev157` calls `get_ci [x_iaddr]` returning `Induct [..., x_inp, x_ini, ...]`, `heq245 : x_ini = C.ni`!
    -- Wait: `peel_n_foralls_rawTm_val` ALREADY works for ANY `< 18446744069414584321` (not just `< 4294967296`)!
    -- Let's extract `aIndM` and `rc.indices.toNat < 4294967296` cleanly from `evRmp` + `evGetInd`!
    have hrmp_ind : ∃ (aIndM : Bytes.Address),
        Bytes.RepAddressRef addrTy mRmp aIndM x_iaddr ∧
        majorKey rc tyP = some (Core.keyOf t (ixAddr aIndM)) := by
      match Obs.«KernelModeled::rec_major_pins».obs evRmp with
      | .run (v16 := v16) (x_dom := xdom) (m77 := m77) (x_h := xh) (x_args := xargs)
          (op37 := opMi) (ev14 := evP) (ld51 := ldFa) (ev89 := evSp) (ld122 := ldC)
          (ev157 := evCi1) (ev270 := evL1) (ev324 := evD1) (ev309 := evA1)
          (he359 := hrR) (ev399 := evT1) (ev385 := evLo1) (he423 := hhR) .. =>
        subst hhR
        injection hrR with hl; injection hl with hi1 _; subst hi1
        rw [hrp_eq, hni_eq] at opMi
        have hv16 : v16 = .field ((mI : Nat) : F) := by
          rw [SubstAux.add_ok opMi]; simp only [mI, Nat.cast_add]
        rw [hv16] at evP
        have hmi_val : ZMod.val (mI : F) = mI := SubstAux.val_natCast (by omega)
        obtain ⟨hhP, _, _, _, hstripP, hbodyP⟩ :=
          Typing.peel_n_foralls_rawTm_val mI hmi_val (hrawTm.mono ext_67_838) evP
        subst hhP
        obtain ⟨Rt, _, _, _, _, _, rfl, -, hRt, -, -⟩ := hbodyP.forallE_of_load ldFa
        obtain ⟨_, _, Rh, _, _, _, htupSp, hRh, -, -, hRt_eq, -, -⟩ :=
          Decl.collect_spine_rawTm_spec hRt evSp
        injection htupSp with h1; injection h1 with hhd _; subst hhd
        have hconst : ∃ a us, Rh = .const (Core.keyOf t (ixAddr a)) us ∧
            Bytes.RepAddressRef addrTy m77 a x_iaddr := by
          cases hRh with
          | const cell ra _ _ =>
            obtain ⟨-, hxs⟩ := load_cell cell ldC; injection hxs with hcx _; subst hcx
            exact ⟨_, _, rfl, ra⟩
          | bvarLocal cell _ _ | bvarFree cell _ _ _ | sort cell _ _ | app cell _ _ | lam cell _ _ _
          | forallE cell _ _ _ | letE cell _ _ _ | litNat cell _ _ | litStr cell _ _
          | proj cell _ _ => exact (load_cell_ne cell ldC (by decide)).elim
        obtain ⟨aIndM, us, rfl, haIndM⟩ := hconst
        have ext_77_rmp := evCi1.heap_extends.trans (evL1.heap_extends.trans
          (evD1.heap_extends.trans (evA1.heap_extends.trans
            (evT1.heap_extends.trans evLo1.heap_extends))))
        refine ⟨aIndM, Bytes.repAddressRef_heapMono₂ addrTy ext_77_rmp haIndM, ?_⟩
        have hmajR : majorKey rc R' = some (Core.keyOf t (ixAddr aIndM)) := by
          unfold majorKey binderDom headKey
          rw [hstripP]; simp only [Option.bind_some]; rw [hRt_eq, Decl.getAppFn_mkAppN]; rfl
        exact (Typing.majorKey_eq_of_rawShape (rc := rc) hshapeP).trans hmajR
    obtain ⟨aIndM, haIndM_rmp, hmajKey_ind⟩ := hrmp_ind
    -- `get_ci_induct_record` on `evGetInd` gives `cmM, ipM, cbM, msM, indM, bBlkM`!
    obtain ⟨cmM, ipM, cbM, msM, indM, bBlkM, hrecM, hinfoM, hcmM_can, haIndM_can,
        hrecBM, hmutsM, hmsM, hip_lt, hindM_np_lt, hindM_ni_lt, hindM_nc_lt,
        hx_inp_eq, hx_ini_eq, hx_inct_eq, hbBlkM_ref, hbBlkM_eq, hx_iidx_eq⟩ :=
      get_ci_induct_record hbd hS hH hsub_ind haIndM_rmp evGetInd ldInd
    -- `ixAddr aPar = ixAddr aIndM`
    have haPar_eq_indM : ixAddr aPar = ixAddr aIndM := by
      have hk := Option.some.inj (hmajKey.symm.trans hmajKey_ind)
      exact Core.keyOf_inj htwf hk
    -- Identify `C.parCi` as `.construct kciEnum "Induct" [...]` from `C.evGetParent`
    have hpar_induct : ∃ p1 p2 p3 p4 p5 p6 p7 p8,
        C.parCi = .construct kciEnum "Induct" [p1, p2, p3, p4, p5, p6, p7, p8] := by
      have hsub_par : CallSub C.evGetParent.cs calls :=
        fun cl hcl => hsub cl (C.evGetParent.sub cl hcl)
      obtain ⟨-, _, cPar, _, hhPar, hbaPar, hexPar, -, -, -, hrawPar⟩ :=
        L1.get_ci_spec (bounded_sub hsub_par hbd) haPar_ref C.evGetParent.obs
      have hrecAtPar : Ix.Cert.recordAt E₀ (ixAddr aPar) = some cmM := by
        rw [haPar_eq_indM, ← hS.recordOf_eq_recordAt]; exact hrecM
      have hcPar_eq : cPar = cmM :=
        hS.record_eq hrecAtPar (Core.hashed_mono hsub_par hhPar) hbaPar hexPar
      subst hcPar_eq
      unfold L1.GetCIRawResult at hrawPar
      rw [hinfoM] at hrawPar
      obtain ⟨_, _, _, _, _, vPar, _, _, _, _, _, _, hldPar, hrawIndPar⟩ := hrawPar
      obtain ⟨_, _, _, _, _, _, _, _, _, _, hvPar_eq, _⟩ := hrawIndPar
      have hv_eq := Except.ok.inj (C.ldParent.symm.trans hldPar)
      rw [hvPar_eq] at hv_eq
      exact ⟨_, _, _, _, _, _, _, _, hv_eq⟩
    obtain ⟨p1, p2, p3, p4, p5, p6, p7, p8, hparCi_eq⟩ := hpar_induct
    -- 4. `C.evCanon` gives `rc.lvls.toNat = ind0.lvls.toNat ∨ rc.lvls.toNat = ind0.lvls.toNat + 1`!
    have hlvls_rel : rc.lvls.toNat = ind0.lvls.toNat ∨ rc.lvls.toNat = ind0.lvls.toNat + 1 := by
      have evCan' : ObsFn Obs.W "KernelCheck::check_recursor_canonical_at"
          [rcV, .construct "KernelTypes::KConstantInfo" "Rec"
            [.field (rc.lvls.toNat : F), C.ty, np, C.ni, n, C.nmin, C.rules, .field 0, .field 0, C.blk, C.idx],
            C.x, .construct kciEnum "Induct" [p1, p2, p3, p4, p5, p6, p7, p8],
            C.parAddr, uo, .field (ind0.lvls.toNat : F), form] C.mPar C.form' C.mCan C.evCanon.cs := by
        rw [← hnl_eq, ← hbnl_eq, ← hparCi_eq]; exact C.evCanon.obs
      exact check_recursor_canonical_lvls hlvls_lt hind0_lvls_lt huo evCan'
    -- Define `ps := LoadedReads.recPs rc ind0` and read `ty₀` under `recParam ps`!
    let ps : List LevelParam := LoadedReads.recPs rc ind0
    have hps_len : ps.length = rc.lvls.toNat := LoadedReads.recPs_length hlvls_rel
    have hperm : ps.Perm (List.range ps.length) := LoadedReads.recPs_perm hlvls_rel
    obtain ⟨ty₀, hread₀⟩ := LoadedReads.exprReader_read_ok ht
      (param := Ix.Kernel.Reader.recParam ps) rty hself0 hblob
    obtain ⟨hty₀_lbb, hty₀_def⟩ :=
      Typing.read_recParam_scoped hperm hread₀ hreadP htyP_lbb (by rwa [hps_len])
    -- Canonical annotation `tyA` of `ty₀` at root `mutsRootOffset rs.toList k`
    have hself_nil : ∀ i x m k', ([] : List _root_.Address)[i]? = some x →
        blockSelf t rb rs i = some m → m = .ok k' → k' = Core.keyOf t x := fun _ _ _ _ hx => by
      simp at hx
    obtain ⟨tyA, hcanon_ty, hann_ty, htm_tyA⟩ :=
      annotation_canon_gen_exact ht hperm (by rw [hps_len]; exact hlvls_lt)
        hself_nil hagree rty built hpT hlT hread₀ hty₀_lbb hty₀_def
    -- Bridge to `evRecsVal`'s `MemberValItem` via `CallMembers.recMemberVal_of_item`!
    obtain ⟨_, htyA_def, _, htyA_fv, hment, hmemStep⟩ :=
      recMemberVal_of_item ht hbd hS hR hlenSD hk_u64 hrk haRec_eq hg_eq hvalItem
        hperm hps_len hread₀ hty₀_lbb hty₀_def hcanon_ty
    -- 5. Count match: `rc.rules.size = indM.ctors.size`
    have ext_67_mInd : Heap.Extends C.m67 mInd :=
      ext_67_838.trans (evRmp.heap_extends.trans evGetInd.heap_extends)
    obtain ⟨hv144_eq, hmLen_eq⟩ := rules_length_eq
      (hrlsTrace.mono ext_67_mInd (fun _ hm => hm)) evRlen
    subst mLen
    have hrules_len_lt : rc.rules.size < 72057594037927936 := by
      have htoRep : ∀ {j' : Nat} {root' : F} {l : List Ixon.RecursorRule} {q : SourceValue F},
          L1.RulesTraceRep crb.refs.toList (L1.blockRecurAddrs rb rs.toList) crb.univs.toList
            crb.sharing.toList blobs tree C.m838 j' root' l q →
          RepList krrListEnum (fun _ _ _ => True) C.m838 l q := by
        intro j' root' l q htr
        induction htr with
        | nil c => exact .nil c
        | cons c _ _ _ _ _ ih' => exact .cons c trivial ih'
      have hrep_rls := htoRep (hrlsTrace.mono ext_67_838 (fun _ hm => hm))
      have hlt39 : rc.rules.toList.length < 2 ^ 39 :=
        RomBound.bounded_length_lt hbd (hsub _ C.evRules.mem) (by simp) hrep_rls
      rw [Array.length_toList] at hlt39
      omega
    have hcntRules : rc.rules.size = indM.ctors.size := by
      rw [Array.length_toList] at hv144_eq
      exact nat_eq_of_field_eq_u56_r hrules_len_lt hindM_nc_lt
        (Value.field.inj (hv144_eq.symm.trans (heqInct.trans hx_inct_eq)))
    -- 6. Run `Decl.rec_major_pins_spec_wide` on `evRmp` to get `pinsA` and `majorShape`!
    have hrp_val : ZMod.val (rP : F) = rP := SubstAux.val_natCast (by omega)
    have hni_val : ZMod.val (rc.indices.toNat : F) = rc.indices.toNat := SubstAux.val_natCast (by omega)
    have evRmp' : ObsFn Obs.W "KernelModeled::rec_major_pins"
        [C.ty, .field (rP : F), .field (rc.indices.toNat : F)] C.m838
        (.tuple [x_iaddr, x_ilvls, x_pins]) mRmp csRmp := by
      rw [← hrp_eq, ← hni_eq]; exact evRmp
    obtain ⟨_, _, _, aInd2, inpF, bsPos, domPos, bodyPos, mMajPos, lvlsPos, AsPos,
        htupRmp, haInd2, hilvls_rmp, hstripPos, hfnPos, hargsPos, _, hAsPos_f, hdropPos, hnoLoosePos,
        hpins_rmp, hAsPos_len⟩ :=
      Decl.rec_major_pins_spec_wide (bounded_sub hsub_rmp hbd)
        (by rw [hrp_val]; omega) (by rw [hni_val]; omega) evRmp' ((htm_tyA 0 zeroGhost).mono ext_67_838)
    injection htupRmp with hl; injection hl with h1 hl; injection hl with h2 hl; injection hl with h3 _
    subst h1 h2 h3
    have haInd2_eq : aInd2 = aIndM := addr_det haInd2 haIndM_rmp
    subst aInd2
    -- Match `ZMod.val inpF = indM.params.toNat` from `evRmp'`'s `get_ci [x_iaddr]` and `Lists::length`
    have hinp_eq : ZMod.val inpF = indM.params.toNat := by
      match Obs.«KernelModeled::rec_major_pins».obs evRmp' with
      | .run (x_iaddr := xi) (m77 := m77) (m141 := m141) (p149 := p149) (cs155 := cs155)
          (x_args := x_args) (x_inp := xinp) (v257 := v257) (v258 := v258)
          (m260 := m260) (cs268 := cs268)
          (op37 := opMi) (ev14 := eP) (ld51 := ldFa) (ev89 := eS) (ld122 := ldC)
          (ev157 := eCi) (ld151 := ldI) (heq245 := heqIni) (ev270 := eL)
          (op292 := opA) (heq295 := heqL) (he359 := hrE) (he423 := hhE) (hc424 := hcE) .. =>
        subst hhE
        injection hrE with hl; injection hl with hxi _; subst hxi
        rw [SubstAux.add_ok opMi] at eP
        have hmi_v : ZMod.val ((rP : F) + (rc.indices.toNat : F)) = rP + rc.indices.toNat := by
          rw [← Nat.cast_add]; exact SubstAux.val_natCast (by omega)
        obtain ⟨bs0, rem0, hstrip0, hrem0, rfl⟩ :=
          Decl.peel_n_foralls_exact (rP + rc.indices.toNat) hmi_v eP ((htm_tyA 0 zeroGhost).mono ext_67_838)
        rw [Nat.zero_add] at hrem0
        obtain ⟨dom0, body0, _, rfl, hdom0, _, _⟩ := hrem0.forallE_of_load ldFa
        obtain ⟨_, _, H0, As0, htup0, hH0, hAs0, hdom0_eq⟩ := Decl.collect_spine_exact eS hdom0
        injection htup0 with hl0; injection hl0 with h10 hl0; injection hl0 with h20 _; subst h10 h20
        obtain ⟨aInd0, lvls0, rfl, haInd0, _⟩ := hH0.const_of_load ldC
        have hstrip_eq : dom0 = domPos := by
          rw [hrp_val, hni_val] at hstripPos
          have h := Option.some.inj (hstrip0.symm.trans hstripPos)
          exact (Expr.forallE.inj (Prod.mk.inj h).2).1
        have hAs0_eq : As0 = AsPos := by
          rw [← hargsPos, ← hstrip_eq, hdom0_eq, Decl.getAppArgs_mkAppN]
          simp [Expr.getAppArgs]
        have hfn0 : dom0.getAppFn = .const (Core.keyOf t (ixAddr aInd0)) lvls0 := by
          rw [hdom0_eq, Decl.getAppFn_mkAppN]; rfl
        have haInd0_eq : ixAddr aInd0 = ixAddr aIndM := by
          have hk := hfn0.symm.trans (hstrip_eq ▸ hfnPos)
          exact Core.keyOf_inj htwf (Expr.const.inj hk).1
        -- `eCi` loads `aInd0` (same record `cmM` as `aIndM`), so `xinp = .field (indM.params.toNat : F)`
        have hsub155 : CallSub cs155 calls := fun cl hcl => hsub_rmp cl (by rw [hcE]; simp [hcl])
        obtain ⟨-, _, cI, _, hhI, hbaI, hexI, -, -, -, hrawI⟩ :=
          L1.get_ci_spec (bounded_sub hsub155 hbd) haInd0 eCi
        have hrecAtI : Ix.Cert.recordAt E₀ (ixAddr aInd0) = some cmM := by
          rw [haInd0_eq, ← hS.recordOf_eq_recordAt]; exact hrecM
        have hcI_eq : cI = cmM := hS.record_eq hrecAtI (Core.hashed_mono hsub155 hhI) hbaI hexI
        subst hcI_eq
        unfold L1.GetCIRawResult at hrawI
        rw [hinfoM] at hrawI
        obtain ⟨_, _, cbI, msI, indI, vI, hhBI, hbaBI, hexBI, -, hmutsI, hmsI, hldI, hrawIndI⟩ := hrawI
        have hcbI_eq : cbI = cbM :=
          hS.record_eq ((hS.recordOf_eq_recordAt ipM.block).symm.trans hrecBM)
            (Core.hashed_mono hsub155 hhBI) hbaBI hexBI
        subst cbI
        have hmsI_eq : msI = msM := Ixon.ConstantInfo.muts.inj (hmutsI.symm.trans hmutsM)
        subst msI
        rw [Array.getElem?_toList, hmsM] at hmsI
        have hindI_eq : indI = indM := Ixon.MutConst.indc.inj (Option.some.inj hmsI).symm
        subst indI
        obtain ⟨_, _, _, _, _, _, _, _, _, _, hvI_eq, _⟩ := hrawIndI
        have hvI_ld := Except.ok.inj (ldI.symm.trans hldI)
        rw [hvI_eq] at hvI_ld
        injection hvI_ld with _ _ haI
        injection haI with _ haI; injection haI with _ haI; injection haI with hxinp_eq _
        -- `eL` gives `v257 = .field (AsPos.length : F)`
        have eL' : ObsFn Obs.W (Instance.mk "Lists::length" [(.ptr (.named "KernelTypes::KExprNode" []))]).symbol
            [x_args] m141 v257 m260 cs268 := by
          rw [Obs.Names.«Lists::length<&KernelTypes::KExprNode>».symbol]; exact eL
        have hAs141 : RepList (Instance.mk "Lists::Node" [(.ptr (.named "KernelTypes::KExprNode" []))]).symbol
            (fun h E p => Decl.TmExact (Core.keyOf t) 0 zeroGhost h (rP + rc.indices.toNat) E p) m141 As0 x_args := by
          rw [Obs.Names.«Lists::Node<&KernelTypes::KExprNode>».symbol]
          exact RepLinkedList.mono (fun _ _ _ _ ext x => x.mono ext) eCi.heap_extends hAs0
        have hv257 : v257 = .field (AsPos.length : F) := by
          rw [← hAs0_eq]; exact (Lib.Lists.length_spec eL' hAs141).1
        rw [hxinp_eq, heqIni] at opA
        have hv258 := SubstAux.add_ok opA
        rw [hv257, hv258] at heqL
        have hfeq : inpF + (rc.indices.toNat : F) = (indM.params.toNat : F) + (rc.indices.toNat : F) :=
          hAsPos_f.symm.trans (Value.field.inj heqL)
        have hinp_f : inpF = (indM.params.toNat : F) := add_right_cancel hfeq
        rw [hinp_f]
        exact SubstAux.val_natCast (by omega)
    -- 7. Transfer `majorShape` from `Core.posOf ps tyA` to `tyA`, and establish `hlvls_def`, `hpins_ok`,
    --    `husedIndM`, `hpins_used`, `hty_used`.
    have hstripA_ex : ∃ bsA domA bodyA mA, tyA.stripPis mI = some (bsA, .forallE domA bodyA mA) ∧
        domPos = Core.posOf ps domA := by
      rw [hrp_val, hni_val] at hstripPos
      unfold Core.posOf at hstripPos
      rw [stripPis_instantiateLevelParams] at hstripPos
      cases hst : tyA.stripPis (rP + rc.indices.toNat) with
      | none => rw [hst] at hstripPos; cases hstripPos
      | some q =>
        rw [hst] at hstripPos
        rcases q with ⟨bsA, remA⟩
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hstripPos
        cases remA with
        | forallE dA bA mA =>
          injection hstripPos.2 with hd _ _
          exact ⟨bsA, dA, bA, mA, rfl, hd.symm⟩
        | _ => cases hstripPos.2
    obtain ⟨bsA, domA, bodyA, mA, hstripA, hdomPos_eq⟩ := hstripA_ex
    have hfnA_ex : ∃ lvlsA, domA.getAppFn = .const (Core.keyOf t (ixAddr aIndM)) lvlsA ∧
        lvlsPos = lvlsA.map (Level.subst ps (Core.posLevels ps)) := by
      rw [hdomPos_eq] at hfnPos
      unfold Core.posOf at hfnPos
      rw [getAppFn_instantiateLevelParams] at hfnPos
      cases hf : domA.getAppFn with
      | const k ls =>
        rw [hf] at hfnPos
        simp only [Expr.instantiateLevelParams, Expr.const.injEq] at hfnPos
        exact ⟨ls, by rw [hfnPos.1], hfnPos.2.symm⟩
      | _ => rw [hf] at hfnPos; cases hfnPos
    obtain ⟨lvlsA, hfnA, hlvlsPos_eq⟩ := hfnA_ex
    let pinsA := (domA.getAppArgs.take indM.params.toNat).map (Expr.lowerBVars rc.indices.toNat 0)
    have hAsPos_map : AsPos = domA.getAppArgs.map (Core.posOf ps) := by
      rw [← hargsPos, hdomPos_eq]; exact getAppArgs_instantiateLevelParams _ _ domA
    have hpinsPos_map : (AsPos.take (ZMod.val inpF)).map (Expr.lowerBVars (ZMod.val (rc.indices.toNat : F)) 0) =
        pinsA.map (Core.posOf ps) := by
      rw [hinp_eq, hni_val, hAsPos_map, ← List.map_take, List.map_map, List.map_map]
      refine List.map_congr_left fun a _ => ?_
      exact lowerBVars_instantiateLevelParams _ _ _ _ a
    have hmajA : majorShape tyA mI rP indM.params.toNat = some (lvlsA, pinsA) := by
      unfold majorShape
      rw [ite_eq_left_iff.mpr (fun hn => absurd (by omega) hn),
        show mI - rP = rc.indices.toNat by omega, hstripA]
      dsimp only
      rw [hfnA]
      dsimp only
      have hlen_dom : domA.getAppArgs.length = indM.params.toNat + rc.indices.toNat := by
        have h1 : AsPos.length = domA.getAppArgs.length := by rw [hAsPos_map, List.length_map]
        rw [hinp_eq, hni_val] at hAsPos_len; omega
      have htake_dom : domA.getAppArgs.take indM.params.toNat =
          pinsA.map (Expr.liftLooseBVars rc.indices.toNat 0) := by
        simp only [pinsA, List.map_map]
        conv_lhs => rw [← List.map_id (domA.getAppArgs.take indM.params.toNat)]
        refine List.map_congr_left fun a ha => ?_
        have hmemP : Core.posOf ps a ∈ AsPos.take (ZMod.val inpF) := by
          rw [hinp_eq, hAsPos_map, ← List.map_take]
          exact List.mem_map.mpr ⟨a, ha, rfl⟩
        have hno := hnoLoosePos _ hmemP
        rw [hni_val] at hno
        unfold Core.posOf at hno
        rw [noLooseIn_instantiateLevelParams] at hno
        exact (liftLooseBVars_lowerBVars_of_noLooseIn rc.indices.toNat 0 a hno).symm
      have hdrop_dom : domA.getAppArgs.drop indM.params.toNat =
          (List.range rc.indices.toNat).map (fun i => Expr.bvar (rc.indices.toNat - 1 - i)) := by
        have hpos_eq : (domA.getAppArgs.drop indM.params.toNat).map (Core.posOf ps) =
            ((List.range rc.indices.toNat).map (fun i => Expr.bvar (rc.indices.toNat - 1 - i))).map
              (Core.posOf ps) := by
          rw [List.map_drop, ← hAsPos_map, ← hinp_eq, hdropPos, hni_val, List.map_map]
          rfl
        exact (List.map_injective_iff.mpr fun _ _ h => Decl.posOf_inj hperm h) hpos_eq
      rw [ite_eq_left_iff.mpr fun hn => absurd ⟨hlen_dom, htake_dom, hdrop_dom⟩ hn]
    have hlvls_def : lvlsA.all (Level.allParamsDefined ps) = true := by
      have hrem_def := allLevelParamsDefined_stripPis mI htyA_def hstripA
      simp only [Expr.allLevelParamsDefined, Bool.and_eq_true] at hrem_def
      have hfn_def := allLevelParamsDefined_getAppFn domA hrem_def.1.1
      rw [hfnA] at hfn_def
      exact hfn_def
    have htyA_lbb : tyA.looseBVarsBounded 0 = true := by
      rw [Decl.annotates_looseBVarsBounded hann_ty 0]; exact hty₀_lbb
    have hpins_ok : pinsA.all (fun p => !p.hasFvar && p.looseBVarsBounded rP &&
        p.allLevelParamsDefined ps) = true := by
      refine List.all_eq_true.mpr fun p hp => ?_
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hp
      have ha_in : a ∈ domA.getAppArgs := List.mem_of_mem_take ha
      have hrem_fv := hasFvar_stripPis mI htyA_fv hstripA
      simp only [Expr.hasFvar, Bool.or_eq_false_iff] at hrem_fv
      have ha_fv := hasFvar_getAppArgs domA hrem_fv.1 a ha_in
      have hrem_lbb := looseBVarsBounded_stripPis mI 0 htyA_lbb hstripA
      simp only [Nat.zero_add, Expr.looseBVarsBounded, Bool.and_eq_true] at hrem_lbb
      have ha_lbb := looseBVarsBounded_getAppArgs mI domA hrem_lbb.1 a ha_in
      have hrem_def := allLevelParamsDefined_stripPis mI htyA_def hstripA
      simp only [Expr.allLevelParamsDefined, Bool.and_eq_true] at hrem_def
      have ha_def := allLevelParamsDefined_getAppArgs domA hrem_def.1.1 a ha_in
      have hno_a : Decl.noLooseIn 0 rc.indices.toNat a = true := by
        have hmemP : Core.posOf ps a ∈ AsPos.take (ZMod.val inpF) := by
          rw [hinp_eq, hAsPos_map, ← List.map_take]
          exact List.mem_map.mpr ⟨a, ha, rfl⟩
        have hno := hnoLoosePos _ hmemP
        rw [hni_val] at hno
        unfold Core.posOf at hno
        rwa [noLooseIn_instantiateLevelParams] at hno
      have hlbb_low := looseBVarsBounded_lowerBVars_of_noLooseIn rP rc.indices.toNat 0 a
        (by simpa [mI] using ha_lbb) hno_a
      simp only [Nat.add_zero] at hlbb_low
      simp [hasFvar_lowerBVars, ha_fv, hlbb_low, allLevelParamsDefined_lowerBVars, ha_def]
    -- `UsedRef E₀ rb` for every `AddrIn C.m67 C.ty a`, and in particular for `ixAddr aIndM`
    have hty_used_67 : ∀ a, AddrIn C.m67 C.ty a → UsedRef E₀ rb (ixAddr a) := by
      intro a ha
      rcases L1.RawConvExpr.addrIn_used rty a ha with ⟨i_r, hi_u, hi_ref⟩ | hnil
      · refine ⟨crb, i_r, hR.record, ?_, by rw [← Array.getElem?_toList]; exact hi_ref⟩
        unfold usedRefIdxs; rw [hR.muts]
        rcases hi_u with hi_e | ⟨s_sh, hs_sh, hi_s⟩
        · have hmem_rs : Ixon.MutConst.recr rc ∈ rs.toList :=
            List.mem_of_getElem? (by rw [Array.getElem?_toList]; exact hrk)
          exact List.mem_append_right _ (List.mem_flatMap.mpr
            ⟨.recr rc, hmem_rs, List.mem_append_left _ hi_e⟩)
        · exact List.mem_append_left _ (List.mem_flatMap.mpr ⟨s_sh, hs_sh, hi_s⟩)
      · cases hnil
    have husedIndM : UsedRef E₀ rb (ixAddr aIndM) := by
      have hki : KeyIn (Core.keyOf t (ixAddr aIndM)) (Core.posOf ps tyA) := by
        rw [hrp_val, hni_val] at hstripPos
        have hfn_ki : ∀ e : KExpr, e.getAppFn = .const (Core.keyOf t (ixAddr aIndM)) lvlsPos →
            KeyIn (Core.keyOf t (ixAddr aIndM)) e := by
          intro e; induction e with
          | const k ls => intro h; injection h with hk _; exact hk.symm
          | app f a ihf _ => intro h; exact Or.inl (ihf h)
          | _ => intro h; cases h
        exact keyIn_stripPis (Core.keyOf t (ixAddr aIndM)) mI hstripPos (Or.inl (hfn_ki domPos hfnPos))
      obtain ⟨a', ha', hk'⟩ := addrIn_of_keyIn_tmExact (htm_tyA 0 zeroGhost) _ hki
      have heq : ixAddr a' = ixAddr aIndM := Core.keyOf_inj htwf hk'
      rw [← heq]; exact hty_used_67 a' ha'
    -- `AddrIn` backward on `x_pins` via `addrIn_rec_major_pins`
    have hpins_addr := addrIn_rec_major_pins evRmp' ((htm_tyA 0 zeroGhost).mono ext_67_838) hpins_rmp
    rw [hpinsPos_map, hrp_val] at hpins_addr
    have hpins_mInd : RepList kexprListEnum
        (fun h P p => Decl.TmExact (Core.keyOf t) 0 zeroGhost h rP P p ∧
          ∀ a, AddrIn h p a → UsedRef E₀ rb (ixAddr a)) mInd
        (pinsA.map (Core.posOf ps)) x_pins := by
      have hsub_u : ∀ a, AddrIn mRmp C.ty a → UsedRef E₀ rb (ixAddr a) := fun a ha =>
        hty_used_67 a (Binding.TmExact.addrIn_back (htm_tyA 0 zeroGhost)
          (ext_67_838.trans evRmp.heap_extends) a ha)
      have hrmp_used : RepList kexprListEnum
          (fun h P p => Decl.TmExact (Core.keyOf t) 0 zeroGhost h rP P p ∧
            ∀ a, AddrIn h p a → UsedRef E₀ rb (ixAddr a)) mRmp
          (pinsA.map (Core.posOf ps)) x_pins :=
        repList_map_pred (fun _ _ ⟨ht', ha'⟩ => ⟨ht', fun a ha => hsub_u a (ha' a ha)⟩) hpins_addr
      exact RepLinkedList.mono (fun _ _ _ _ ext ⟨ht', hu'⟩ =>
        ⟨ht'.mono ext, fun a ha => hu' a (Binding.TmExact.addrIn_back ht' ext a ha)⟩)
        evGetInd.heap_extends hrmp_used
    -- 8. Run `rulesTrace_walk` on `evGo`!
    have ext_h_mInd : Heap.Extends h mInd := C.evGetRec.extends.trans ext_67_mInd
    have evGo' := evGo
    rw [hnl_eq, ← hps_len, hrp_eq, hni_eq, show rc.indices.toNat = mI - rP by omega,
      hx_iidx_eq, hx_inp_eq] at evGo'
    rw [show (.field 0 : SourceValue F) = .field ((0 : Nat) : F) by simp] at evGo'
    rw [hlvlsPos_eq] at hilvls_rmp
    obtain ⟨rules₀, rhss, thms, rlsCan, remBytes, hstr_out, hrr_rules, hrules_sc,
        hcanon_rules, hf2_rules, hcprj_all, hrules_step⟩ :=
      rulesTrace_walk ht hbd hS hH hB hR hrecBM hmutsM hip_lt hmsM htypes hctors hrecs hlenSD
        hlenNR hctorLookup hrecRefs hrk hperm hps_len hlvls_lt (by omega) (by omega) hindM_np_lt
        hmajA hlvls_def hpins_ok hblob built hbBlkM_eq hg_eq.symm haMd_in_dst
        (rus := rc.rules.toList) (fun _ hm => hm)
        (j := 0) (root := ((L1.mutsRootOffset rs.toList k : Nat) : F) + 1)
        (by rw [Nat.zero_add, Array.length_toList]; exact hcntRules) hindM_nc_lt hsub_go
        (RCRep.mono ext_h_mInd hrc) (Bytes.repAddressRef_heapMono₂ addrTy ext_h_mInd haMd_rep)
        hbBlkM_ref (RepLinkedList.mono (Bytes.repAddressRef_heapMono₂ addrTy) ext_h_mInd hsrc_rep)
        (RepLinkedList.mono (Bytes.repAddressRef_heapMono₂ addrTy) ext_h_mInd hdst_rep)
        (AddrMapAll.mono (fun _ _ _ _ _ x => x) ext_h_mInd haset_rep)
        (htm_tyA.mono ext_67_mInd)
        (fun a ha => hty_used_67 a (Binding.TmExact.addrIn_back (htm_tyA 0 zeroGhost) ext_67_mInd a ha))
        (hilvls_rmp.mono evGetInd.heap_extends) hpins_mInd
        (hrlsTrace.mono ext_67_mInd (fun _ hm => hm)) (hstr_s.mono ext_h_mInd) evGo'
    -- 9. Assemble `RecMemberData`!
    have hrules_len : rules₀.length = rc.rules.size := by
      have h1 := List.Forall₂.length_eq hrr_rules
      rw [List.length_zipIdx, Array.length_toList] at h1; exact h1.symm
    have hrules_ctor : ∀ j rl, rules₀[j]? = some rl →
        rl.ctor = Core.keyOf t (cprjAddr ipM.block ipM.idx.toNat j) := by
      intro j rl hj
      have hlen_z : (rc.rules.toList.zipIdx 0).length = rules₀.length := List.Forall₂.length_eq hrr_rules
      have hj_lt : j < rules₀.length := (List.getElem?_eq_some_iff.mp hj).1
      have hget_z : (rc.rules.toList.zipIdx 0)[j]? = some (rc.rules.toList[j]'(by rw [Array.length_toList, ← hrules_len]; exact hj_lt), j) := by
        rw [List.getElem?_zipIdx, List.getElem?_eq_getElem (by rw [Array.length_toList, ← hrules_len]; exact hj_lt)]
        simp
      have hrel := (List.forall₂_iff_get.mp hrr_rules).2 j (by omega) hj_lt
      simp only [List.get_eq_getElem] at hrel
      have hrl_eq : rules₀[j] = rl := Option.some.inj ((List.getElem?_eq_getElem hj_lt).symm.trans hj)
      rw [hrl_eq] at hrel
      obtain ⟨_, _, hmk⟩ := hrel
      have hz_eq : (rc.rules.toList.zipIdx 0)[j] = (rc.rules.toList[j]'(by rw [Array.length_toList, ← hrules_len]; exact hj_lt), j) :=
        Option.some.inj ((List.getElem?_eq_getElem (by omega)).symm.trans hget_z)
      rw [hz_eq] at hmk
      rw [hmk]; simp [LoadedReads.ctorAddr_eq_cprjAddr]; rfl
    -- `ReadsIn` given `InLogic cbM`
    have hreads_of_logic : InLogic cbM →
        ReadsIn t (recordOf E₀) (fun x => E₀.blobs.get? x) (memberAddr rb k (.recr rc))
          (.recInfo ⟨Core.keyOf t (rprjAddr rb k), ps, ty₀⟩ mI rP rules₀) := by
      intro hlogM
      have hIndF : IndKeyAt t (recordOf E₀) (Core.keyOf t (iprjAddr B 0)) B 0 ind0 := by
        have hrec0 : recordOf E₀ (iprjAddr B 0) = some (memberProjection B 0 (.indc ind0)) := by
          rw [← LoadedReads.memberAddr_indc]; exact hB.members 0 (.indc ind0) hms0
        exact ⟨iprjAddr B 0, memberProjection B 0 (.indc ind0), ⟨0, B⟩, cb, ms, rfl, hrec0, rfl,
          rfl, rfl, hB.record, hB.muts, hms0, rfl, by rw [LoadedReads.memberAddr_indc], hB.logic⟩
      have hIndM : IndKeyAt t (recordOf E₀) (Core.keyOf t (ixAddr aIndM)) ipM.block ipM.idx.toNat indM :=
        ⟨ixAddr aIndM, cmM, ipM, cbM, msM, rfl, hrecM, hinfoM, rfl, rfl,
          hrecBM, hmutsM, hmsM, hcmM_can, haIndM_can, hlogM⟩
      have hrr : RecReads t (recordOf E₀) (fun x => E₀.blobs.get? x) crb (blockSelf t rb rs)
          (Core.keyOf t (rprjAddr rb k)) rc
          (.recInfo ⟨Core.keyOf t (rprjAddr rb k), ps, ty₀⟩ mI rP rules₀) :=
        ⟨tyP, ty₀, Core.keyOf t (iprjAddr B 0), Core.keyOf t (ixAddr aIndM), B, ipM.block, 0,
          ipM.idx.toNat, ind0, indM, ps, rules₀, hreadP, hfamKey, hIndF, hmajKey_ind, hIndM,
          rfl, hread₀, hcntRules, hrr_rules, rfl⟩
      unfold ReadsIn
      refine ⟨memberProjection rb k (.recr rc), hR.members k (.recr rc) hrk, ?_⟩
      show ∃ cb' ms' rc',
        MemberAt (recordOf E₀) (memberAddr rb k (.recr rc)) (memberProjection rb k (.recr rc))
          rb cb' ms' k.toUInt64.toNat (.recr rc') ∧
        RecReads t (recordOf E₀) (fun x => E₀.blobs.get? x) cb' (blockSelf t rb ms')
          (Core.keyOf t (memberAddr rb k (.recr rc))) rc' _
      rw [hk_toNat, LoadedReads.memberAddr_recr]
      exact ⟨crb, rs, rc, ⟨hR.record, hR.muts, hrk, rfl, by rw [LoadedReads.memberAddr_recr], hR.logic⟩, hrr⟩
    exact ⟨⟨{
      ps, ty₀, tyA, rules₀, rhss, thms
      aIndM, cmM, ipM, cbM, msM, indM
      hrecM, hinfoM, hcmM_can, haIndM_can, hrecBM, hmutsM, hmsM, husedIndM, hcntRules
      hcntLt := hindM_nc_lt
      hnotK, hps_len
      hty_lbb := hty₀_lbb
      hty_def := hty₀_def
      hrules_sc, hcanon_ty
      hcanon_rules := ⟨rlsCan, hcanon_rules, hf2_rules⟩
      hment
      hhead := ⟨domA, lvlsA, pinsA, piDomAt_eq_of_stripPis mI hstripA, hfnA, hmajA⟩
      hrules_len, hrules_ctor
      hrules_recCprj := fun j hj => by
        rw [hrules_len, ← Array.length_toList] at hj
        simpa using hcprj_all j hj
      hreads := hreads_of_logic
      hmemFacts := fun hSE hadv hdefSrc => (hmemStep hSE hadv hdefSrc).2 mI rP rules₀
      hrulesFacts := fun recsBlk recsTys hSE hadv hadvHyp hdefSrc hmodels => by
        have hnp_ty := (hmemStep hSE hadv hdefSrc).1
        have hleaves := pinsP_leavesFixed ht (bounded_sub hsub hbd) hlenSD C hnp_eq hn_eq hnmin_eq
          hni_eq hnp_lt hnmot_lt hnmin_lt hni_lt hsrc_rep hdst_rep hperm htyA_fv hnp_ty
          (htm_tyA 0 zeroGhost) hmajA
        exact hrules_step recsBlk recsTys hSE hadvHyp hdefSrc hmodels hnp_ty hleaves
    }⟩, remBytes, hstr_out⟩

/-- **Element-wise walk of `KernelModeled::check_recs`** over remaining `(recAs', recMs')` paired
with their `MemberValItem`s from `evRecsVal`, starting at recursor index `k0`. -/
theorem checkRecs_walk
    {calls : List (Call F)} {bAddr : _root_.Address} {t : Ix.Kernel.RoleTable}
    {E₀ : Ixon.Env} {lim : Option Nat} {csFam : List (Call F)}
    {B rb : _root_.Address} {cb crb : Ixon.Constant} {ms rs : Array Ixon.MutConst}
    (ht : t.check = .ok ()) (hbd : Bounded calls)
    (hS : LoadedReads.RunStore calls E₀) (hH : LoadedReads.HashedRecordsStored calls E₀)
    (hB : FamBlockRecord E₀ B cb ms) (hR : FamRecRecord E₀ rb crb rs)
    {advAs typeAs ctorAs recAs dstAs : List Bytes.Address}
    (htypes : typeAs.map ixAddr =
      ms.toList.mapIdx fun i m => projAddr (Specs.Callees.memberProjInfo B i m))
    (hctors : ctorAs.map ixAddr = ctorAddrsFrom B ms.toList 0)
    (hrecs : recAs.map ixAddr =
      rs.toList.mapIdx fun i m => projAddr (Specs.Callees.memberProjInfo rb i m))
    (hlenSD : (typeAs ++ ctorAs ++ recAs).length = dstAs.length)
    {nonrecsBlk : List (ConstantInfo .anon)} {nonrecsTys : List KExpr}
    (hlenNR : nonrecsBlk.length = nonrecsTys.length)
    (hctorLookup : CtorLookupFn.{u} calls bAddr t E₀ lim csFam B rb cb crb ms advAs
      (typeAs ++ ctorAs ++ recAs) dstAs nonrecsBlk nonrecsTys)
    (hrecRefs : ∀ x, UsedRef E₀ rb x → Claim.CoveredAt t lim x ∨ NeedOk E₀ x)
    {a0 : Bytes.Address} {restTypeAs : List Bytes.Address} {ind0 : Ixon.Inductive}
    (htypeAs_cons : typeAs = a0 :: restTypeAs) (ha0_eq : ixAddr a0 = iprjAddr B 0)
    (hms0 : ms[0]? = some (.indc ind0)) (hind0_lvls_lt : ind0.lvls.toNat < 4294967296)
    (hrs_u64 : rs.size < UInt64.size)
    {rcV tys src dst aset n np uo bnl fam : SourceValue F}
    (hbnl_eq : bnl = .field (ind0.lvls.toNat : F))
    (huo : uo = .field 0 ∨ uo = .field 1) :
    ∀ (k0 : Nat) (remRecs remMods : List Bytes.Address)
      {recsPtr modsPtr s form r : SourceValue F} {bytes : List UInt8}
      {h h' : Heap F} {cs : List (Call F)},
      k0 + remRecs.length = rs.size →
      (hlen : remRecs.length = remMods.length) →
      (∀ idx (hi : idx < remRecs.length), ixAddr remRecs[idx] = rprjAddr rb (k0 + idx)) →
      (∀ idx (hi : idx < remRecs.length),
        aliasMap (((typeAs ++ ctorAs ++ recAs).map fun b => Core.keyOf t (ixAddr b)).zip
          (dstAs.map fun b => Core.keyOf t (ixAddr b))) (Core.keyOf t (rprjAddr rb (k0 + idx))) =
          Core.keyOf t (ixAddr (remMods[idx]'(by rw [← hlen]; exact hi)))) →
      (∀ b ∈ remMods, b ∈ dstAs) →
      List.Forall₂ (fun aM aMd =>
        Nonempty (MemberValItem calls bAddr t E₀ lim csFam advAs
          (typeAs ++ ctorAs ++ recAs) dstAs recAs aM aMd)) remRecs remMods →
      CallSub cs calls →
      RCRep t lim h rcV →
      RepList addrListEnum (Bytes.RepAddressRef addrTy) h typeAs tys →
      RepList addrListEnum (Bytes.RepAddressRef addrTy) h remRecs recsPtr →
      RepList addrListEnum (Bytes.RepAddressRef addrTy) h remMods modsPtr →
      RepList addrListEnum (Bytes.RepAddressRef addrTy) h (typeAs ++ ctorAs ++ recAs) src →
      RepList addrListEnum (Bytes.RepAddressRef addrTy) h dstAs dst →
      AddrMapAll addrMapEnum (fun _ k _ => AdvChecked calls bAddr t lim csFam advAs k) h aset →
      L1.Stream h bytes s →
      ObsFn Obs.W "KernelModeled::check_recs"
        [rcV, tys, recsPtr, modsPtr, src, dst, aset, s, n, .field (k0 : F), np, uo, bnl, fam, form]
        h r h' cs →
      ∃ (recsBlk : List (ConstantInfo .anon)) (recsTys : List KExpr)
        (rhsss : List (List KExpr)) (thmsList : List (List KKey)),
        recsBlk.length = remRecs.length ∧
        recsTys.length = remRecs.length ∧
        rhsss.length = remRecs.length ∧
        thmsList.length = remRecs.length ∧
        ∀ idx (hi : idx < remRecs.length),
          ∃ (rc : Ixon.Recursor)
            (D : RecMemberData.{u} calls bAddr t E₀ lim csFam B rb cb crb ms rs advAs
              (typeAs ++ ctorAs ++ recAs) dstAs recAs nonrecsBlk nonrecsTys
              (k0 + idx) rc remRecs[idx] (remMods[idx]'(by rw [← hlen]; exact hi))),
            rs[k0 + idx]? = some (.recr rc) ∧
            recsBlk[idx]? = some D.recInfo ∧
            recsTys[idx]? = some D.tyA ∧
            rhsss[idx]? = some D.rhss ∧
            thmsList[idx]? = some D.thms := by
  intro k0 remRecs
  induction remRecs generalizing k0 with
  | nil =>
    intro remMods recsPtr modsPtr s form r bytes h h' cs _ hlen _ _ _ _ _ _ _ _ _ _ _ _ _ _
    cases remMods with
    | nil => exact ⟨[], [], [], [], rfl, rfl, rfl, rfl, fun _ hi => nomatch hi⟩
    | cons _ _ => simp at hlen
  | cons aRec restRecs ih =>
    intro remMods recsPtr modsPtr s form r bytes h h' cs hsum hlen ha_eq hg_eq hsubDst hitems
      hsub hrc htys hrecsP hmodsP hsrc hdst haset hstr ev
    cases remMods with
    | nil => simp at hlen
    | cons aMd restMods =>
      rcases checkRecs_step ev with ⟨ldNil, _, _⟩ | ⟨⟨C⟩⟩
      · exact absurd (Lib.rep_nil_of_load hrecsP ldNil) (List.cons_ne_nil _ _)
      · obtain ⟨_, _, hcr, haRec_rep, hrestR_rep⟩ := Lib.rep_cons_of_load hrecsP C.ldRecs
        injection hcr with h1 h2; subst h1 h2
        obtain ⟨_, _, hcm, haMd_rep, hrestM_rep⟩ := Lib.rep_cons_of_load hmodsP C.ldModels
        injection hcm with h1 h2; subst h1 h2
        cases hitems with
        | cons hitem0 hitems_rest =>
          obtain ⟨item0⟩ := hitem0
          have hk0_lt : k0 < rs.size := by simp at hsum; omega
          have hm0_get : rs[k0]? = some rs[k0] := Array.getElem?_eq_getElem hk0_lt
          obtain ⟨rc, hrc_eq⟩ := hR.recrs rs[k0] (Array.mem_toList_iff.mpr (Array.getElem_mem hk0_lt))
          have hrk : rs[k0]? = some (.recr rc) := by rwa [hrc_eq] at hm0_get
          have ha0 : ixAddr aRec = rprjAddr rb k0 := by
            have h0 := ha_eq 0 (by simp)
            simp only [List.getElem_cons_zero, Nat.add_zero] at h0
            exact h0
          have hg0 := hg_eq 0 (by simp)
          simp only [Nat.add_zero, List.getElem_cons_zero] at hg0
          obtain ⟨⟨D0⟩, remBytes, hstr_mid⟩ :=
            recMember_of_cons ht hbd hS hH hB hR htypes hctors hrecs hlenSD hlenNR hctorLookup
              hrecRefs htypeAs_cons ha0_eq hms0 hind0_lvls_lt hsub C (Nat.lt_trans hk0_lt hrs_u64)
              hrk rfl hbnl_eq huo ha0 hg0 (hsubDst aMd List.mem_cons_self) hrc htys
              haRec_rep haMd_rep hsrc hdst haset hstr item0
          -- Advance to `C.evNext` at `k0 + 1`
          have hk1_eq : C.k' = .field ((k0 + 1 : Nat) : F) := by
            rw [SubstAux.add_ok C.opKNext, Nat.cast_add, Nat.cast_one]
          have evNext' : ObsFn Obs.W "KernelModeled::check_recs"
              [rcV, tys, C.rest, C.mrest, src, dst, aset, C.s', n, .field ((k0 + 1 : Nat) : F),
                np, uo, bnl, fam, C.form'] C.m892 r h' C.evNext.cs := by
            rw [← hk1_eq]; exact C.evNext.obs
          have ext_h_892 : Heap.Extends h C.m892 := C.ext_h_m838.trans C.evRules.extends
          have hsub_next : CallSub C.evNext.cs calls := fun cl hcl => hsub cl (C.evNext.sub cl hcl)
          have hha_rest : ∀ idx (hi : idx < restRecs.length),
              ixAddr restRecs[idx] = rprjAddr rb (k0 + 1 + idx) := fun idx hi => by
            have h1 := ha_eq (idx + 1) (by simp; omega)
            simp only [List.getElem_cons_succ] at h1
            rwa [show k0 + (idx + 1) = k0 + 1 + idx by omega] at h1
          have hhg_rest : ∀ idx (hi : idx < restRecs.length),
              aliasMap (((typeAs ++ ctorAs ++ recAs).map fun b => Core.keyOf t (ixAddr b)).zip
                (dstAs.map fun b => Core.keyOf t (ixAddr b))) (Core.keyOf t (rprjAddr rb (k0 + 1 + idx))) =
                Core.keyOf t (ixAddr (restMods[idx]'(by simp at hlen; omega))) := fun idx hi => by
            have h1 := hg_eq (idx + 1) (by simp; omega)
            simp only [List.getElem_cons_succ] at h1
            rwa [show k0 + (idx + 1) = k0 + 1 + idx by omega] at h1
          obtain ⟨recsBlkR, recsTysR, rhsssR, thmsR, hl1, hl2, hl3, hl4, hgetR⟩ :=
            ih (k0 + 1) restMods (by simp at hsum; omega) (by simp at hlen; omega)
              hha_rest hhg_rest
              (fun b hb => hsubDst b (List.mem_cons_of_mem _ hb)) hitems_rest hsub_next
              (RCRep.mono ext_h_892 hrc)
              (RepLinkedList.mono (Bytes.repAddressRef_heapMono₂ addrTy) ext_h_892 htys)
              (RepLinkedList.mono (Bytes.repAddressRef_heapMono₂ addrTy) ext_h_892 hrestR_rep)
              (RepLinkedList.mono (Bytes.repAddressRef_heapMono₂ addrTy) ext_h_892 hrestM_rep)
              (RepLinkedList.mono (Bytes.repAddressRef_heapMono₂ addrTy) ext_h_892 hsrc)
              (RepLinkedList.mono (Bytes.repAddressRef_heapMono₂ addrTy) ext_h_892 hdst)
              (AddrMapAll.mono (fun _ _ _ _ _ x => x) ext_h_892 haset)
              hstr_mid evNext'
          refine ⟨D0.recInfo :: recsBlkR, D0.tyA :: recsTysR, D0.rhss :: rhsssR, D0.thms :: thmsR,
            by simp [hl1], by simp [hl2], by simp [hl3], by simp [hl4], fun idx hi => ?_⟩
          cases idx with
          | zero => exact ⟨rc, D0, hrk, rfl, rfl, rfl, rfl⟩
          | succ idx' =>
            have hi' : idx' < restRecs.length := by simp at hi; omega
            obtain ⟨rc', D', hrk', hb', ht', hrh', hth'⟩ := hgetR idx' hi'
            have hcast : ∀ {k1 k2 : Nat}, k1 = k2 →
                ∀ (D1 : RecMemberData.{u} calls bAddr t E₀ lim csFam B rb cb crb ms rs advAs
                    (typeAs ++ ctorAs ++ recAs) dstAs recAs nonrecsBlk nonrecsTys
                    k1 rc' restRecs[idx'] (restMods[idx']'(by simp at hlen; omega))),
                  rs[k1]? = some (.recr rc') →
                  recsBlkR[idx']? = some D1.recInfo →
                  recsTysR[idx']? = some D1.tyA →
                  rhsssR[idx']? = some D1.rhss →
                  thmsR[idx']? = some D1.thms →
                  ∃ (D2 : RecMemberData.{u} calls bAddr t E₀ lim csFam B rb cb crb ms rs advAs
                      (typeAs ++ ctorAs ++ recAs) dstAs recAs nonrecsBlk nonrecsTys
                      k2 rc' restRecs[idx'] (restMods[idx']'(by simp at hlen; omega))),
                    rs[k2]? = some (.recr rc') ∧
                    recsBlkR[idx']? = some D2.recInfo ∧
                    recsTysR[idx']? = some D2.tyA ∧
                    rhsssR[idx']? = some D2.rhss ∧
                    thmsR[idx']? = some D2.thms := by
              rintro k1 _ rfl D1 h1 h2 h3 h4 h5
              exact ⟨D1, h1, h2, h3, h4, h5⟩
            obtain ⟨D2, hrk2, hb2, ht2, hrh2, hth2⟩ :=
              hcast (show k0 + 1 + idx' = k0 + (idx' + 1) by omega) D' hrk' hb' ht' hrh' hth'
            exact ⟨rc', D2, hrk2, hb2, ht2, hrh2, hth2⟩

end IxVM.Refinement.Typing.FamilyAlias
