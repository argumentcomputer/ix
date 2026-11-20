import IxVMRefinement.Assembly.NativeBlockCtorSpecs
import IxVMRefinement.Guard.CheckedFields
import IxVMRefinement.Decl.NativeCtorScoped
import IxVMRefinement.Ingress.TraceRecords

/-! # The constructor loop of a native block at the constructor stage

`Decl.native_ctor_scoped_runs` refines the loop `check_inductive_shape_ctors` at a table-keyed
context. Here the same refinement is stated at the constructor stage: the typed calls of each
iteration (`k_ensure_sort` on the constructor's type, `check_param_agreement`,
`check_field_universes`) are read at a scoped context `cS` of any keying whose load contract
holds and which allows every call (the stage `Decl.ctorStage` is of this kind); the raw scans
(`check_ctor_return_type`, `check_positivity`) are read at the table-keyed record context of the
same base (`Ingress.traceRecordCtx`), as before.

* `StagedCtorLoads`: the family of constructor loads, with the stored constructor's value
  represented exactly under the stage's keying and its raw type under the table's;
  `CtorLoadAtIndex.staged` is the table-keyed instance.
* `native_ctor_staged_runs_checked`: each iteration's outputs (`Decl.NativeCtorOut`) at the
  stage's environment. At a structure-like proposition (one constructor, no index, a sort that
  evaluates to zero) the field sorts are the ones the classifier's field loop checked
  (`KernelGuard::check_prop_fields`), and the output carries that loop's run data
  (`GuardData.CheckedFieldsAt`); elsewhere they are `check_field_universes`'s, as before.
* `native_ctor_staged_checked`, `native_ctor_staged`: the whole loop, with and without the run
  data.
-/

namespace IxVM.Refinement.Decl

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open IxVM.Refinement.Core
open IxVM.Refinement.KernelLevels (RepKLevel RepKLevelList repKLevel_heapMono₂)
open Ix.Kernel (ConstantInfo ConstantVal Declaration Expr Level LevelParam)
open Ix.Kernel.Rules (Red DefEq Infer)
open Ix.Kernel.Semantics (ConstantValCheckJ FieldSortsJ)
open Ix.Kernel.Model (rulesJ)

set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-- **The constructor family the loop loads, at a stage keying `κ`**: as `CtorLoadAtIndex`, with
the stored constructor's value represented exactly under `κ` (its name is not part of that
representation); the raw type keeps the table's keying, under which the raw scans read it. -/
def StagedCtorLoads (κ : _root_.Address → KKey) (t : Ix.Kernel.RoleTable) (b₀ : Bytes.Address)
    (nP : Nat) (indIndex : F) (cs_root : List (Call F)) (ctors ctorsA : List (KConstantVal × Nat))
    (ctorRawTypes : List KExpr) : Prop :=
  ctorsA.length = ctors.length ∧
  ∀ j < ctors.length, ∃ c cvCa₀,
    ctors[j]? = some c ∧
    ctorsA[j]? = some (cvCa₀, c.2) ∧
    IxVM.Consistency.ValStored cvCa₀ c.1 ∧
    ∀ (bp ptr : SourceValue F) (h h' : Heap F) (cs : List (Call F)),
      (∀ x ∈ cs, x ∈ cs_root) →
      Bytes.RepAddressRef addrTy h b₀ bp →
      ObsFn W "Ingress::get_ci_cprj" [bp, .field indIndex, .field (j : F)] h ptr h' cs →
      ∃ (nl cty cblk cnp cnf : SourceValue F) (b_c : Bytes.Address),
        loadValue h' ptr = .ok (.construct kciEnum "Ctor"
          [nl, cty, cblk, .field indIndex, .field (j : F), cnp, cnf, .field 0]) ∧
        Bytes.RepAddressRef addrTy h' b_c cblk ∧
        ixAddr b_c = ixAddr b₀ ∧
        (∀ d Γ, RawTmExact (keyOf t) d Γ h' 0
          (ctorRawTypes.getD j default) (posOf cvCa₀.levelParams cvCa₀.type) cty) ∧
        ValRepExact κ h' nl cty cvCa₀ ∧ cnp = .field (nP : F) ∧ cnf = .field (c.2 : F)

/-- The table-keyed family is the family at the table's keying. -/
theorem CtorLoadAtIndex.staged {t : Ix.Kernel.RoleTable} {b₀ : Bytes.Address} {nP : Nat}
    {indIndex : F} {cs_root : List (Call F)} {ctors ctorsA : List (KConstantVal × Nat)}
    {ctorRawTypes : List KExpr}
    (h : CtorLoadAtIndex t b₀ nP indIndex cs_root ctors ctorsA ctorRawTypes) :
    StagedCtorLoads (keyOf t) t b₀ nP indIndex cs_root ctors ctorsA ctorRawTypes := by
  refine ⟨h.1, fun j hj => ?_⟩
  obtain ⟨c, cvCa₀, hc, hcA, hvs, hload⟩ := h.2 j hj
  refine ⟨c, cvCa₀, hc, hcA, hvs, fun bp ptr h₁ h₂ cs hsub hbp ev => ?_⟩
  obtain ⟨nl, cty, cblk, cnp, cnf, b_c, hld, hb_c, hbeq, hraw, hci⟩ :=
    hload bp ptr h₁ h₂ cs hsub hbp ev
  obtain ⟨hv, hnp, hnf⟩ := CIRepExact.ctor_inv hci
  exact ⟨nl, cty, cblk, cnp, cnf, b_c, hld, hb_c, hbeq, hraw, hv, hnp, hnf⟩

/-- **The constructor loop at the constructor stage.** From the iteration at slot `j` on, every
constructor of the family is checked at the stage `cS`: its stored value is checked
(`ConstantValCheckJ`), its type is a sort there, its parameter domains are the former's, its
fields have their sorts, and the raw scans give its residual and its field kinds. The typed calls
are read at `cS` (any keying, every call allowed, its load contract `loads`); the raw scans at the
record context of the run (`Ingress.traceRecordCtx`). At a structure-like proposition the sorts are
those of the classifier's field loop, with its run data (module docstring). -/
theorem native_ctor_staged_runs_checked (hLevels : IxVM.Consistency.Levels)
    {cS : ScopedCtx} (hall : ∀ call, cS.allowed call) {indIndex : F}
    {b₀ : Bytes.Address} {T : KKey} {lps : List LevelParam}
    {nP nIdx : Nat} {ta : KExpr} {resSort ind_lvl : KLevel}
    {cs_root : List (Call F)} {ctors ctorsA : List (KConstantVal × Nat)}
    {ctorRawTypes : List KExpr}
    (hlps : lps = List.range lps.length)
    (hlps_lt : lps.length < 4294967296)
    (hnP_lt : nP < 72057594037927936)
    (hnIdx_lt : nIdx < 72057594037927936)
    (hnCtors_lt : ctors.length < 549755813888)
    (hnF_lt : ∀ c ∈ ctors, c.2 < 72057594037927936)
    (hlveq : LvEq resSort ind_lvl)
    (hcload : StagedCtorLoads cS.κ cS.t b₀ nP indIndex cs_root ctors ctorsA ctorRawTypes)
    (hlps_ctors : ∀ c ∈ ctors, c.1.levelParams = lps)
    (hlbd_ctors : ∀ c ∈ ctors, c.1.type.looseBVarsBounded 0 = true)
    (hfv_ctors : ∀ c ∈ ctors, c.1.type.hasFvar = false)
    (hfresh_ctors : ∀ c ∈ ctors, cS.env.find? c.1.name = none)
    (hbasis_ctors : ∀ c ∈ ctors, Ix.Kernel.reservedBasisNames.contains c.1.name = false)
    (hshape_ctors : ∀ c ∈ ctors, c.1.name.isProjFnShape = false)
    (hno_proj_T : ∀ i, cS.env.findProj? T i = none)
    (hstore₁ : Ix.Kernel.Open.StoreInv cS.env)
    (hef₁ : CoreEnvFacts cS.toCtx)
    (loads : ScopedLoadFacts cS)
    (rawFacts : RawRecordFacts (Ingress.traceRecordCtx cS.toCtx cs_root))
    (hpeer₁ : OneTypePeerReads (Ingress.traceRecordCtx cS.toCtx cs_root) b₀ T lps.length nP nIdx
      ctors.length indIndex) :
    ∀ (m j : Nat) {rc pta bp pind r : SourceValue F} {h h' : Heap F} {cs : List (Call F)},
      m + j = ctors.length →
      (∀ x ∈ cs, x ∈ cs_root) →
      Good cS.toCtx cs →
      RCRep cS.t cS.lim h rc →
      Tm cS.κ 0 (fun _ => default) h 0 ta pta →
      Bytes.RepAddressRef addrTy h b₀ bp →
      RepKLevel h ind_lvl pind →
      ObsFn W "KernelCheck::check_inductive_shape_ctors"
        [rc, pta, .field (nP : F), .field (nIdx : F), .field (ctors.length : F),
          .field (lps.length : F), bp, .field indIndex, pind, .field 0, .field (j : F)] h r h' cs →
      ∃ sortss_suf : List (List KLevel),
        sortss_suf.length = m ∧
        ∀ t_idx < m, ∃ c cA sorts,
          ctors[j + t_idx]? = some c ∧
          ctorsA[j + t_idx]? = some cA ∧
          sortss_suf[t_idx]? = some sorts ∧
          NativeCtorOut cS.env T lps nP nIdx resSort ta
            (ctorRawTypes.getD (j + t_idx) default) c cA sorts ∧
          (ctors.length = 1 → nIdx = 0 → (∀ φ : LevelParam → Nat, Level.eval φ ind_lvl = 0) →
            GuardData.CheckedFieldsAt cS cs_root b₀ indIndex nP c.2 cA.1.type ind_lvl sorts)
  | 0, j, _, _, _, _, _, _, _, _, hmj, _, _, _, _, _, _, ev => by
    match Obs.«KernelCheck::check_inductive_shape_ctors».obs ev with
    | .n0 .. =>
      exact ⟨[], rfl, fun _ ht => absurd ht (Nat.not_lt_zero _)⟩
    | .other (op17 := op) (hne29 := hne) .. =>
      have hj_eq : j = ctors.length := by omega
      cases hj_eq.symm
      rw [evalBinOp_sub_nat (Nat.le_refl ctors.length) op, Nat.sub_self] at hne
      exact absurd rfl hne
  | m + 1, j, rc, pta, bp, pind, r, h, h', cs, hmj, hsub, hgood, hrc, hta, hbp, hpind, ev => by
    match Obs.«KernelCheck::check_inductive_shape_ctors».obs ev with
    | .n0 (op17 := op) .. =>
      have hsub_op : (.field ((0 : Nat) : F) : SourceValue F) =
          .field (((ctors.length - j : Nat) : F)) := by
        simpa using evalBinOp_sub_nat (by omega : j ≤ ctors.length) op
      have hj_eq := nat_eq_of_field_eq (by decide) (by omega) hsub_op
      omega
    | .other (m34 := m34) (p41 := p41) (cs47 := cs_cprj)
        (x_c_nlvls := xcnl) (x_cty := xcty) (x_c_block := xcblk)
        (x_c_np := xcnp) (x_c_nf := xcnf)
        (m144 := m144) (m319 := m319) (cs329 := cs_ws)
        (m356 := m356) (cs366 := cs_es) (m387 := m387)
        (m400 := m400) (m430 := m430) (cs440 := cs_pa)
        (m476 := m476) (cs486 := cs_rt) (m546 := m546) (cs556 := cs_fu)
        (m592 := m_prop) (cs602 := cs_prop) (m716 := m646) (m725 := m655) (cs718 := cs_sg) (cs765 := cs_rec) (v778 := v670)
        (ev49 := ev_cprj) (ld43 := ld_ctor) (ev154 := ev_aeq)
        (heq261 := heq_nl) (heq289 := heq_np)
        (ev331 := ev_ws) (hm395 := hm387) (ev368 := ev_es) (ev412 := ev_saf)
        (ev442 := ev_pa) (ev488 := ev_rt) (ev558 := ev_fu) (ev604 := ev_prop) (sg723 := sg_pos)
        (op862 := op_add) (ev767 := ev_rec) (hc864 := hc) .. =>
      have indexEq := evalBinOp_add_nat j 1 op_add
      subst v670
      have recurseMember : (⟨"KernelCheck::check_inductive_shape_ctors",
          [rc, pta, .field (nP : F), .field (nIdx : F), .field (ctors.length : F),
            .field (lps.length : F), bp, .field indIndex, pind, .field 0,
            .field ((j + 1 : Nat) : F)], m655⟩ : Call F) ∈ cs := by
        simp [hc]
      have e_to_rec := (ev.call_heap_bounds recurseMember).1
      have hg_rec : Good cS.toCtx cs_rec := hgood.sub (fun x hx => by simp [hc, hx])
      obtain ⟨sortss_rest, hlen_rest, hrest_out⟩ :=
        native_ctor_staged_runs_checked hLevels hall hlps hlps_lt hnP_lt hnIdx_lt hnCtors_lt
          hnF_lt hlveq hcload hlps_ctors hlbd_ctors hfv_ctors hfresh_ctors hbasis_ctors
          hshape_ctors hno_proj_T hstore₁ hef₁ loads rawFacts hpeer₁
          m (j + 1) (by omega) (fun x hx => hsub x (by simp [hc, hx])) hg_rec
          (hrc.mono e_to_rec) (hta.mono e_to_rec)
          (Bytes.repAddressRef_heapMono₂ addrTy e_to_rec hbp)
          (repKLevel_heapMono₂ e_to_rec hpind) ev_rec
      obtain ⟨c_j, cvCa₀, hc_j, hcA_j, hvs_j, hload_j⟩ := hcload.2 j (by omega)
      have hc_mem : c_j ∈ ctors := List.mem_of_getElem? hc_j
      have hc_nf_lt : c_j.2 < 72057594037927936 := hnF_lt c_j hc_mem
      have hsub_cprj : ∀ x ∈ cs_cprj, x ∈ cs_root := fun x hx => hsub x (by simp [hc, hx])
      obtain ⟨nl', cty', cblk', cnp', cnf', _, ld_c', _, _, hraw_rep, hv_rep, hnp_f, hnf_f⟩ :=
        hload_j bp p41 h m34 cs_cprj hsub_cprj hbp ev_cprj
      rw [ld_c'] at ld_ctor
      injection ld_ctor with hval; injection hval with _ _ h1
      injection h1 with hnl_eq h1; injection h1 with hcty_eq h1; injection h1 with hcblk_eq h1
      injection h1 with _ h1; injection h1 with _ h1; injection h1 with hcnp_eq h1
      injection h1 with hcnf_eq _
      cases hnl_eq.symm; cases hcty_eq.symm; cases hcblk_eq.symm
      cases hcnp_eq.symm; cases hcnf_eq.symm
      · subst heq_nl heq_np
        have e_cprj := ev_cprj.heap_extends
        have e_aeq := ev_aeq.heap_extends
        have e_ws := ev_ws.heap_extends
        have e_nil : Heap.Extends m319 m387 := by rw [hm387]; exact Heap.Extends.snoc m319 _
        have e_to_es := e_cprj.trans (e_aeq.trans (e_ws.trans e_nil))
        have hg_es : CoreGood cS cs_es :=
          CoreGood.ofRaw (hgood.sub (fun x hx => by simp [hc, hx])) (fun call _ => hall call)
        have hg_pa : CoreGood cS cs_pa :=
          CoreGood.ofRaw (hgood.sub (fun x hx => by simp [hc, hx])) (fun call _ => hall call)
        have hg_rt : Good cS.toCtx cs_rt := hgood.sub (fun x hx => by simp [hc, hx])
        have hg_fu : CoreGood cS cs_fu :=
          CoreGood.ofRaw (hgood.sub (fun x hx => by simp [hc, hx])) (fun call _ => hall call)
        have hlps_cj : cvCa₀.levelParams = List.range lps.length := by
          rw [hvs_j.2.1, hlps_ctors c_j hc_mem]
          exact hlps
        have hpos_lift : PosSortLift cS.env cvCa₀ := PosSortLift.of_range hlps_cj
        have hv_m144 : ValRepExact cS.κ m144 (.field (lps.length : F)) xcty cvCa₀ :=
          ⟨hv_rep.1, hv_rep.2.1, hv_rep.2.2.1, hv_rep.2.2.2.mono e_aeq⟩
        have hty_nil : TypesRep cS.κ (fun _ => default) m387 0
            (.ptr (.enum kexprListEnum) m319.length) := by
          rw [hm387]; exact typesRep_alloc_nil cS.κ (fun _ => default) m319
        obtain ⟨hcvC_chk, sty₀, u₀, _, hinf₀, hred₀, _, _⟩ :=
          constantValCheckJ_of_scoped (c := cS) (Γ := fun _ => default) hvs_j hv_m144
            (hlbd_ctors c_j hc_mem) (hfv_ctors c_j hc_mem)
            (hfresh_ctors c_j hc_mem) (hbasis_ctors c_j hc_mem) (hshape_ctors c_j hc_mem)
            hstore₁ hpos_lift ev_ws (e_ws.trans e_nil)
            (hrc.mono e_to_es) hty_nil hef₁ loads hg_es ev_es
        rw [hlps_cj, posOf_range] at hinf₀
        have hfv_ca : cvCa₀.type.hasFvar = false :=
          annotates_hasFvar_false hvs_j.2.2 (hfv_ctors c_j hc_mem)
        have hnp_ca : noProjAt T cvCa₀.type = true :=
          noProjAt_of_infer_full hno_proj_T hinf₀ hfv_ca
        have e_es := ev_es.heap_extends
        have e_saf := ev_saf.heap_extends
        have e_to_pa := e_to_es.trans (e_es.trans e_saf)
        have hcty_raw_m34 :
            RawTmExact (keyOf cS.t) 0 (fun _ => default) m34 0
              (ctorRawTypes.getD j default) cvCa₀.type xcty := by
          have h0 := hraw_rep 0 (fun _ => default)
          rwa [hlps_cj, posOf_range] at h0
        have hcty_exact_m34 : TmExact cS.κ 0 (fun _ => default) m34 0 cvCa₀.type xcty := by
          have h0 := hv_rep.2.2.2 0 (fun _ => default)
          rwa [hlps_cj, posOf_range] at h0
        have hcty_pa : Tm cS.κ 0 (fun _ => default) m400 0 cvCa₀.type xcty :=
          (hcty_exact_m34.mono (e_aeq.trans (e_ws.trans (e_nil.trans (e_es.trans e_saf))))).toTm
        have hdoms_sh : StructDomsShared cS.env ta cvCa₀.type nP :=
          check_param_agreement_staged_spec (c := cS) (by omega) (hrc.mono e_to_pa) hef₁ loads
            hg_pa (hta.mono e_to_pa) hcty_pa ev_pa
        have e_pa := ev_pa.heap_extends
        have e_from_m34_to_m430 :=
          e_aeq.trans (e_ws.trans (e_nil.trans (e_es.trans (e_saf.trans e_pa))))
        have e_to_rt := e_cprj.trans e_from_m34_to_m430
        rw [hnf_f] at ev_rt
        obtain ⟨hnt_476, rcbs, rargs, cbs, es, hstR_c, hrcbs_len, hstrip_c, hcbs_len,
            hes_len, hes_noT⟩ :=
          check_ctor_return_type_observed_spec (c := Ingress.traceRecordCtx cS.toCtx cs_root)
            hlps hlps_lt (by omega) (by omega) hpeer₁ rawFacts
            hg_rt (Ingress.traceRecordCtx_coverage cS.toCtx (fun x hx => hsub x (by simp [hc, hx])))
            (hcty_raw_m34.mono e_from_m34_to_m430) hnp_ca
            (Bytes.repAddressRef_heapMono₂ addrTy e_to_rt hbp) ev_rt
        obtain ⟨fvsP, crest, xFvs, idxArgs, hopP, hopF, hopAll, hidx_len⟩ :=
          ctor_openPis_residual hstrip_c hes_len
        have hres_ca : cvCa₀.type.constsResolve cS.env = true := by
          obtain ⟨ty', ⟨_, _, _, _, _, _, _, _, hcr, _⟩, hcv⟩ := hcvC_chk
          have hty_eq : cvCa₀.type = ty' := by rw [hcv]
          rwa [hty_eq]
        obtain ⟨hfvs_res, happ_res⟩ := openPisAtFvars_constsResolve (nP + c_j.2) hres_ca hopAll
        have hxFvs_res : ∀ x ∈ xFvs, x.fvarTypeD.constsResolve cS.env = true :=
          fun x hx => hfvs_res x (List.mem_append_right _ hx)
        have hidx_res : ∀ e ∈ idxArgs, e.constsResolve cS.env = true := by
          intro e he
          have hga_res := (constsResolve_getApp happ_res).2
          rw [getAppArgs_mkAppN_const] at hga_res
          exact hga_res e (List.mem_append_right _ he)
        have e_rt := ev_rt.heap_extends
        have e_from_m34_to_m476 := e_from_m34_to_m430.trans e_rt
        have e_to_fu := e_cprj.trans e_from_m34_to_m476
        obtain ⟨sorts_j, hfsorts_j, hchk_j⟩ : ∃ sorts_j : List KLevel,
            FieldSortsJ rulesJ cS.env (Level.isEquiv resSort .zero == some true) false resSort
              nP xFvs idxArgs c_j.2 sorts_j ∧
            (ctors.length = 1 → nIdx = 0 → (∀ φ : LevelParam → Nat, Level.eval φ ind_lvl = 0) →
              GuardData.CheckedFieldsAt cS cs_root b₀ indIndex nP c_j.2 cvCa₀.type ind_lvl
                sorts_j) := by
          by_cases hsl : ctors.length = 1 ∧ nIdx = 0 ∧
              ∀ φ : LevelParam → Nat, Level.eval φ ind_lvl = 0
          · -- a structure-like proposition: the sorts the classifier's field loop checked
            obtain ⟨hlen1, hidx0, hzero⟩ := hsl
            have hj0 : j = 0 := by omega
            have e_fu' := ev_fu.heap_extends
            have hg_prop : CoreGood cS cs_prop :=
              CoreGood.ofRaw (hgood.sub (fun x hx => by simp [hc, hx])) (fun call _ => hall call)
            have hg_cprj : CoreGood cS cs_cprj :=
              CoreGood.ofRaw (hgood.sub (fun x hx => by simp [hc, hx])) (fun call _ => hall call)
            have hnPv : ZMod.val ((nP : Nat) : F) = nP :=
              ZMod.val_natCast_of_lt (by unfold Aiur.Library.U32.Goldilocks.modulus; omega)
            have hnFv : ZMod.val ((c_j.2 : Nat) : F) = c_j.2 :=
              ZMod.val_natCast_of_lt (by unfold Aiur.Library.U32.Goldilocks.modulus; omega)
            have ev_prop' := ev_prop
            rw [hlen1, hidx0, Nat.cast_one, Nat.cast_zero, hnf_f] at ev_prop'
            have ev_cprj' := ev_cprj
            rw [hj0, Nat.cast_zero] at ev_cprj'
            obtain ⟨sorts, hsorted, hchecked⟩ :=
              GuardData.checkedFieldsAt_of_run (c := cS) ⟨hef₁, loads⟩ (calls := cs_root)
                hnPv hnFv hopP hopF hg_prop (hrc.mono (e_to_fu.trans e_fu'))
                (hcty_exact_m34.mono (e_from_m34_to_m476.trans e_fu')).toTm
                (repKLevel_heapMono₂ (e_to_fu.trans e_fu') hpind) hzero ev_prop'
                ev_cprj' hg_cprj hbp ld_c' (e_from_m34_to_m476.trans e_fu')
                (fun x hx => hsub x (by simp [hc, hx])) hsub_cprj
            have hisProp : (Level.isEquiv resSort .zero == some true) = true :=
              isEquiv_zero_of_eval_zero (fun φ => (hlveq φ).trans (hzero φ))
            obtain ⟨hlenS, hfieldsS⟩ := hsorted
            refine ⟨sorts, ⟨hlenS, fun i hi => ?_⟩, fun _ _ _ => hchecked⟩
            obtain ⟨fv, ty, v, hfv, hv, hinf, hred, -, -⟩ := hfieldsS i hi
            exact ⟨fv, ty, v, hfv, hv, hinf, hred,
              (fun hfalse => by rw [hisProp] at hfalse; exact nomatch hfalse),
              (fun _ hlarge => nomatch hlarge)⟩
          · obtain ⟨sorts_j, hfsorts_j⟩ :=
              check_field_universes_staged_spec hLevels (c := cS) (by omega) hlveq hinf₀ hopP
                hopF hopAll (hrc.mono e_to_fu) hef₁ loads hg_fu
                (repKLevel_heapMono₂ e_to_fu hpind)
                (hcty_exact_m34.mono e_from_m34_to_m476).toTm hnt_476 ev_fu
            exact ⟨sorts_j, hfsorts_j, fun h1 h2 h3 => absurd ⟨h1, h2, h3⟩ hsl⟩
        have e_fu := ev_fu.heap_extends
        have e_from_m34_to_m546 := (e_from_m34_to_m476.trans e_fu).trans ev_prop.heap_extends
        have e_to_pos := e_cprj.trans e_from_m34_to_m546
        have hpos_ext :
            (∀ i < c_j.2,
              (Ix.Kernel.recFieldKind T lps nP nIdx i (cbs.getD (nP + i) default).1 ≠ .negative ∧
               Ix.Kernel.recFieldKind T lps nP nIdx i (cbs.getD (nP + i) default).1 ≠
                .unsupported) ∧
              ((cbs.getD (nP + i) default).1.mentionsConst T = false ∨
               RawRecSpine T (rcbs.getD (nP + i) default).1 (cbs.getD (nP + i) default).1)) ∧
            Heap.Extends m_prop m646 := by
          cases sg_pos with
          | other hne _ _ _ => exact absurd rfl hne
          | n0 cs_pos _ ev_pos hc_sg =>
            have hg_pos : Good cS.toCtx cs_pos :=
              hgood.sub (fun x hx => by simp [hc, hc_sg, hx])
            exact ⟨check_positivity_observed_spec (c := Ingress.traceRecordCtx cS.toCtx cs_root)
              hlps hlps_lt (by omega) (by omega) hpeer₁
              rawFacts hg_pos
              (Ingress.traceRecordCtx_coverage cS.toCtx
                (fun x hx => hsub x (by simp [hc, hc_sg, hx])))
              (hcty_raw_m34.mono e_from_m34_to_m546) hnp_ca hstR_c hstrip_c
              (Bytes.repAddressRef_heapMono₂ addrTy e_to_pos hbp) ev_pos,
              ev_pos.heap_extends⟩
        refine ⟨sorts_j :: sortss_rest, by simp [hlen_rest], fun t_idx ht => ?_⟩
        cases t_idx with
        | zero =>
          rw [Nat.add_zero]
          exact ⟨c_j, (cvCa₀, c_j.2), sorts_j, hc_j, hcA_j, rfl,
            { nF_eq := rfl
              stored := hvs_j
              cvCheck := hcvC_chk
              noProj := hnp_ca
              inferSort := ⟨sty₀, u₀, hinf₀, hred₀⟩
              residual := ⟨rcbs, rargs, cbs, es, hstR_c, hrcbs_len, hstrip_c, hcbs_len,
                hes_len, hes_noT, (fun i hi => (hpos_ext.1 i hi).1),
                (fun i hi => (hpos_ext.1 i hi).2)⟩
              domsShared := hdoms_sh
              opened := ⟨fvsP, crest, xFvs, idxArgs, hopP, hopF, hidx_len,
                hxFvs_res, hidx_res, hfsorts_j⟩ }, hchk_j⟩
        | succ t' =>
          obtain ⟨c', cA', sorts', hc', hcA', hs', hout'⟩ := hrest_out t' (by omega)
          rw [show j + 1 + t' = j + (t' + 1) by omega] at hc' hcA' hout'
          exact ⟨c', cA', sorts', hc', hcA', hs', hout'⟩

/-- **The whole constructor loop at the constructor stage**, from its first slot, with the run
data of the classifier's field loop at a structure-like proposition. -/
theorem native_ctor_staged_checked (hLevels : IxVM.Consistency.Levels)
    {cS : ScopedCtx} (hall : ∀ call, cS.allowed call) {indIndex : F}
    {b₀ : Bytes.Address} {T : KKey} {lps : List LevelParam}
    {nP nIdx : Nat} {ta : KExpr} {resSort ind_lvl : KLevel}
    {cs_root : List (Call F)} {ctors ctorsA : List (KConstantVal × Nat)}
    {ctorRawTypes : List KExpr}
    (hlps : lps = List.range lps.length)
    (hlps_lt : lps.length < 4294967296)
    (hnP_lt : nP < 72057594037927936)
    (hnIdx_lt : nIdx < 72057594037927936)
    (hnCtors_lt : ctors.length < 549755813888)
    (hnF_lt : ∀ c ∈ ctors, c.2 < 72057594037927936)
    (hlveq : LvEq resSort ind_lvl)
    (hcload : StagedCtorLoads cS.κ cS.t b₀ nP indIndex cs_root ctors ctorsA ctorRawTypes)
    (hlps_ctors : ∀ c ∈ ctors, c.1.levelParams = lps)
    (hlbd_ctors : ∀ c ∈ ctors, c.1.type.looseBVarsBounded 0 = true)
    (hfv_ctors : ∀ c ∈ ctors, c.1.type.hasFvar = false)
    (hfresh_ctors : ∀ c ∈ ctors, cS.env.find? c.1.name = none)
    (hbasis_ctors : ∀ c ∈ ctors, Ix.Kernel.reservedBasisNames.contains c.1.name = false)
    (hshape_ctors : ∀ c ∈ ctors, c.1.name.isProjFnShape = false)
    (hno_proj_T : ∀ i, cS.env.findProj? T i = none)
    (hstore₁ : Ix.Kernel.Open.StoreInv cS.env)
    (hef₁ : CoreEnvFacts cS.toCtx)
    (loads : ScopedLoadFacts cS)
    (rawFacts : RawRecordFacts (Ingress.traceRecordCtx cS.toCtx cs_root))
    (hpeer₁ : OneTypePeerReads (Ingress.traceRecordCtx cS.toCtx cs_root) b₀ T lps.length nP nIdx
      ctors.length indIndex)
    {rc pta bp pind r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (subset : ∀ call ∈ cs, call ∈ cs_root) (good : Good cS.toCtx cs)
    (roleContext : RCRep cS.t cS.lim h rc)
    (formerRep : Tm cS.κ 0 (fun _ => default) h 0 ta pta)
    (blockRep : Bytes.RepAddressRef addrTy h b₀ bp)
    (sortRep : RepKLevel h ind_lvl pind)
    (observed : ObsFn W "KernelCheck::check_inductive_shape_ctors"
      [rc, pta, .field (nP : F), .field (nIdx : F), .field (ctors.length : F),
        .field (lps.length : F), bp, .field indIndex, pind, .field 0, .field 0] h r h' cs) :
    ∃ sortss : List (List KLevel),
      sortss.length = ctors.length ∧
      ∀ j < ctors.length, ∃ c cA sorts,
        ctors[j]? = some c ∧ ctorsA[j]? = some cA ∧ sortss[j]? = some sorts ∧
        NativeCtorOut cS.env T lps nP nIdx resSort ta
          (ctorRawTypes.getD j default) c cA sorts ∧
        (ctors.length = 1 → nIdx = 0 → (∀ φ : LevelParam → Nat, Level.eval φ ind_lvl = 0) →
          GuardData.CheckedFieldsAt cS cs_root b₀ indIndex nP c.2 cA.1.type ind_lvl sorts) := by
  simpa only [Nat.zero_add] using
    native_ctor_staged_runs_checked hLevels hall hlps hlps_lt hnP_lt hnIdx_lt hnCtors_lt hnF_lt hlveq
      hcload hlps_ctors hlbd_ctors hfv_ctors hfresh_ctors hbasis_ctors hshape_ctors hno_proj_T
      hstore₁ hef₁ loads rawFacts hpeer₁ ctors.length 0 (Nat.add_zero _) subset good roleContext
      formerRep blockRep sortRep observed

/-- **The whole constructor loop at the constructor stage**, from its first slot. -/
theorem native_ctor_staged (hLevels : IxVM.Consistency.Levels)
    {cS : ScopedCtx} (hall : ∀ call, cS.allowed call) {indIndex : F}
    {b₀ : Bytes.Address} {T : KKey} {lps : List LevelParam}
    {nP nIdx : Nat} {ta : KExpr} {resSort ind_lvl : KLevel}
    {cs_root : List (Call F)} {ctors ctorsA : List (KConstantVal × Nat)}
    {ctorRawTypes : List KExpr}
    (hlps : lps = List.range lps.length)
    (hlps_lt : lps.length < 4294967296)
    (hnP_lt : nP < 72057594037927936)
    (hnIdx_lt : nIdx < 72057594037927936)
    (hnCtors_lt : ctors.length < 549755813888)
    (hnF_lt : ∀ c ∈ ctors, c.2 < 72057594037927936)
    (hlveq : LvEq resSort ind_lvl)
    (hcload : StagedCtorLoads cS.κ cS.t b₀ nP indIndex cs_root ctors ctorsA ctorRawTypes)
    (hlps_ctors : ∀ c ∈ ctors, c.1.levelParams = lps)
    (hlbd_ctors : ∀ c ∈ ctors, c.1.type.looseBVarsBounded 0 = true)
    (hfv_ctors : ∀ c ∈ ctors, c.1.type.hasFvar = false)
    (hfresh_ctors : ∀ c ∈ ctors, cS.env.find? c.1.name = none)
    (hbasis_ctors : ∀ c ∈ ctors, Ix.Kernel.reservedBasisNames.contains c.1.name = false)
    (hshape_ctors : ∀ c ∈ ctors, c.1.name.isProjFnShape = false)
    (hno_proj_T : ∀ i, cS.env.findProj? T i = none)
    (hstore₁ : Ix.Kernel.Open.StoreInv cS.env)
    (hef₁ : CoreEnvFacts cS.toCtx)
    (loads : ScopedLoadFacts cS)
    (rawFacts : RawRecordFacts (Ingress.traceRecordCtx cS.toCtx cs_root))
    (hpeer₁ : OneTypePeerReads (Ingress.traceRecordCtx cS.toCtx cs_root) b₀ T lps.length nP nIdx
      ctors.length indIndex)
    {rc pta bp pind r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (subset : ∀ call ∈ cs, call ∈ cs_root) (good : Good cS.toCtx cs)
    (roleContext : RCRep cS.t cS.lim h rc)
    (formerRep : Tm cS.κ 0 (fun _ => default) h 0 ta pta)
    (blockRep : Bytes.RepAddressRef addrTy h b₀ bp)
    (sortRep : RepKLevel h ind_lvl pind)
    (observed : ObsFn W "KernelCheck::check_inductive_shape_ctors"
      [rc, pta, .field (nP : F), .field (nIdx : F), .field (ctors.length : F),
        .field (lps.length : F), bp, .field indIndex, pind, .field 0, .field 0] h r h' cs) :
    ∃ sortss : List (List KLevel),
      sortss.length = ctors.length ∧
      ∀ j < ctors.length, ∃ c cA sorts,
        ctors[j]? = some c ∧ ctorsA[j]? = some cA ∧ sortss[j]? = some sorts ∧
        NativeCtorOut cS.env T lps nP nIdx resSort ta
          (ctorRawTypes.getD j default) c cA sorts := by
  obtain ⟨sortss, hlen, hout⟩ := native_ctor_staged_checked hLevels hall hlps hlps_lt hnP_lt hnIdx_lt hnCtors_lt hnF_lt hlveq
      hcload hlps_ctors hlbd_ctors hfv_ctors hfresh_ctors hbasis_ctors hshape_ctors hno_proj_T
      hstore₁ hef₁ loads rawFacts hpeer₁ subset good
    roleContext formerRep blockRep sortRep observed
  refine ⟨sortss, hlen, fun j hj => ?_⟩
  obtain ⟨c, cA, sorts, hc, hcA, hs, ho, -⟩ := hout j hj
  exact ⟨c, cA, sorts, hc, hcA, hs, ho⟩

end IxVM.Refinement.Decl
