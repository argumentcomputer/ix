import IxVMRefinement.Decl.NativeFront
import IxVMRefinement.Core.CallHeaps

/-! # Scoped semantic checks for native constructors

The successful traversal selects its concrete sort, parameter-agreement, and field-sort
sub-observations. Semantic loads are required only for children of those selected runs;
raw return and positivity queries use their separate record scope.
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

/-- One actual typed helper invocation selected from the constructor traversal. -/
structure NativeCtorCoreRun (rootCalls : List (Call F)) where
  name : String
  args : List (SourceValue F)
  before : Heap F
  result : SourceValue F
  after : Heap F
  calls : List (Call F)
  kind : name = "KernelInfer::k_ensure_sort" ∨
    name = "KernelCheck::check_param_agreement" ∨ name = "KernelCheck::check_field_universes"
  observed : ObsFn W name args before result after calls
  member : (⟨name, args, before⟩ : Call F) ∈ rootCalls
  subset : ∀ call ∈ calls, call ∈ rootCalls

/-- The selected scope contains the children of the actual typed runs. -/
def nativeCtorCoreCalls {rootCalls : List (Call F)}
    (runs : List (NativeCtorCoreRun rootCalls)) : List (Call F) :=
  runs.flatMap (·.calls)

/-- The exact finite scope produced by the selected typed observations. -/
def nativeCtorCoreCtx (base : Ctx) {rootCalls : List (Call F)}
    (runs : List (NativeCtorCoreRun rootCalls)) : ScopedCtx :=
  { toCtx := base, allowed := fun call => call ∈ nativeCtorCoreCalls runs }

/-- Each selected run has core coverage in the produced context. -/
theorem NativeCtorCoreRun.coreGood {base : Ctx} {rootCalls : List (Call F)}
    {runs : List (NativeCtorCoreRun rootCalls)} {run : NativeCtorCoreRun rootCalls}
    (good : Good base rootCalls) (member : run ∈ runs) :
    CoreGood (nativeCtorCoreCtx base runs) run.calls :=
  CoreGood.ofRaw (good.sub run.subset)
    (fun _call inside => List.mem_flatMap.mpr ⟨run, member, inside⟩)

/-- Every selected call belongs to the original successful traversal. -/
theorem nativeCtorCoreCalls_subset {rootCalls : List (Call F)}
    (runs : List (NativeCtorCoreRun rootCalls)) :
    ∀ call ∈ nativeCtorCoreCalls runs, call ∈ rootCalls := by
  intro call member
  obtain ⟨run, _, inside⟩ := List.mem_flatMap.mp member
  exact run.subset call inside

/-- Child coverage in the produced scope locates every read back in the actual root trace. -/
theorem nativeCtorCoreCtx_child_subset {base : Ctx} {rootCalls calls : List (Call F)}
    {runs : List (NativeCtorCoreRun rootCalls)}
    (good : CoreGood (nativeCtorCoreCtx base runs) calls) :
    ∀ call ∈ calls, call ∈ rootCalls :=
  fun call member => nativeCtorCoreCalls_subset runs call (good.allAllowed call member)

/-- A fresh constructor read in the actual typed scope is supplied by the produced raw
family. Both the permitted top invocation and coverage of its children remain explicit. -/
theorem CtorLoadAtIndex.scoped_fresh_read {base : Ctx} {block : Bytes.Address}
    {indIndex : F} {params slot : Nat} {rootCalls : List (Call F)}
    {runs : List (NativeCtorCoreRun rootCalls)}
    {ctors ctorsA : List (KConstantVal × Nat)} {rawTypes : List KExpr}
    {bp ptr : SourceValue F} {h h' : Heap F} {calls : List (Call F)}
    (family : CtorLoadAtIndex base.t block params indIndex rootCalls ctors ctorsA rawTypes)
    (slotBound : slot < ctors.length)
    (_allowed : (nativeCtorCoreCtx base runs).allowedTop "Ingress::get_ci_cprj"
      [bp, .field indIndex, .field (slot : F)] h)
    (good : CoreGood (nativeCtorCoreCtx base runs) calls)
    (blockRep : Bytes.RepAddressRef addrTy h block bp)
    (observed : ObsFn W "Ingress::get_ci_cprj" [bp, .field indIndex, .field (slot : F)]
      h ptr h' calls)
    (fresh : base.env.find? (base.κ
      (cprjAddr (ixAddr block) (ZMod.val indIndex) (ZMod.val (slot : F)))) = none) :
    (∃ ci, CIPtrRep base.κ h' ptr ci) ∧
      ∀ ci, base.env.find? (base.κ
        (cprjAddr (ixAddr block) (ZMod.val indIndex) (ZMod.val (slot : F)))) = some ci →
        CIPtrRep base.κ h' ptr ci :=
  family.fresh_read (c := nativeCtorCoreCtx base runs) slotBound
    (nativeCtorCoreCtx_child_subset good) blockRep observed fresh

/-- Build the finite typed-call scope while refining the actual constructor loop. The
remaining load premise is explicitly restricted to that scope by the caller; base semantic
facts and raw metadata facts retain their separate obligations. -/
theorem native_ctor_scoped_runs (hLevels : IxVM.Consistency.Levels)
    {cR : ScopedCtx} {indIndex : F}
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
    (hcload : CtorLoadAtIndex cR.t b₀ nP indIndex cs_root ctors ctorsA ctorRawTypes)
    (hlps_ctors : ∀ c ∈ ctors, c.1.levelParams = lps)
    (hlbd_ctors : ∀ c ∈ ctors, c.1.type.looseBVarsBounded 0 = true)
    (hfv_ctors : ∀ c ∈ ctors, c.1.type.hasFvar = false)
    (hfresh_ctors : ∀ c ∈ ctors, cR.env.find? c.1.name = none)
    (hbasis_ctors : ∀ c ∈ ctors, Ix.Kernel.reservedBasisNames.contains c.1.name = false)
    (hshape_ctors : ∀ c ∈ ctors, c.1.name.isProjFnShape = false)
    (hno_proj_T : ∀ i, cR.env.findProj? T i = none)
    (hstore₁ : Ix.Kernel.Open.StoreInv cR.env)
    (hef₁ : CoreEnvFacts cR.toCtx)
    (rawFacts : RawRecordFacts cR)
    (hpeer₁ : OneTypePeerReads cR b₀ T lps.length nP nIdx ctors.length indIndex) :
    ∀ (m j : Nat) {rc pta bp pind r : SourceValue F} {h h' : Heap F} {cs : List (Call F)},
      m + j = ctors.length →
      (∀ x ∈ cs, x ∈ cs_root) →
      Good cR.toCtx cs →
      RawRecordCoverage cR cs →
      RCRep cR.t cR.lim h rc →
      Tm cR.κ 0 (fun _ => default) h 0 ta pta →
      Bytes.RepAddressRef addrTy h b₀ bp →
      RepKLevel h ind_lvl pind →
      ObsFn W "KernelCheck::check_inductive_shape_ctors"
        [rc, pta, .field (nP : F), .field (nIdx : F), .field (ctors.length : F),
          .field (lps.length : F), bp, .field indIndex, pind, .field 0, .field (j : F)] h r h' cs →
      ∃ runs : List (NativeCtorCoreRun cs_root),
        ∀ allowed : Call F → Prop,
          (∀ call ∈ nativeCtorCoreCalls runs, allowed call) →
          ScopedLoadFacts { toCtx := cR.toCtx, allowed := allowed } →
      ∃ sortss_suf : List (List KLevel),
        sortss_suf.length = m ∧
        ∀ t_idx < m, ∃ c cA sorts,
          ctors[j + t_idx]? = some c ∧
          ctorsA[j + t_idx]? = some cA ∧
          sortss_suf[t_idx]? = some sorts ∧
          NativeCtorOut cR.env T lps nP nIdx resSort ta
            (ctorRawTypes.getD (j + t_idx) default) c cA sorts
  | 0, j, _, _, _, _, _, _, _, _, hmj, _, _, _, _, _, _, _, ev => by
    match Obs.«KernelCheck::check_inductive_shape_ctors».obs ev with
    | .n0 .. =>
      exact ⟨[], fun _ _ _ => ⟨[], rfl, fun _ ht => absurd ht (Nat.not_lt_zero _)⟩⟩
    | .other (op17 := op) (hne29 := hne) .. =>
      have hj_eq : j = ctors.length := by omega
      cases hj_eq.symm
      rw [evalBinOp_sub_nat (Nat.le_refl ctors.length) op, Nat.sub_self] at hne
      exact absurd rfl hne
  | m + 1, j, rc, pta, bp, pind, r, h, h', cs, hmj, hsub, hgood, rawCovered, hrc, hta, hbp, hpind, ev => by
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
        (m646 := m646) (m655 := m655) (cs648 := cs_sg) (cs695 := cs_rec) (v708 := v670)
        (ev49 := ev_cprj) (ld43 := ld_ctor) (ev154 := ev_aeq)
        (heq261 := heq_nl) (heq289 := heq_np)
        (ev331 := ev_ws) (hm395 := hm387) (ev368 := ev_es) (ev412 := ev_saf)
        (ev442 := ev_pa) (ev488 := ev_rt) (ev558 := ev_fu) (sg653 := sg_pos)
        (op792 := op_add) (ev697 := ev_rec) (hc794 := hc) .. =>
      have indexEq := evalBinOp_add_nat j 1 op_add
      subst v670
      have recurseMember : (⟨"KernelCheck::check_inductive_shape_ctors",
          [rc, pta, .field (nP : F), .field (nIdx : F), .field (ctors.length : F),
            .field (lps.length : F), bp, .field indIndex, pind, .field 0,
            .field ((j + 1 : Nat) : F)], m655⟩ : Call F) ∈ cs := by
        simp [hc]
      have e_to_rec := (ev.call_heap_bounds recurseMember).1
      have hg_rec : Good cR.toCtx cs_rec := hgood.sub (fun x hx => by simp [hc, hx])
      obtain ⟨restRuns, restSemantic⟩ :=
        native_ctor_scoped_runs hLevels hlps hlps_lt hnP_lt hnIdx_lt hnCtors_lt
          hnF_lt hlveq hcload hlps_ctors hlbd_ctors hfv_ctors hfresh_ctors hbasis_ctors
          hshape_ctors hno_proj_T hstore₁ hef₁ rawFacts hpeer₁
          m (j + 1) (by omega) (fun x hx => hsub x (by simp [hc, hx])) hg_rec
          (rawCovered.sub (fun x hx => by simp [hc, hx]))
          (hrc.mono e_to_rec) (hta.mono e_to_rec)
          (Bytes.repAddressRef_heapMono₂ addrTy e_to_rec hbp)
          (repKLevel_heapMono₂ e_to_rec hpind) ev_rec
      let sortRun : NativeCtorCoreRun cs_root := {
        name := _, args := _, before := _, result := _, after := _, calls := cs_es
        kind := Or.inl rfl, observed := ev_es
        member := hsub _ (by simp [hc])
        subset := fun call member => hsub call (by simp [hc, member]) }
      let paramRun : NativeCtorCoreRun cs_root := {
        name := _, args := _, before := _, result := _, after := _, calls := cs_pa
        kind := Or.inr (Or.inl rfl), observed := ev_pa
        member := hsub _ (by simp [hc])
        subset := fun call member => hsub call (by simp [hc, member]) }
      let fieldRun : NativeCtorCoreRun cs_root := {
        name := _, args := _, before := _, result := _, after := _, calls := cs_fu
        kind := Or.inr (Or.inr rfl), observed := ev_fu
        member := hsub _ (by simp [hc])
        subset := fun call member => hsub call (by simp [hc, member]) }
      refine ⟨sortRun :: paramRun :: fieldRun :: restRuns, ?_⟩
      intro allowed covered loads
      let cC : ScopedCtx := { toCtx := cR.toCtx, allowed := allowed }
      have restAllowed : ∀ call ∈ nativeCtorCoreCalls restRuns, allowed call := by
        intro call member
        apply covered call
        simp only [nativeCtorCoreCalls, List.flatMap_cons, List.mem_append]
        exact Or.inr (Or.inr (Or.inr member))
      obtain ⟨sortss_rest, hlen_rest, hrest_out⟩ := restSemantic allowed restAllowed loads
      obtain ⟨c_j, cvCa₀, hc_j, hcA_j, hvs_j, hload_j⟩ := hcload.2 j (by omega)
      have hc_mem : c_j ∈ ctors := List.mem_of_getElem? hc_j
      have hc_nf_lt : c_j.2 < 72057594037927936 := hnF_lt c_j hc_mem
      have hsub_cprj : ∀ x ∈ cs_cprj, x ∈ cs_root := fun x hx => hsub x (by simp [hc, hx])
      obtain ⟨nl', cty', cblk', cnp', cnf', _, ld_c', _, _, hraw_rep, hci_rep⟩ :=
        hload_j bp p41 h m34 cs_cprj hsub_cprj hbp ev_cprj
      rw [ld_c'] at ld_ctor
      injection ld_ctor with hval; injection hval with _ _ h1
      injection h1 with hnl_eq h1; injection h1 with hcty_eq h1; injection h1 with hcblk_eq h1
      injection h1 with _ h1; injection h1 with _ h1; injection h1 with hcnp_eq h1
      injection h1 with hcnf_eq _
      cases hnl_eq.symm; cases hcty_eq.symm; cases hcblk_eq.symm
      cases hcnp_eq.symm; cases hcnf_eq.symm
      obtain ⟨hv_rep, hnp_f, hnf_f⟩ := CIRepExact.ctor_inv hci_rep
      · subst heq_nl heq_np
        have e_cprj := ev_cprj.heap_extends
        have e_aeq := ev_aeq.heap_extends
        have e_ws := ev_ws.heap_extends
        have e_nil : Heap.Extends m319 m387 := by rw [hm387]; exact Heap.Extends.snoc m319 _
        have e_to_es := e_cprj.trans (e_aeq.trans (e_ws.trans e_nil))
        have hg_es : CoreGood cC cs_es :=
          CoreGood.ofRaw (hgood.sub (fun x hx => by simp [hc, hx]))
            (fun call member => covered call (by simp [nativeCtorCoreCalls, sortRun, member]))
        have hg_pa : CoreGood cC cs_pa :=
          CoreGood.ofRaw (hgood.sub (fun x hx => by simp [hc, hx]))
            (fun call member => covered call (by simp [nativeCtorCoreCalls, paramRun, member]))
        have hg_rt : Good cR.toCtx cs_rt := hgood.sub (fun x hx => by simp [hc, hx])
        have hg_fu : CoreGood cC cs_fu :=
          CoreGood.ofRaw (hgood.sub (fun x hx => by simp [hc, hx]))
            (fun call member => covered call (by simp [nativeCtorCoreCalls, fieldRun, member]))
        have hlps_cj : cvCa₀.levelParams = List.range lps.length := by
          rw [hvs_j.2.1, hlps_ctors c_j hc_mem]
          exact hlps
        have hpos_lift : PosSortLift cR.env cvCa₀ := PosSortLift.of_range hlps_cj
        have hv_m144 : ValRepExact cR.κ m144 (.field (lps.length : F)) xcty cvCa₀ :=
          ⟨hv_rep.1, hv_rep.2.1, hv_rep.2.2.1, hv_rep.2.2.2.mono e_aeq⟩
        have hty_nil : TypesRep cR.κ (fun _ => default) m387 0
            (.ptr (.enum kexprListEnum) m319.length) := by
          rw [hm387]; exact typesRep_alloc_nil cR.κ (fun _ => default) m319
        obtain ⟨hcvC_chk, sty₀, u₀, _, hinf₀, hred₀, _, _⟩ :=
          constantValCheckJ_of_scoped (c := cC) (Γ := fun _ => default) hvs_j hv_m144
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
            RawTmExact cR.κ 0 (fun _ => default) m34 0
              (ctorRawTypes.getD j default) cvCa₀.type xcty := by
          have h0 := hraw_rep 0 (fun _ => default)
          rwa [hlps_cj, posOf_range] at h0
        have hcty_exact_m34 : TmExact cR.κ 0 (fun _ => default) m34 0 cvCa₀.type xcty :=
          hcty_raw_m34.toTmExact
        have hcty_pa : Tm cR.κ 0 (fun _ => default) m400 0 cvCa₀.type xcty :=
          (hcty_exact_m34.mono (e_aeq.trans (e_ws.trans (e_nil.trans (e_es.trans e_saf))))).toTm
        have hdoms_sh : StructDomsShared cR.env ta cvCa₀.type nP :=
          check_param_agreement_scoped_spec (c := cC) (by omega) (hrc.mono e_to_pa) hef₁ loads hg_pa
            (hta.mono e_to_pa) hcty_pa ev_pa
        have e_pa := ev_pa.heap_extends
        have e_from_m34_to_m430 :=
          e_aeq.trans (e_ws.trans (e_nil.trans (e_es.trans (e_saf.trans e_pa))))
        have e_to_rt := e_cprj.trans e_from_m34_to_m430
        rw [hnf_f] at ev_rt
        obtain ⟨hnt_476, rcbs, rargs, cbs, es, hstR_c, hrcbs_len, hstrip_c, hcbs_len,
            hes_len, hes_noT⟩ :=
          check_ctor_return_type_observed_spec hlps hlps_lt (by omega) (by omega) hpeer₁ rawFacts hg_rt
            (rawCovered.sub (fun x hx => by simp [hc, hx]))
            (hcty_raw_m34.mono e_from_m34_to_m430) hnp_ca
            (Bytes.repAddressRef_heapMono₂ addrTy e_to_rt hbp) ev_rt
        obtain ⟨fvsP, crest, xFvs, idxArgs, hopP, hopF, hopAll, hidx_len⟩ :=
          ctor_openPis_residual hstrip_c hes_len
        have hres_ca : cvCa₀.type.constsResolve cR.env = true := by
          obtain ⟨ty', ⟨_, _, _, _, _, _, _, _, hcr, _⟩, hcv⟩ := hcvC_chk
          have hty_eq : cvCa₀.type = ty' := by rw [hcv]
          rwa [hty_eq]
        obtain ⟨hfvs_res, happ_res⟩ := openPisAtFvars_constsResolve (nP + c_j.2) hres_ca hopAll
        have hxFvs_res : ∀ x ∈ xFvs, x.fvarTypeD.constsResolve cR.env = true :=
          fun x hx => hfvs_res x (List.mem_append_right _ hx)
        have hidx_res : ∀ e ∈ idxArgs, e.constsResolve cR.env = true := by
          intro e he
          have hga_res := (constsResolve_getApp happ_res).2
          rw [getAppArgs_mkAppN_const] at hga_res
          exact hga_res e (List.mem_append_right _ he)
        have e_rt := ev_rt.heap_extends
        have e_from_m34_to_m476 := e_from_m34_to_m430.trans e_rt
        have e_to_fu := e_cprj.trans e_from_m34_to_m476
        obtain ⟨sorts_j, hfsorts_j⟩ :=
          check_field_universes_scoped_spec hLevels (c := cC) (by omega) hlveq hinf₀ hopP hopF hopAll
            (hrc.mono e_to_fu) hef₁ loads hg_fu
            (repKLevel_heapMono₂ e_to_fu hpind)
            (hcty_exact_m34.mono e_from_m34_to_m476).toTm hnt_476 ev_fu
        have e_fu := ev_fu.heap_extends
        have e_from_m34_to_m546 := e_from_m34_to_m476.trans e_fu
        have e_to_pos := e_cprj.trans e_from_m34_to_m546
        have hpos_ext :
            (∀ i < c_j.2,
              (Ix.Kernel.recFieldKind T lps nP nIdx i (cbs.getD (nP + i) default).1 ≠ .negative ∧
               Ix.Kernel.recFieldKind T lps nP nIdx i (cbs.getD (nP + i) default).1 ≠ .unsupported) ∧
              ((cbs.getD (nP + i) default).1.mentionsConst T = false ∨
               RawRecSpine T (rcbs.getD (nP + i) default).1 (cbs.getD (nP + i) default).1)) ∧
            Heap.Extends m546 m646 := by
          cases sg_pos with
          | other hne _ _ _ => exact absurd rfl hne
          | n0 cs_pos _ ev_pos hc_sg =>
            have hg_pos : Good cR.toCtx cs_pos :=
              hgood.sub (fun x hx => by simp [hc, hc_sg, hx])
            exact ⟨check_positivity_observed_spec hlps hlps_lt (by omega) (by omega) hpeer₁ rawFacts hg_pos
              (rawCovered.sub (fun x hx => by simp [hc, hc_sg, hx]))
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
                hxFvs_res, hidx_res, hfsorts_j⟩ }⟩
        | succ t' =>
          obtain ⟨c', cA', sorts', hc', hcA', hs', hout'⟩ := hrest_out t' (by omega)
          rw [show j + 1 + t' = j + (t' + 1) by omega] at hc' hcA' hout'
          exact ⟨c', cA', sorts', hc', hcA', hs', hout'⟩

/-- The actual complete constructor traversal chooses its exact typed-call scope. No caller
coverage predicate or unrestricted load contract is needed. -/
theorem native_ctor_scoped (hLevels : IxVM.Consistency.Levels)
    {cR : ScopedCtx} {indIndex : F}
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
    (hcload : CtorLoadAtIndex cR.t b₀ nP indIndex cs_root ctors ctorsA ctorRawTypes)
    (hlps_ctors : ∀ c ∈ ctors, c.1.levelParams = lps)
    (hlbd_ctors : ∀ c ∈ ctors, c.1.type.looseBVarsBounded 0 = true)
    (hfv_ctors : ∀ c ∈ ctors, c.1.type.hasFvar = false)
    (hfresh_ctors : ∀ c ∈ ctors, cR.env.find? c.1.name = none)
    (hbasis_ctors : ∀ c ∈ ctors, Ix.Kernel.reservedBasisNames.contains c.1.name = false)
    (hshape_ctors : ∀ c ∈ ctors, c.1.name.isProjFnShape = false)
    (hno_proj_T : ∀ i, cR.env.findProj? T i = none)
    (hstore₁ : Ix.Kernel.Open.StoreInv cR.env)
    (hef₁ : CoreEnvFacts cR.toCtx)
    (rawFacts : RawRecordFacts cR)
    (hpeer₁ : OneTypePeerReads cR b₀ T lps.length nP nIdx ctors.length indIndex)
    {rc pta bp pind r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (subset : ∀ call ∈ cs, call ∈ cs_root)
    (good : Good cR.toCtx cs) (rawCovered : RawRecordCoverage cR cs)
    (roleContext : RCRep cR.t cR.lim h rc)
    (formerRep : Tm cR.κ 0 (fun _ => default) h 0 ta pta)
    (blockRep : Bytes.RepAddressRef addrTy h b₀ bp)
    (sortRep : RepKLevel h ind_lvl pind)
    (observed : ObsFn W "KernelCheck::check_inductive_shape_ctors"
      [rc, pta, .field (nP : F), .field (nIdx : F), .field (ctors.length : F),
        .field (lps.length : F), bp, .field indIndex, pind, .field 0, .field 0] h r h' cs) :
    ∃ runs : List (NativeCtorCoreRun cs_root),
      ScopedLoadFacts (nativeCtorCoreCtx cR.toCtx runs) →
      ∃ sortss : List (List KLevel),
        sortss.length = ctors.length ∧
        ∀ j < ctors.length, ∃ c cA sorts,
          ctors[j]? = some c ∧ ctorsA[j]? = some cA ∧ sortss[j]? = some sorts ∧
          NativeCtorOut cR.env T lps nP nIdx resSort ta
            (ctorRawTypes.getD j default) c cA sorts := by
  obtain ⟨runs, checked⟩ := native_ctor_scoped_runs hLevels hlps hlps_lt hnP_lt hnIdx_lt
    hnCtors_lt hnF_lt hlveq hcload hlps_ctors hlbd_ctors hfv_ctors hfresh_ctors
    hbasis_ctors hshape_ctors hno_proj_T hstore₁ hef₁ rawFacts hpeer₁ ctors.length 0
    (Nat.add_zero _) subset good rawCovered roleContext formerRep blockRep sortRep observed
  refine ⟨runs, fun loads => ?_⟩
  simpa only [Nat.zero_add] using
    checked (fun call => call ∈ nativeCtorCoreCalls runs) (fun _ member => member) loads


end IxVM.Refinement.Decl
