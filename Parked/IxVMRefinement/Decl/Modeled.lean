import IxVMRefinement.Decl.ModeledInstall
import IxVMRefinement.Obs.RBTreeMap
import IxVMRefinement.Obs.KernelCheck
import IxVMRefinement.Obs.KernelModeled

/-! # Modeled Inductive Block Dispatch & Top-Level `L5` Assembly (`Modeled.lean`)

Completes the modeled-inductive slice (`L5-M`) and joins it with `L5-V` (`Value.lean`,
`ModeledInstall.lean`) and the native-inductive seam (`NativeIndStep`) to discharge
`IxVM.Consistency.Decls.{u} S₀` and `IxVM.Consistency.L5.{u} S₀`:

1. **`AddrMapAll` & `RBTreeMap` insertion (`rbtree_map_insert_field_addrMapAll`)**: proves from
   the generated path lemmas for `rbtree_map_balance_fix`, `rbtree_map_balance`, `rbtree_map_ins`,
   and `rbtree_map_insert<Field>` that inserting `(a, 1)` into an `AddrMapAll` address set extends
   its membership predicate to `S · ∨ · = a`.
2. **Payload address streams, list operations, & `RenameMap` construction**: refines
   `KernelModeled::get_addrs`, `Lists::length<&[Field; 32]>`, `Lists::concat<&[Field; 32]>`,
   proves `ixAddr_injective` and `keyOf_injective`, and builds `RenameMap` for the 3-way
   concatenated `(types ++ ctors ++ recs) → (type_models ++ ctor_models ++ rec_models)` table.
3. **`KernelCheck::check_const` & `KernelModeled::check_family` component specs**:
   - `check_const_ind_inv`, `check_const_ctor_inv`, `check_const_rec_inv` (splitting safe unpinned
     inductive members cleanly into native `block_is_modeled = 0` vs modeled `block_is_modeled ≠ 0`),
   - `check_modeled_block_inv`, `check_family_seg1_inv`,
   - `check_advice_records_spec` (stepping `(env, seen)` along `advice` via `AdviceStepOracle` +
     `rbtree_map_insert_field_addrMapAll`),
   - `ci_lvls_type_spec`, `member_val_spec`, `members_val_spec` (matching every block member's
     signature against its advice `Defn` model via `ExactGetCI` + `rename_exact` +
     `kexpr_struct_eq_one`),
   - `check_recs_spec` (refining `KernelModeled::check_recs` across the recursor list via
     `validate_expr_well_scoped_spec`, `core_ensure_sort`, and `check_rules_vm_spec`).
4. **End-to-end `ModeledBlockWitness` assembly & `modeledIndDecl_step`**: walks
   `Obs.«KernelModeled::check_family».obs` end-to-end to construct `ModeledBlockWitness.{u}` and
   feeds it into `modeledBlock_install_step`.
5. **Top-level `Decls S₀` & `L5 S₀` theorems (`l5_decls_S₀`, `l5_S₀`)**: uses `DeclInvM` as the
   witness invariant `Inv`, combining `valueOrPinnedDecl_step_M`, `modeledIndDecl_step`, and
   `NativeIndStep` across all declarations. -/

/-! # Parked: the legacy modeled-inductive step of `Decl/Modeled.lean`

Moved out of `IxVMRefinement/Decl/Modeled.lean`, outside every library, unchanged:
`check_recs_spec`, `ModeledFamilyBridge`, `modeledBlockWitness_of_check_family`,
`DeclModeledExtraFacts`, `modeledIndDecl_step`, `DeclExtraFacts`, `AllDeclExtraFacts`,
`decl_step_S₀`, `l5_decls_S₀`, `l5_S₀`. They rest on the parked refinement of the rule loops
(`Parked/IxVMRefinement/Decl/ModeledRules.lean`: `check_rules_vm_spec`), which no longer follows
the program's rule typing on renamed terms, and on the family check's recursor loop before its
recursor-type assertion. The legacy top-level theorem `l5_S₀` goes with them. `NativeIndStep`
and the other helpers stay in the library. -/

namespace IxVM.Refinement.Decl

/-- **`KernelModeled::check_recs`** refines a list of `RawRecEntry`s into a matching list of
`RecInstallEntry`s carrying `RawIotaRulesVmRun` and telescope/pin decompositions. -/
theorem check_recs_spec
    (hCore : IxVM.Consistency.Core S₀) (hroles : RolesSpec) (hcallees : CalleesSpec)
    {c_pub c_rhs c_adv : Ctx}
    (ht_rhs : c_rhs.t = c_pub.t) (hlim_rhs : c_rhs.lim = c_pub.lim)
    (ht_eq : c_adv.t = c_pub.t) (hlim_eq : c_adv.lim = c_pub.lim)
    (hef_pub : EnvFacts c_pub) (hlf_pub : LoadFacts c_pub) (hexact_pub : ExactGetCI c_pub)
    (hef_rhs : EnvFacts c_rhs) (hlf_rhs : LoadFacts c_rhs)
    (hef_adv : EnvFacts c_adv) (hlf_adv : LoadFacts c_adv) (hexact_adv : ExactGetCI c_adv)
    {blockNames : List KKey} {f_id : KKey → KKey} {advSet : Bytes.Address → Prop}
    (hf_out : ∀ k, blockNames.contains k = false → f_id k = k)
    (hproj_rhs : ∀ sn i entry, c_rhs.env.findProj? sn i = some entry →
      blockNames.contains sn = false)
    (hnp_ctor : ∀ k cvj cnP cnF, c_pub.env.find? k = some (.ctorInfo cvj cnP cnF) →
      NoProjIn blockNames cvj.type = true) :
    ∀ (raws : List RawRecEntry)
      {x_rc x_type_addrs x_recs x_models x_src x_dst x_aset x_s x_n_recs x_k x_np
       x_univ_offset x_bnl s_out : SourceValue F}
      {bytes_in : List UInt8} {h h' : Heap F} {calls : List (Call F)},
      Good c_pub calls → Good c_rhs calls → Good c_adv calls →
      RCRep c_pub.t c_pub.lim h x_rc →
      RepList addrListEnum (Bytes.RepAddressRef addrTy) h (raws.map (·.a_rec)) x_recs →
      RepList addrListEnum (Bytes.RepAddressRef addrTy) h (raws.map (·.a_rm)) x_models →
      AddrMapAll addrMapEnum (fun _ k _ => advSet k) h x_aset →
      RenameMap c_pub.κ c_pub.κ f_id h x_src x_dst →
      L1.Stream h bytes_in x_s →
      (∀ e ∈ raws,
        c_pub.κ (ixAddr e.a_rm) = f_id e.cv.name ∧
        NoProjIn blockNames e.cv.type = true ∧
        (∀ (b_ind : Bytes.Address) (i_ind : Nat) (cv_ind : ConstantVal .anon)
          (caps_ind : IndCaps .anon),
          c_pub.env.find? (c_pub.κ (iprjAddr (ixAddr b_ind) i_ind)) =
            some (.indInfo cv_ind caps_ind) →
          (∃ bs dom body mb lvls_d, e.cv.type.stripPis e.mI = some (bs, .forallE dom body mb) ∧
            dom.getAppFn = .const (c_pub.κ (iprjAddr (ixAddr b_ind) i_ind)) lvls_d) →
          (∀ (k : Nat) (rl : RecRule .anon), e.rawRules[k]? = some rl →
            rl.ctor = c_pub.κ (cprjAddr (ixAddr b_ind) i_ind k)) ∧
          (∀ (k : Nat) (rl : RecRule .anon), e.rawRules[k]? = some rl → ∀ cvj cnP cnF,
            c_pub.env.find? rl.ctor = some (.ctorInfo cvj cnP cnF) →
            cvj.levelParams.length = cv_ind.levelParams.length)) ∧
        ∀ {p_ci x_r : SourceValue F} {h₁ h₂ : Heap F} {cs_ci : List (Call F)},
          Heap.Extends h h₁ →
          (∀ x ∈ cs_ci, x ∈ calls) →
          Bytes.RepAddressRef addrTy h₁ e.a_rec x_r →
          ObsFn W "Ingress::get_ci" [x_r] h₁ p_ci h₂ cs_ci →
          CIPtrRepExact c_pub.κ h₂ p_ci e.toCI) →
      ObsFn W "KernelModeled::check_recs"
        [x_rc, x_type_addrs, x_recs, x_models, x_src, x_dst, x_aset, x_s,
         x_n_recs, x_k, x_np, x_univ_offset, x_bnl] h s_out h' calls →
      ∃ (recs : List RecInstallEntry) (bytes_out : List UInt8),
        recs.map (·.cv) = raws.map (·.cv) ∧
        recs.map (·.prov_r) = raws.map (·.prov_r) ∧
        recs.map (·.prov_p) = raws.map (·.prov_p) ∧
        List.Forall₂
          (fun (e : RawRecEntry) (w : RecInstallEntry) =>
            w.cv = e.cv ∧ w.mI = e.mI ∧ w.rP = e.rP ∧ w.rawRules = e.rawRules)
          raws recs ∧
        (∀ w ∈ recs,
          w.cv.type.constsResolve c_pub.env = true ∧
          w.rP ≤ w.mI ∧
          w.cv.type.stripPis w.mI = some (w.pre, .forallE w.dom w.body w.bm) ∧
          w.dom.getAppFn = .const w.indKey w.lvls_lps ∧
          w.dom.getAppArgs.length = w.cnP_ind + (w.mI - w.rP) ∧
          (∀ p ∈ w.dom.getAppArgs.take w.cnP_ind, noLooseIn 0 (w.mI - w.rP) p = true) ∧
          w.dom.getAppArgs.drop w.cnP_ind =
            (List.range (w.mI - w.rP)).map (fun m => .bvar (w.mI - w.rP - 1 - m)) ∧
          w.pins_lps = (w.dom.getAppArgs.take w.cnP_ind).map (Expr.lowerBVars (w.mI - w.rP) 0) ∧
          (∀ r ∈ w.rawRules,
            noLetExpr (posOf w.cv.levelParams r.rhs) = true ∧
            r.rhs.constsResolve c_rhs.env = true ∧
            ∃ t', posRulesJ.infer c_rhs.env 0 r.rhs t') ∧
          RawIotaRulesVmRun c_pub c_rhs c_adv blockNames f_id advSet
            w.cv.name w.cv.levelParams w.cv.type w.mI w.rP w.lvls_lps w.pins_lps 0 w.rawRules) ∧
        L1.Stream h' bytes_out s_out ∧
        Heap.Extends h h' := by
  intro raws
  induction raws with
  | nil =>
    intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ bytes_in h h' _
      _ _ _ _ hrecs_rep _ _ _ hstr _ ev
    cases Obs.«KernelModeled::check_recs».obs ev with
    | Nil _ he21 he22 _ =>
      rw [he21, he22]
      exact ⟨[], bytes_in, rfl, rfl, rfl, .nil, (fun _ hm => nomatch hm), hstr, Heap.Extends.refl h⟩
    | Cons _ _ _ _ _ _ _ _ _ _ _ _ _ _
        _ _ _ _ _ _ _ _ _ _ _ _ _ _
        _ _ _ _ _ _ _ _ _ _ _ _ _ _
        _ _ _ _
        _ _ _ _ _ _
        _ _ _ _ _ _ _ _ _ _
        _ _ _ _ _ _ _ _ _ _
        ld12 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
        _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
      obtain ⟨_, _, he, _, _⟩ := Lib.rep_cons_of_load hrecs_rep ld12
      cases he
  | cons e₀ rawRest ih =>
    intro x_rc x_type_addrs x_recs x_models x_src x_dst x_aset x_s x_n_recs x_k x_np
      x_univ_offset x_bnl s_out bytes_in h h' calls
      hg_pub hg_rhs hg_adv hrc hrecs_rep hmd_rep haset hren hstr hraw_info ev
    cases Obs.«KernelModeled::check_recs».obs ev with
    | Nil ld12 _ _ _ =>
      cases Lib.rep_nil_of_load hrecs_rep ld12
    | Cons x_r x_rest x_rm x_mrest m67 p74 cs80 x_nl x_ty x_rnp x_ni x_nmot x_nmin x_rules
        x_kf x_r_uns w107 w108 v285 m288 cs296 v332 m335 cs343 v346 v347 m349 cs357
        v390 m391 cs401 v405 v406 x420 x428 x436 v472 m473 cs483 v510 m511 cs521
        v547 m548 cs558 m579
        safeTyValue safeTyHeap safeTyCalls safeRulesValue safeRulesHeap safeRulesCalls
        v591 m592 cs602 v645 _ cs656 v662 m688 p693 cs699 _ m646 _
        v731 m732 cs742 v749 x790 cs854 v866
        ld12 ld51 ev82 ld76 _ _ _ _ ev298 _ ev359 _ ev345 _ _ _ _ _ _ ev403 ev485
        ev523 hm587 ev560 evSafetyTy evSafetyRules ev604 ev701 _ ev658 evHeader op805 op797 ev744 _ ev856 hc969 =>
      have hsub80 : ∀ x ∈ cs80, x ∈ calls := fun x hx => by
        rw [hc969]
        repeat first | exact mem_head_step hx | exact hx | apply List.mem_cons_of_mem | apply mem_tail_step
      have hsub558 : ∀ x ∈ cs558, x ∈ calls := fun x hx => by
        rw [hc969]
        repeat first | exact mem_head_step hx | exact hx | apply List.mem_cons_of_mem | apply mem_tail_step
      have hsub742 : ∀ x ∈ cs742, x ∈ calls := fun x hx => by
        rw [hc969]
        repeat first | exact mem_head_step hx | exact hx | apply List.mem_cons_of_mem | apply mem_tail_step
      have hsub854 : ∀ x ∈ cs854, x ∈ calls := fun x hx => by
        rw [hc969]
        repeat first | exact mem_head_step hx | exact hx | apply List.mem_cons_of_mem | apply mem_tail_step
      obtain ⟨a_r', rRest, hr_eq, hr_head, hr_tail⟩ := Lib.rep_cons_of_load hrecs_rep ld12
      obtain ⟨a_rm', rmRest, hrm_eq, hrm_head, hrm_tail⟩ := Lib.rep_cons_of_load hmd_rep ld51
      injection hr_eq with h1 h2; subst h1
      injection hrm_eq with h3 h4; subst h3
      obtain ⟨hrm_key0, hnp_ty0, hrule_ctor0, hci0⟩ := hraw_info e₀ List.mem_cons_self
      have hptr0 : CIPtrRepExact c_pub.κ m67 p74 e₀.toCI :=
        hci0 (Heap.Extends.refl h) hsub80 hr_head ev82
      obtain ⟨v_rec, hld_rec, hci_rec⟩ := hptr0
      rw [ld76] at hld_rec; injection hld_rec with hv_rec
      generalize hci_rec_eq : e₀.toCI = ci_rec_g at hci_rec
      cases hci_rec with
      | @recr nl_r ty_r np_r ni_r nm_r nmi_r rules_r _ _ _ _ cv_g mI_g rP_g rls_g p_f i_f m_f mi_f
          hval0 hnp_f hni_f hnm_f hnmi_f hrP_f hmI_f hcounts0 hrules0 _ _ =>
        injection hv_rec with _ _ hrec_args
        injection hrec_args with h1_r hrec_1
        injection hrec_1 with h2_r hrec_2
        injection hrec_2 with h3_r hrec_3
        injection hrec_3 with h4_r hrec_4
        injection hrec_4 with h5_r hrec_5
        injection hrec_5 with h6_r hrec_6
        injection hrec_6 with h7_r _
        subst h1_r h2_r h3_r h4_r h5_r h6_r h7_r
        dsimp only [RawRecEntry.toCI] at hci_rec_eq
        injection hci_rec_eq with hcv_g hmI_g hrP_g hrls_g
        subst hcv_g hmI_g hrP_g hrls_g
        obtain ⟨hnl0, hlps_lt0, hperm0, hty_rep0⟩ := hval0
        obtain ⟨hrp_le0, hmi_lt0⟩ := hcounts0
        have e82 := ObsFn.heap_extends ev82
        have e298 := ObsFn.heap_extends ev298
        have e359 := ObsFn.heap_extends ev359
        have e345 := ObsFn.heap_extends ev345
        have e403 := ObsFn.heap_extends ev403
        have e485 := ObsFn.heap_extends ev485
        have e523 := ObsFn.heap_extends ev523
        have e_67_511 : Heap.Extends m67 m511 :=
          e298.trans (e359.trans (e345.trans (e403.trans (e485.trans e523))))
        have e_511_579 : Heap.Extends m511 m579 := by
          rw [hm587]; exact heap_extends_append m511 _
        have e_h_579 : Heap.Extends h m579 := e82.trans (e_67_511.trans e_511_579)
        have htypes579 : TypesRep c_pub.κ zg m579 0
            (.ptr (.enum Obs.Names.«Lists::Node<&KernelTypes::KExprNode>») m511.length) :=
          by rw [hm587]; exact typesRep_alloc_nil c_pub.κ zg m511
        obtain ⟨stype0, _, _, hinf_ty0, _, _, _⟩ :=
          core_ensure_sort hCore (hrc.mono e_h_579) htypes579 (ghostScoped_zero zg)
            hef_pub hlf_pub (hg_pub.sub hsub558) ev560
            ((hty_rep0 0 zg).toTm.mono (e_67_511.trans e_511_579))
        have hty_nfv0 : (posOf e₀.cv.levelParams e₀.cv.type).hasFvar = false :=
          Tm.hasFvar_false (hty_rep0 0 zg).toTm
        have hty_cr_pos0 :
            (posOf e₀.cv.levelParams e₀.cv.type).constsResolve c_pub.env = true :=
          infer_constsResolve hinf_ty0 hef_pub.store hty_nfv0
        have hty_cr0 : e₀.cv.type.constsResolve c_pub.env = true := by
          rwa [constsResolve_posOf] at hty_cr_pos0
        have e560 := ObsFn.heap_extends ev560
        have e604 := ObsFn.heap_extends ev604
        have e701 := ObsFn.heap_extends ev701
        have e658 := ObsFn.heap_extends ev658
        have e_579_646 : Heap.Extends m579 m646 :=
          e560.trans (evSafetyTy.heap_extends.trans (evSafetyRules.heap_extends.trans
            (e604.trans (e701.trans (e658.trans evHeader.heap_extends)))))
        have e_67_646 : Heap.Extends m67 m646 := (e_67_511.trans e_511_579).trans e_579_646
        have e_h_646 : Heap.Extends h m646 := e82.trans e_67_646
        have hv749_eq : v749 = .field (e₀.rP : F) := by
          rw [hnp_f, hnm_f] at op805
          simp only [evalBinOp, Except.ok.injEq] at op805
          rw [← op805, hnmi_f] at op797
          simp only [evalBinOp, Except.ok.injEq] at op797
          rw [← op797, ← hrP_f]
        have hxni_eq : x_ni = .field ((e₀.mI - e₀.rP : Nat) : F) := by
          rw [hni_f]
          congr 1
          rw [Nat.cast_sub hrp_le0, hrP_f, hmI_f]
          ring
        rw [hnl0, hv749_eq, hxni_eq] at ev744
        have hren646 : RenameMap c_pub.κ c_pub.κ f_id m646 x_src x_dst := by
          obtain ⟨sAs, dAs, hs, hd, hl, hm⟩ := hren
          exact ⟨sAs, dAs,
            RepLinkedList.mono (Bytes.repAddressRef_heapMono₂ addrTy) e_h_646 hs,
            RepLinkedList.mono (Bytes.repAddressRef_heapMono₂ addrTy) e_h_646 hd, hl, hm⟩
        obtain ⟨bytes_mid, indKey0, cnP_ind0, _, pre0, dom0, body0, bm0, lvls0, pins0,
            hstr_mid, _, hstrip0, hdom_fn0, hdom_len0, hdom_nli0, hdom_drop0, hpins0,
            hraw_rules0⟩ :=
          check_rules_vm_spec hCore hroles hcallees
            ht_rhs hlim_rhs ht_eq hlim_eq
            hef_pub hlf_pub hexact_pub hef_rhs hlf_rhs hef_adv hlf_adv hexact_adv
            hf_out hproj_rhs
            (hg_pub.sub hsub742)
            (hg_rhs.sub hsub742)
            (hg_adv.sub hsub742)
            hlps_lt0 hperm0 hrp_le0 hmi_lt0
            ⟨stype0, hinf_ty0⟩ hnp_ty0 hnp_ctor hrule_ctor0
            (hrc.mono e_h_646)
            (Bytes.repAddressRef_heapMono₂ addrTy e_h_646 hrm_head)
            hrm_key0
            (addrSet_mono e_h_646 haset)
            hren646
            (hty_rep0.mono e_67_646)
            (hrules0.mono e_67_646)
            (hstr.mono e_h_646)
            ev744
        have hrls_nolet0 : ∀ r ∈ e₀.rawRules,
            noLetExpr (posOf e₀.cv.levelParams r.rhs) = true :=
          rulesRepExact_noLet hrules0
        have hrls_facts0 : ∀ r ∈ e₀.rawRules,
            noLetExpr (posOf e₀.cv.levelParams r.rhs) = true ∧
            r.rhs.constsResolve c_rhs.env = true ∧
            ∃ t', posRulesJ.infer c_rhs.env 0 r.rhs t' := by
          have hwalk : ∀ (j : Nat) (rls : List (RecRule .anon)),
              RawIotaRulesVmRun c_pub c_rhs c_adv blockNames f_id advSet
                e₀.cv.name e₀.cv.levelParams e₀.cv.type e₀.mI e₀.rP lvls0 pins0 j rls →
              ∀ r ∈ rls, r.rhs.constsResolve c_rhs.env = true ∧
                ∃ t', posRulesJ.infer c_rhs.env 0 r.rhs t' := by
            intro j rls hrun r hr
            induction rls generalizing j with
            | nil => cases hr
            | cons r₀ rt ih_rls =>
              obtain ⟨⟨hcert⟩, hrt⟩ := hrun
              rcases List.mem_cons.mp hr with rfl | htl
              · exact ⟨hcert.hrhs_cr, hcert.hrhs_typed⟩
              · exact ih_rls (j + 1) hrt htl
          intro r hr
          obtain ⟨hcr, hinf⟩ := hwalk 0 e₀.rawRules hraw_rules0 r hr
          exact ⟨hrls_nolet0 r hr, hcr, hinf⟩
        let w₀ : RecInstallEntry :=
          { cv := e₀.cv
            mI := e₀.mI
            rP := e₀.rP
            cnP_ind := cnP_ind0
            indKey := indKey0
            lvls_lps := lvls0
            pins_lps := pins0
            pre := pre0
            dom := dom0
            body := body0
            bm := bm0
            rawRules := e₀.rawRules }
        have e744 := ObsFn.heap_extends ev744
        have e_h_732 : Heap.Extends h m732 := e_h_646.trans e744
        have hren732 : RenameMap c_pub.κ c_pub.κ f_id m732 x_src x_dst := by
          obtain ⟨sAs, dAs, hs, hd, hl, hm⟩ := hren
          exact ⟨sAs, dAs,
            RepLinkedList.mono (Bytes.repAddressRef_heapMono₂ addrTy) e_h_732 hs,
            RepLinkedList.mono (Bytes.repAddressRef_heapMono₂ addrTy) e_h_732 hd, hl, hm⟩
        have hr_tail' : RepList addrListEnum (Bytes.RepAddressRef addrTy) m732
            (rawRest.map (·.a_rec)) x_rest := by
          rw [← h2] at hr_tail
          exact RepLinkedList.mono (Bytes.repAddressRef_heapMono₂ addrTy) e_h_732 hr_tail
        have hrm_tail' : RepList addrListEnum (Bytes.RepAddressRef addrTy) m732
            (rawRest.map (·.a_rm)) x_mrest := by
          rw [← h4] at hrm_tail
          exact RepLinkedList.mono (Bytes.repAddressRef_heapMono₂ addrTy) e_h_732 hrm_tail
        obtain ⟨recsRest, bytes_out, hcv_map, hpr_map, hpp_map, hf2_rest,
            hw_rest, hstr_out, ext_rest⟩ :=
          ih
            (hg_pub.sub hsub854)
            (hg_rhs.sub hsub854)
            (hg_adv.sub hsub854)
            (hrc.mono e_h_732) hr_tail' hrm_tail'
            (addrSet_mono e_h_732 haset)
            hren732 hstr_mid
            (fun e he => by
              obtain ⟨hk_e, hnp_e, hrc_e, hci_e⟩ :=
                hraw_info e (List.mem_cons_of_mem e₀ he)
              exact ⟨hk_e, hnp_e, hrc_e, fun ext1 hsub1 hrep1 ev1 =>
                hci_e (e_h_732.trans ext1) (fun x hx => hsub854 x (hsub1 x hx)) hrep1 ev1⟩)
            ev856
        refine ⟨w₀ :: recsRest, bytes_out,
          congrArg (e₀.cv :: ·) hcv_map,
          congrArg (e₀.prov_r :: ·) hpr_map,
          congrArg (e₀.prov_p :: ·) hpp_map,
          .cons ⟨rfl, rfl, rfl, rfl⟩ hf2_rest,
          ?_, hstr_out, e_h_732.trans ext_rest⟩
        intro w hw
        rcases List.mem_cons.mp hw with rfl | htl
        · exact ⟨hty_cr0, hrp_le0, hstrip0, hdom_fn0, hdom_len0, hdom_nli0,
            hdom_drop0, hpins0, hrls_facts0, hraw_rules0⟩
        · exact hw_rest w htl
      | _ =>
        injection hv_rec with _ htag _
        exact absurd htag (by decide)

/-- Loader (L1), role/callee (L6), and assembly (L7) companions for a modeled inductive block
(`.indDecl block₀ nP` with `basisPinHit block₀ = none` when `block_is_modeled ≠ 0`). -/
structure ModeledFamilyBridge (calls : List (Call F)) (env : Env .anon)
    (block₀ : List (ConstantInfo .anon)) (nP : Nat)
    (E : Ixon.Env) (t : Ix.Kernel.RoleTable) (lim : Option Nat)
    (rc iblk : SourceValue F) (m_mb : Heap F) (cs_mb : List (Call F)) : Prop where
  rolesSpec : RolesSpec
  calleesSpec : CalleesSpec
  /-- Initial `read_payload` stream at `iblk` in `m_mb` and renewed payload stream inside
  `check_family` at any extended heap. -/
  readPayloadStream :
    ∀ {v_pay : SourceValue F} {h₁ h₂ : Heap F} {cs_p : List (Call F)},
      Heap.Extends m_mb h₁ →
      ObsFn W "KernelModeled::read_payload" [iblk] h₁ v_pay h₂ cs_p →
      ∃ bytes_p, L1.Stream h₂ bytes_p v_pay
  /-- `get_count` peels a count field off a payload `L1.Stream`. -/
  getCountStream :
    ∀ {x_s x_n x_s' : SourceValue F} {bytes_in : List UInt8} {h₁ h₂ : Heap F} {cs_c : List (Call F)},
      L1.Stream h₁ bytes_in x_s →
      ObsFn W "KernelModeled::get_count" [x_s] h₁ (.tuple [x_n, x_s']) h₂ cs_c →
      ∃ bytes_out, L1.Stream h₂ bytes_out x_s'
  /-- `check_witnesses` advances the payload `L1.Stream`. -/
  checkWitnessesStream :
    ∀ {x_s x_n x_out x_s' : SourceValue F} {bytes_in : List UInt8} {h₁ h₂ : Heap F}
      {cs_w : List (Call F)},
      L1.Stream h₁ bytes_in x_s →
      ObsFn W "KernelModeled::check_witnesses" [rc, iblk, x_s, x_n]
        h₁ (.tuple [x_out, x_s']) h₂ cs_w →
      ∃ bytes_out, L1.Stream h₂ bytes_out x_s'
  /-- Advice-record step oracle for `check_advice_records`. -/
  adviceOracle :
    ∀ (blockNames : List KKey) (wset : SourceValue F),
      AdviceStepOracle.{u} calls blockNames rc wset
  /-- Initial role-context & exact-loader companions on `⟨E, env, t, lim⟩`. -/
  baseCtxFacts :
    DeclStoreInv env →
    CtxRoleFacts ⟨E, env, t, lim⟩ ∧
    LoadFacts ⟨E, env, t, lim⟩ ∧
    ExactGetCI ⟨E, env, t, lim⟩ ∧
    Good ⟨E, env, t, lim⟩ calls
  /-- Exact L1/L7 decomposition of the family's inductive types (`v673`), constructors (`v746`),
  and recursors (`v839`) inside `check_family`, matching `installs (.indDecl block₀ nP)` and the
  syntactic checks (`build_flat_block`, `check_nested_aux`, `family_refs_ok`). -/
  familyMembers :
    ∀ {v_pay0 x_rec_block w_rem0 x_s4 x_n_w x_outside x_s5 v390 x_members
       w538 w539 w540 w541 v588 v673 v746 v839 x_univ_offset v1248 v1233 v1292 : SourceValue F}
      {m_pay0 m_ga m297 m332 m391 m453 m501 m589 m652 m674 m704 m747 m784 m840
       m1191 m1257 m1234 m1293 : Heap F}
      {cs_pay0 cs_ga0 cs342 cs401 cs511 cs599 cs684 cs757 cs850 cs1265 cs1244 cs1303 : List (Call F)},
      ObsFn W "KernelModeled::read_payload" [iblk] m_mb v_pay0 m_pay0 cs_pay0 →
      ObsFn W "IxonDeserialize::get_address" [v_pay0] m_pay0 (.tuple [x_rec_block, w_rem0]) m_ga cs_ga0 →
      ObsFn W "KernelModeled::check_witnesses" [rc, iblk, x_s4, x_n_w] m297
        (.tuple [x_outside, x_s5]) m332 cs342 →
      ObsFn W "KernelClaim::addr_set_build"
        [x_outside, .construct addrMapEnum "Nil" []] m332 v390 m391 cs401 →
      ObsFn W "Ingress::load_verified_constant" [iblk] m453
        (.construct "Ixon::Constant" "Mk"
          [.construct "Ixon::ConstantInfo" "Muts" [x_members], w538, w539, w540, w541])
        m501 cs511 →
      ObsFn W Obs.Names.«Lists::length<Ixon::MutConst>» [x_members] m501 v588 m589 cs599 →
      ObsFn W "Ingress::build_recur_addrs" [x_members, iblk] m652 v673 m674 cs684 →
      ObsFn W "KernelModeled::block_ctor_addrs" [x_members, iblk, .field 0] m704 v746 m747 cs757 →
      ObsFn W "KernelModeled::family_recs" [x_rec_block] m784 v839 m840 cs850 →
      ObsFn W "KernelCheck::build_flat_block" [x_rec_block, iblk, x_univ_offset]
        m1191 v1248 m1257 cs1265 →
      ObsFn W "KernelModeled::check_nested_aux" [iblk, v1248] m1257 v1233 m1234 cs1244 →
      ObsFn W "KernelModeled::family_refs_ok" [x_rec_block, iblk, v390]
        m1234 v1292 m1293 cs1303 →
      ∃ (indAs ctorAs : List Bytes.Address)
        (inds ctors : List (ConstantInfo .anon))
        (rawSpecs : List RawRecSpec)
        (_hind_len : indAs.length = inds.length)
        (_hctor_len : ctorAs.length = ctors.length),
        let nonrecs := inds ++ ctors
        let blockNames := (nonrecs.map (·.name)) ++ (rawSpecs.map (·.cv.name))
        v588 = .field (indAs.length : F) ∧
        indAs.length < 4294967296 ∧
        ctorAs.length < 4294967296 ∧
        rawSpecs.length < 4294967296 ∧
        RepList addrListEnum (Bytes.RepAddressRef addrTy) m674 indAs v673 ∧
        RepList addrListEnum (Bytes.RepAddressRef addrTy) m747 ctorAs v746 ∧
        RepList addrListEnum (Bytes.RepAddressRef addrTy) m840 (rawSpecs.map (·.a_rec)) v839 ∧
        blockNames.Nodup ∧
        (∀ c ∈ nonrecs,
          isBaseKey c.name = true ∧
          Ix.Kernel.reservedBasisNames.contains c.name = false ∧
          ((∃ cv, c = .indInfo cv {}) ∨ ∃ cv nP_c nF_c, c = .ctorInfo cv nP_c nF_c) ∧
          NoProjIn blockNames c.toConstantVal.type = true ∧
          (∃ ci₀ ∈ IxVM.Consistency.installs (.indDecl block₀ nP), ci₀.name = c.name)) ∧
        (∀ s ∈ rawSpecs,
          isBaseKey s.cv.name = true ∧
          Ix.Kernel.reservedBasisNames.contains s.cv.name = false ∧
          NoProjIn blockNames s.cv.type = true ∧
          s.cv.type.constsResolve (pushList nonrecs env) = true ∧
          (∃ ci₀ ∈ IxVM.Consistency.installs (.indDecl block₀ nP), ci₀.name = s.cv.name)) ∧
        (∀ ci₀ ∈ IxVM.Consistency.installs (.indDecl block₀ nP),
          (∃ c ∈ nonrecs, IxVM.Consistency.StoredAs c ci₀) ∨
          (∃ s ∈ rawSpecs, IxVM.Consistency.StoredAs s.toCI ci₀)) ∧
        (∀ i (hi : i < indAs.length),
          keyOf t (ixAddr indAs[i]) = (inds[i]'(by omega)).name ∧
          ∀ {p_ci x_m : SourceValue F} {h₁ h₂ : Heap F} {cs_ci : List (Call F)},
            Heap.Extends m840 h₁ → (∀ x ∈ cs_ci, x ∈ calls) →
            Bytes.RepAddressRef addrTy h₁ indAs[i] x_m →
            ObsFn W "Ingress::get_ci" [x_m] h₁ p_ci h₂ cs_ci →
            CIPtrRepExact (keyOf t) h₂ p_ci (inds[i]'(by omega))) ∧
        (∀ i (hi : i < ctorAs.length),
          keyOf t (ixAddr ctorAs[i]) = (ctors[i]'(by omega)).name ∧
          ∀ {p_ci x_m : SourceValue F} {h₁ h₂ : Heap F} {cs_ci : List (Call F)},
            Heap.Extends m840 h₁ → (∀ x ∈ cs_ci, x ∈ calls) →
            Bytes.RepAddressRef addrTy h₁ ctorAs[i] x_m →
            ObsFn W "Ingress::get_ci" [x_m] h₁ p_ci h₂ cs_ci →
            CIPtrRepExact (keyOf t) h₂ p_ci (ctors[i]'(by omega))) ∧
        (∀ i (hi : i < rawSpecs.length),
          keyOf t (ixAddr rawSpecs[i].a_rec) = rawSpecs[i].cv.name ∧
          ∀ {p_ci x_r : SourceValue F} {h₁ h₂ : Heap F} {cs_ci : List (Call F)},
            Heap.Extends m840 h₁ → (∀ x ∈ cs_ci, x ∈ calls) →
            Bytes.RepAddressRef addrTy h₁ rawSpecs[i].a_rec x_r →
            ObsFn W "Ingress::get_ci" [x_r] h₁ p_ci h₂ cs_ci →
            CIPtrRepExact (keyOf t) h₂ p_ci rawSpecs[i].toCI) ∧
        (∀ pre suff c, nonrecs = pre ++ c :: suff →
          c.toConstantVal.type.constsResolve (pushList pre env) = true) ∧
        (∀ ck cvj cnP cnF,
          (pushList (nonrecs.map posCI) env).find? ck = some (.ctorInfo cvj cnP cnF) →
          cvj.type.allLevelParamsDefined cvj.levelParams = true ∧
          NoProjIn blockNames cvj.type = true ∧
          (pushList nonrecs env).find? ck = some (.ctorInfo cvj cnP cnF) ∧
          ∃ bsC0 cbody0 Dc usc,
            cvj.type.stripPis (cnP + cnF) = some (bsC0, cbody0) ∧
            cbody0.getAppFn = .const Dc usc) ∧
        (∀ s ∈ rawSpecs,
          ∀ (b_ind : Bytes.Address) (i_ind : Nat) (cv_ind : ConstantVal .anon)
            (caps_ind : IndCaps .anon),
            (pushList (nonrecs.map posCI) env).find?
              (keyOf t (iprjAddr (ixAddr b_ind) i_ind)) = some (.indInfo cv_ind caps_ind) →
            (∃ bs dom body mb lvls_d, s.cv.type.stripPis s.mI = some (bs, .forallE dom body mb) ∧
              dom.getAppFn = .const (keyOf t (iprjAddr (ixAddr b_ind) i_ind)) lvls_d) →
            (∀ (k : Nat) (rl : RecRule .anon), s.rawRules[k]? = some rl →
              rl.ctor = keyOf t (cprjAddr (ixAddr b_ind) i_ind k)) ∧
            (∀ (k : Nat) (rl : RecRule .anon), s.rawRules[k]? = some rl → ∀ cvj cnP cnF,
              (pushList (nonrecs.map posCI) env).find? rl.ctor = some (.ctorInfo cvj cnP cnF) →
              cvj.levelParams.length = cv_ind.levelParams.length)) ∧
        (DeclStoreInv (pushList (nonrecs.map posCI) env) →
          CtxRoleFacts ⟨E, pushList (nonrecs.map posCI) env, t, lim⟩ ∧
          LoadFacts ⟨E, pushList (nonrecs.map posCI) env, t, lim⟩ ∧
          ExactGetCI ⟨E, pushList (nonrecs.map posCI) env, t, lim⟩ ∧
          Good ⟨E, pushList (nonrecs.map posCI) env, t, lim⟩ calls) ∧
        (DeclStoreInv
            (pushList (rawSpecs.map RawRecSpec.prov_p) (pushList (nonrecs.map posCI) env)) →
          CtxRoleFacts
            ⟨E, pushList (rawSpecs.map RawRecSpec.prov_p) (pushList (nonrecs.map posCI) env),
             t, lim⟩ ∧
          LoadFacts
            ⟨E, pushList (rawSpecs.map RawRecSpec.prov_p) (pushList (nonrecs.map posCI) env),
             t, lim⟩ ∧
          Good
            ⟨E, pushList (rawSpecs.map RawRecSpec.prov_p) (pushList (nonrecs.map posCI) env),
             t, lim⟩ calls)

private theorem forall₂_mem_right {α β : Type _} {R : α → β → Prop} :
    ∀ {xs : List α} {ys : List β}, List.Forall₂ R xs ys → ∀ y ∈ ys, ∃ x ∈ xs, R x y
  | _, _, .nil, _, hy => nomatch hy
  | a :: _, _ :: _, .cons hhd htl, _, hy => by
    rcases List.mem_cons.mp hy with rfl | hm
    · exact ⟨a, List.mem_cons_self, hhd⟩
    · obtain ⟨x, hx, hr⟩ := forall₂_mem_right htl _ hm
      exact ⟨x, List.mem_cons_of_mem a hx, hr⟩

private theorem forall₂_mem_left {α β : Type _} {R : α → β → Prop} :
    ∀ {xs : List α} {ys : List β}, List.Forall₂ R xs ys → ∀ x ∈ xs, ∃ y ∈ ys, R x y
  | _, _, .nil, _, hx => nomatch hx
  | _ :: _, b :: _, .cons hhd htl, _, hx => by
    rcases List.mem_cons.mp hx with rfl | hm
    · exact ⟨b, List.mem_cons_self, hhd⟩
    · obtain ⟨y, hy, hr⟩ := forall₂_mem_left htl _ hm
      exact ⟨y, List.mem_cons_of_mem b hy, hr⟩

set_option maxHeartbeats 6400000 in
/-- **End-to-end `KernelModeled::check_modeled_block` / `check_family` refinement**: constructs
`Nonempty (ModeledBlockWitness.{u} env block₀ nP)` from an observed `check_modeled_block` run and
`ModeledFamilyBridge`. -/
theorem modeledBlockWitness_of_check_family
    (hCore : IxVM.Consistency.Core S₀)
    {calls : List (Call F)} {env : Env .anon}
    {block₀ : List (ConstantInfo .anon)} {nP : Nat}
    {E : Ixon.Env} {t : Ix.Kernel.RoleTable} {lim : Option Nat}
    {rc iblk r_mb : SourceValue F} {m_mb h'_mb : Heap F} {cs_mb : List (Call F)}
    (htwf : t.wf = true)
    (hrc_mb : RCRep t lim m_mb rc)
    (hsub_mb : ∀ x ∈ cs_mb, x ∈ calls)
    (hfresh : ∀ ci₀ ∈ IxVM.Consistency.installs (.indDecl block₀ nP), env.find? ci₀.name = none)
    (ev_mb : ObsFn W "KernelModeled::check_modeled_block" [rc, iblk] m_mb r_mb h'_mb cs_mb)
    (bridge : ModeledFamilyBridge.{u} calls env block₀ nP E t lim rc iblk m_mb cs_mb)
    (hS₀ : DeclStoreInv env) (hAux₀ : AuxRootSynced env) :
    Nonempty (ModeledBlockWitness.{u} env block₀ nP) := by
  obtain ⟨v_pay0, x_rec_block, w_rem0, m_pay0, m_ga, cs_pay0, cs_ga0, cs_fam,
      ev_pay0, ev_ga0, ev_fam, ext_mb_ga, hsub_fam0⟩ :=
    check_modeled_block_inv ev_mb
  have hsub_fam : ∀ x ∈ cs_fam, x ∈ calls := fun x hx => hsub_mb x (hsub_fam0 x hx)
  cases Obs.«KernelModeled::check_family».obs ev_fam with
  | run v104 m105 cs107 v113 m114 cs124 m136 cs146 x_rb x_s1 v181 m184 cs192
      m219 cs229 x_n_a x_s2 m254 cs264 x_advice x_s3 m297 cs307 x_n_w x_s4
      m332 cs342 x_outside x_s5 v390 m391 cs401 v422 m423 cs433 v452 m453 cs463
      m501 cs511 w538 w539 w540 w541 x_members v588 m589 cs599 v621 m624 cs632
      v651 m652 cs662 v673 m674 cs684 m704 cs714 x_type_models x_s6 v746 m747 cs757
      m784 cs794 v798 m807 cs815 x_ctor_models x_s7 v839 m840 cs850 v861 m862 cs872
      m884 cs894 x_rec_models x_s8 v926 m927 cs937 v941 m950 cs958 v977 m978 cs988
      v992 m1001 cs1009 v1028 m1029 cs1039 v1082 m1083 cs1093 v1136 m1137 cs1147
      m1191 cs1201 x_bnl x_univ_offset v1233 m1234 cs1244 v1248 m1257 cs1265
      v1292 m1293 cs1303 v1330 m1331 cs1341
      sg112 ev126 ev148 ev194 _ ev231 ev266 ev309 ev344 ev403 ev435 ev465
      ev513 ev601 ev634 _ ev664 ev686 ev716 ev759 ev817 ev796 ev852 ev874 ev896
      ev960 ev939 ev1011 ev990 ev1041 ev1095 ev1149 ev1203 ev1267 ev1246 ev1305
      ev1343 _ _ _ hc1466 =>
    -- Subcall inclusions for the 5 key sub-derivations
    have hsub463 : ∀ x ∈ cs463, x ∈ calls := fun x hx => hsub_fam x (by
      rw [hc1466]; repeat first | exact mem_head_step hx | exact hx | apply mem_tail_step)
    have hsub1039 : ∀ x ∈ cs1039, x ∈ calls := fun x hx => hsub_fam x (by
      rw [hc1466]; repeat first | exact mem_head_step hx | exact hx | apply mem_tail_step)
    have hsub1093 : ∀ x ∈ cs1093, x ∈ calls := fun x hx => hsub_fam x (by
      rw [hc1466]; repeat first | exact mem_head_step hx | exact hx | apply mem_tail_step)
    have hsub1147 : ∀ x ∈ cs1147, x ∈ calls := fun x hx => hsub_fam x (by
      rw [hc1466]; repeat first | exact mem_head_step hx | exact hx | apply mem_tail_step)
    have hsub1341 : ∀ x ∈ cs1341, x ∈ calls := fun x hx => hsub_fam x (by
      rw [hc1466]; repeat first | exact mem_head_step hx | exact hx | apply mem_tail_step)
    -- 1. Extract family member lists and L1/L7 invariants
    obtain ⟨indAs, ctorAs, inds, ctors, rawSpecs, hind_len, hctor_len,
        hv588_eq, hind_lt, hctor_lt, hspec_lt,
        hind_rep_674, hctor_rep_747, hrec_rep_840,
        hbn_nd,
        hnr_info, hspec_info, hcov_raw,
        hind_idx, hctor_idx, hspec_idx,
        hcr_nr, hc_wf, hspec_canonical, hctx_pub_fn, hctx_rhs_fn⟩ :=
      bridge.familyMembers ev_pay0 ev_ga0 ev344 ev403 ev513 ev601 ev686 ev759
        ev852 ev1267 ev1246 ev1305
    let nonrecs := inds ++ ctors
    let recAs := rawSpecs.map (·.a_rec)
    let blockNames := (nonrecs.map (·.name)) ++ (rawSpecs.map (·.cv.name))
    -- 2. Payload stream walk up to `ev465 : check_advice_records`
    have ext_105 : Heap.Extends m_ga m105 := check_family_seg1_inv sg112
    obtain ⟨bytes0, hs0⟩ := bridge.readPayloadStream (ext_mb_ga.trans ext_105) ev126
    have ext_114 := ObsFn.heap_extends ev126
    obtain ⟨_, bytes1, _, _, _, htup148, _, hs1_0, ext_136, _⟩ := get_address_spec hs0 ev148
    injection htup148 with hargs148
    injection hargs148 with _ h148_2
    injection h148_2 with hxs1_eq _
    subst hxs1_eq
    have ext_184 := ObsFn.heap_extends ev194
    obtain ⟨bytes2, hs2⟩ := bridge.getCountStream (hs1_0.mono ext_184) ev231
    have ext_219 := ObsFn.heap_extends ev231
    obtain ⟨_, advAs, bytes3, _, _, hadv_rep_254, hs3, ext_254⟩ := get_addrs_spec hs2 ev266
    obtain ⟨bytes4, hs4⟩ := bridge.getCountStream hs3 ev309
    have ext_297 := ObsFn.heap_extends ev309
    obtain ⟨bytes5, hs5⟩ := bridge.checkWitnessesStream hs4 ev344
    have ext_332 := ObsFn.heap_extends ev344
    have ext_423 : Heap.Extends m332 m423 :=
      (ObsFn.heap_extends ev403).trans (ObsFn.heap_extends ev435)
    have ext_mb_423 : Heap.Extends m_mb m423 :=
      ext_mb_ga.trans (ext_105.trans (ext_114.trans (ext_136.trans
        (ext_184.trans (ext_219.trans (ext_254.trans (ext_297.trans (ext_332.trans ext_423))))))))
    have hadv_rep_423 : RepList addrListEnum (Bytes.RepAddressRef addrTy) m423 advAs x_advice :=
      RepLinkedList.mono (Bytes.repAddressRef_heapMono₂ addrTy)
        (ext_297.trans (ext_332.trans ext_423)) hadv_rep_254
    -- 3. `check_advice_records` (`ev465`)
    let instNames := (IxVM.Consistency.installs (.indDecl block₀ nP)).map (·.name)
    have hfr_inst0 : ∀ k ∈ instNames, env.find? k = none := by
      intro k hk
      obtain ⟨ci₀, hm₀, rfl⟩ := List.mem_map.mp hk
      exact hfresh ci₀ hm₀
    obtain ⟨hR₀, hlf₀, hex₀, hg₀⟩ := bridge.baseCtxFacts hS₀
    let c₀ : Ctx := ⟨E, env, t, lim⟩
    have hef₀ : EnvFacts c₀ := hS₀.toEnvFacts htwf hR₀
    obtain ⟨c_adv, hE_adv, ht_adv, hlim_adv, hadv_step, hS_adv, hAux_adv, hfr_inst_adv,
        hef_adv, hlf_adv, hex_adv, hg_adv, haset_raw, _, ext_453⟩ :=
      check_advice_records_spec (bridge.adviceOracle instNames v390)
        advAs (fun _ => False) c₀ hS₀ hAux₀ hfr_inst0
        (fun _ hf => False.elim hf)
        (hrc_mb.mono ext_mb_423) hef₀ hlf₀ hex₀ hg₀
        hadv_rep_423 .nil ev465 hsub463
    have haset_453 : AddrMapAll addrMapEnum (fun _ b _ => b ∈ advAs) m453 v452 :=
      addrMapAll_mono_pred (Heap.Extends.refl m453) (fun hp => hp.elim False.elim id) haset_raw
    have hκ_adv : c_adv.κ = keyOf t := by simp [Ctx.κ, ht_adv, c₀]
    have htwf_adv : c_adv.t.wf = true := ht_adv ▸ htwf
    -- 4. Deserialized model address lists (`ev716`, `ev817`, `ev796`, `ev874`, `ev896`)
    have ext_453_674 : Heap.Extends m453 m674 :=
      (ObsFn.heap_extends ev513).trans
        ((ObsFn.heap_extends ev601).trans
          ((ObsFn.heap_extends ev634).trans
            ((ObsFn.heap_extends ev664).trans (ObsFn.heap_extends ev686))))
    have hs5_674 : L1.Stream m674 bytes5 x_s5 :=
      hs5.mono (ext_423.trans (ext_453.trans ext_453_674))
    obtain ⟨n_tm_f, tmAs, bytes6, hv588_f, htm_len0, htm_rep_704, hs6, ext_704⟩ :=
      get_addrs_spec hs5_674 ev716
    have htm_len : tmAs.length = indAs.length := by
      have hf : n_tm_f = (indAs.length : F) := Value.field.inj (hv588_f.symm.trans hv588_eq)
      rw [htm_len0, hf, SubstAux.val_natCast (Nat.lt_trans hind_lt (by decide))]
    have ext_747 := ObsFn.heap_extends ev759
    obtain ⟨hv798_eq, hm807_eq⟩ := addrList_length_spec hctor_rep_747 ev817
    have ext_807 : Heap.Extends m747 m807 := hm807_eq ▸ Heap.Extends.refl m747
    obtain ⟨n_cm_f, cmAs, bytes7, hv798_f, hcm_len0, hcm_rep_784, hs7, ext_784⟩ :=
      get_addrs_spec (hs6.mono (ext_747.trans ext_807)) ev796
    have hcm_len : cmAs.length = ctorAs.length := by
      have hf : n_cm_f = (ctorAs.length : F) := Value.field.inj (hv798_f.symm.trans hv798_eq)
      rw [hcm_len0, hf, SubstAux.val_natCast (Nat.lt_trans hctor_lt (by decide))]
    have ext_840 := ObsFn.heap_extends ev852
    obtain ⟨hv861_eq, hm862_eq⟩ := addrList_length_spec hrec_rep_840 ev874
    have ext_862 : Heap.Extends m840 m862 := hm862_eq ▸ Heap.Extends.refl m840
    obtain ⟨n_rm_f, rmAs, bytes8, hv861_f, hrm_len0, hrm_rep_884, hs8, ext_884⟩ :=
      get_addrs_spec (hs7.mono (ext_840.trans ext_862)) ev896
    have hrm_len : rmAs.length = rawSpecs.length := by
      have hf : n_rm_f = ((rawSpecs.map (·.a_rec)).length : F) :=
        Value.field.inj (hv861_f.symm.trans hv861_eq)
      rw [hrm_len0, hf, List.length_map, SubstAux.val_natCast (Nat.lt_trans hspec_lt (by decide))]
    -- 5. Build `RenameMap` (`ev960`, `ev939`, `ev1011`, `ev990`)
    have ext_840_884 : Heap.Extends m840 m884 := ext_862.trans ext_884
    have ext_784_884 : Heap.Extends m784 m884 := ext_840.trans ext_840_884
    have ext_747_884 : Heap.Extends m747 m884 := (ext_807.trans ext_784).trans ext_784_884
    have ext_704_884 : Heap.Extends m704 m884 := ext_747.trans ext_747_884
    have ext_674_884 : Heap.Extends m674 m884 := ext_704.trans ext_704_884
    have h941 := addrList_concat_spec
      (RepLinkedList.mono (Bytes.repAddressRef_heapMono₂ addrTy) ext_747_884 hctor_rep_747)
      (RepLinkedList.mono (Bytes.repAddressRef_heapMono₂ addrTy) ext_840_884 hrec_rep_840)
      ev960
    have ext_950 := ObsFn.heap_extends ev960
    have h926 := addrList_concat_spec
      (RepLinkedList.mono (Bytes.repAddressRef_heapMono₂ addrTy)
        (ext_674_884.trans ext_950) hind_rep_674)
      h941 ev939
    have ext_927 := ObsFn.heap_extends ev939
    have h992 := addrList_concat_spec
      (RepLinkedList.mono (Bytes.repAddressRef_heapMono₂ addrTy)
        (ext_784_884.trans (ext_950.trans ext_927)) hcm_rep_784)
      (RepLinkedList.mono (Bytes.repAddressRef_heapMono₂ addrTy)
        (ext_950.trans ext_927) hrm_rep_884)
      ev1011
    have ext_1001 := ObsFn.heap_extends ev1011
    have h977 := addrList_concat_spec
      (RepLinkedList.mono (Bytes.repAddressRef_heapMono₂ addrTy)
        (ext_704_884.trans (ext_950.trans (ext_927.trans ext_1001))) htm_rep_704)
      h992 ev990
    have ext_978 := ObsFn.heap_extends ev990
    have ext_884_978 : Heap.Extends m884 m978 :=
      ext_950.trans (ext_927.trans (ext_1001.trans ext_978))
    have ext_840_978 : Heap.Extends m840 m978 := ext_840_884.trans ext_884_978
    let srcAs := indAs ++ (ctorAs ++ recAs)
    let dstAs := tmAs ++ (cmAs ++ rmAs)
    have hlen_sd : srcAs.length = dstAs.length := by
      simp [srcAs, dstAs, recAs, htm_len, hcm_len, hrm_len]
    let f_id : KKey → KKey := fun k =>
      renameKeyList k (srcAs.map fun b => keyOf t (ixAddr b))
        (dstAs.map fun b => keyOf t (ixAddr b))
    have hren_978 : RenameMap (keyOf t) (keyOf t) f_id m978 v926 v977 :=
      renameMap_of_lists htwf hlen_sd
        (RepLinkedList.mono (Bytes.repAddressRef_heapMono₂ addrTy)
          (ext_1001.trans ext_978) h926)
        h977
    -- Key-map equations and slice index lookups for `f_id`
    have hind_keys : indAs.map (fun b => keyOf t (ixAddr b)) = inds.map (·.name) := by
      apply List.ext_getElem (by simp [hind_len])
      intro i hi₁ _
      simp only [List.length_map] at hi₁
      simp only [List.getElem_map]
      exact (hind_idx i hi₁).1
    have hctor_keys : ctorAs.map (fun b => keyOf t (ixAddr b)) = ctors.map (·.name) := by
      apply List.ext_getElem (by simp [hctor_len])
      intro i hi₁ _
      simp only [List.length_map] at hi₁
      simp only [List.getElem_map]
      exact (hctor_idx i hi₁).1
    have hrec_keys : recAs.map (fun b => keyOf t (ixAddr b)) = rawSpecs.map (·.cv.name) := by
      apply List.ext_getElem (by simp [recAs])
      intro i hi₁ _
      simp only [List.length_map, recAs] at hi₁
      simp only [List.getElem_map, recAs]
      exact (hspec_idx i hi₁).1
    let ks₁ := inds.map (·.name)
    let ks₂ := ctors.map (·.name)
    let ks₃ := rawSpecs.map (·.cv.name)
    let ds₁ := tmAs.map fun b => keyOf t (ixAddr b)
    let ds₂ := cmAs.map fun b => keyOf t (ixAddr b)
    let ds₃ := rmAs.map fun b => keyOf t (ixAddr b)
    have hsrc_keys : srcAs.map (fun b => keyOf t (ixAddr b)) = ks₁ ++ (ks₂ ++ ks₃) := by
      simp only [srcAs, List.map_append, hind_keys, hctor_keys, hrec_keys, ks₁, ks₂, ks₃]
    have hdst_keys : dstAs.map (fun b => keyOf t (ixAddr b)) = ds₁ ++ (ds₂ ++ ds₃) := by
      simp only [dstAs, List.map_append, ds₁, ds₂, ds₃]
    have hbn_assoc : blockNames = ks₁ ++ (ks₂ ++ ks₃) := by
      simp only [blockNames, nonrecs, List.map_append, List.append_assoc, ks₁, ks₂, ks₃]
    have hf_out : ∀ k, blockNames.contains k = false → f_id k = k := by
      intro k hk
      show renameKeyList k (srcAs.map _) (dstAs.map _) = k
      rw [hsrc_keys, ← hbn_assoc]
      exact renameKeyList_out k blockNames _ hk
    have hbn_nd' : (ks₁ ++ (ks₂ ++ ks₃)).Nodup := hbn_assoc ▸ hbn_nd
    have hnd₁ : ks₁.Nodup := (List.nodup_append.mp hbn_nd').1
    have hnd₂₃ : (ks₂ ++ ks₃).Nodup := (List.nodup_append.mp hbn_nd').2.1
    have hdisj₁ : ∀ x ∈ ks₁, x ∉ ks₂ ++ ks₃ :=
      fun x hx hy => (List.nodup_append.mp hbn_nd').2.2 x hx x hy rfl
    have hnd₂ : ks₂.Nodup := (List.nodup_append.mp hnd₂₃).1
    have hnd₃ : ks₃.Nodup := (List.nodup_append.mp hnd₂₃).2.1
    have hdisj₂ : ∀ x ∈ ks₂, x ∉ ks₃ :=
      fun x hx hy => (List.nodup_append.mp hnd₂₃).2.2 x hx x hy rfl
    have hkd_len₁ : ks₁.length = ds₁.length := by simp [ks₁, ds₁, hind_len.symm, htm_len]
    have hkd_len₂ : ks₂.length = ds₂.length := by simp [ks₂, ds₂, hctor_len.symm, hcm_len]
    have hkd_len₃ : ks₃.length = ds₃.length := by simp [ks₃, ds₃, hrm_len]
    have hf_ind : ∀ i (hi : i < indAs.length),
        keyOf t (ixAddr (tmAs[i]'(by omega))) = f_id (inds[i]'(by omega)).name := by
      intro i hi
      have hi_k : i < ks₁.length := by simp [ks₁, hind_len.symm, hi]
      have hmem_k : ks₁[i] ∈ ks₁ := List.getElem_mem hi_k
      have hstep : f_id ks₁[i] = ds₁[i]'(hkd_len₁ ▸ hi_k) := by
        show renameKeyList ks₁[i] (srcAs.map _) (dstAs.map _) = _
        rw [hsrc_keys, hdst_keys,
          renameKeyList_append_left (ks₂ ++ ks₃) (ds₂ ++ ds₃) hkd_len₁ hmem_k]
        exact renameKeyList_getElem_of_nodup hnd₁ hkd_len₁ hi_k
      simpa [ks₁, ds₁] using hstep.symm
    have hf_ctor : ∀ i (hi : i < ctorAs.length),
        keyOf t (ixAddr (cmAs[i]'(by omega))) = f_id (ctors[i]'(by omega)).name := by
      intro i hi
      have hi_k : i < ks₂.length := by simp [ks₂, hctor_len.symm, hi]
      have hmem_k : ks₂[i] ∈ ks₂ := List.getElem_mem hi_k
      have hnin₁ : ks₂[i] ∉ ks₁ :=
        fun hm => hdisj₁ ks₂[i] hm (List.mem_append_left ks₃ hmem_k)
      have hstep : f_id ks₂[i] = ds₂[i]'(hkd_len₂ ▸ hi_k) := by
        show renameKeyList ks₂[i] (srcAs.map _) (dstAs.map _) = _
        rw [hsrc_keys, hdst_keys,
          renameKeyList_append_right (ks₂ ++ ks₃) (ds₂ ++ ds₃) hkd_len₁ hnin₁,
          renameKeyList_append_left ks₃ ds₃ hkd_len₂ hmem_k]
        exact renameKeyList_getElem_of_nodup hnd₂ hkd_len₂ hi_k
      simpa [ks₂, ds₂] using hstep.symm
    have hf_spec : ∀ i (hi : i < rawSpecs.length),
        keyOf t (ixAddr (rmAs[i]'(by omega))) = f_id rawSpecs[i].cv.name := by
      intro i hi
      have hi_k : i < ks₃.length := by simp [ks₃, hi]
      have hmem_k : ks₃[i] ∈ ks₃ := List.getElem_mem hi_k
      have hnin₁ : ks₃[i] ∉ ks₁ :=
        fun hm => hdisj₁ ks₃[i] hm (List.mem_append_right ks₂ hmem_k)
      have hnin₂ : ks₃[i] ∉ ks₂ := fun hm => hdisj₂ ks₃[i] hm hmem_k
      have hstep : f_id ks₃[i] = ds₃[i]'(hkd_len₃ ▸ hi_k) := by
        show renameKeyList ks₃[i] (srcAs.map _) (dstAs.map _) = _
        rw [hsrc_keys, hdst_keys,
          renameKeyList_append_right (ks₂ ++ ks₃) (ds₂ ++ ds₃) hkd_len₁ hnin₁,
          renameKeyList_append_right ks₃ ds₃ hkd_len₂ hnin₂]
        exact renameKeyList_getElem_of_nodup hnd₃ hkd_len₃ hi_k
      simpa [ks₃, ds₃] using hstep.symm
    -- 6. Run `members_val_spec` on `inds` (`ev1041`), `ctors` (`ev1095`), and `rawSpecs` (`ev1149`)
    have ext_453_978 : Heap.Extends m453 m978 :=
      ext_453_674.trans (ext_674_884.trans ext_884_978)
    have haset_978 : AddrMapAll addrMapEnum (fun _ b _ => b ∈ advAs) m978 v452 :=
      addrSet_mono ext_453_978 haset_453
    have hren_adv_978 : RenameMap c_adv.κ c_adv.κ f_id m978 v926 v977 := hκ_adv.symm ▸ hren_978
    obtain ⟨hmv_inds, ext_1029⟩ :=
      members_val_spec bridge.rolesSpec htwf_adv hex_adv hf_out indAs tmAs inds
        htm_len.symm hind_len (hg_adv.sub hsub1039)
        (RepLinkedList.mono (Bytes.repAddressRef_heapMono₂ addrTy)
          (ext_674_884.trans ext_884_978) hind_rep_674)
        (RepLinkedList.mono (Bytes.repAddressRef_heapMono₂ addrTy)
          (ext_704_884.trans ext_884_978) htm_rep_704)
        (fun i hi => by
          have hc_mem : inds[i]'(by omega) ∈ nonrecs :=
            List.mem_append_left ctors (List.getElem_mem (by omega))
          refine ⟨by rw [hκ_adv]; exact hf_ind i hi,
            (hnr_info _ hc_mem).2.2.2.1, fun ext1 hsub1 hrep1 ev1 => ?_⟩
          rw [hκ_adv]
          exact (hind_idx i hi).2 (ext_840_978.trans ext1)
            (fun x hx => hsub1039 x (hsub1 x hx)) hrep1 ev1)
        haset_978 hren_adv_978 ev1041
    have hren_adv_1029 : RenameMap c_adv.κ c_adv.κ f_id m1029 v926 v977 := by
      obtain ⟨sAs, dAs, hs, hd, hl, hm⟩ := hren_adv_978
      exact ⟨sAs, dAs,
        RepLinkedList.mono (Bytes.repAddressRef_heapMono₂ addrTy) ext_1029 hs,
        RepLinkedList.mono (Bytes.repAddressRef_heapMono₂ addrTy) ext_1029 hd, hl, hm⟩
    obtain ⟨hmv_ctors, ext_1083⟩ :=
      members_val_spec bridge.rolesSpec htwf_adv hex_adv hf_out ctorAs cmAs ctors
        hcm_len.symm hctor_len (hg_adv.sub hsub1093)
        (RepLinkedList.mono (Bytes.repAddressRef_heapMono₂ addrTy)
          (ext_747_884.trans (ext_884_978.trans ext_1029)) hctor_rep_747)
        (RepLinkedList.mono (Bytes.repAddressRef_heapMono₂ addrTy)
          (ext_784_884.trans (ext_884_978.trans ext_1029)) hcm_rep_784)
        (fun i hi => by
          have hc_mem : ctors[i]'(by omega) ∈ nonrecs :=
            List.mem_append_right inds (List.getElem_mem (by omega))
          refine ⟨by rw [hκ_adv]; exact hf_ctor i hi,
            (hnr_info _ hc_mem).2.2.2.1, fun ext1 hsub1 hrep1 ev1 => ?_⟩
          rw [hκ_adv]
          exact (hctor_idx i hi).2 (ext_840_978.trans (ext_1029.trans ext1))
            (fun x hx => hsub1093 x (hsub1 x hx)) hrep1 ev1)
        (addrSet_mono ext_1029 haset_978)
        hren_adv_1029 ev1095
    have hren_adv_1083 : RenameMap c_adv.κ c_adv.κ f_id m1083 v926 v977 := by
      obtain ⟨sAs, dAs, hs, hd, hl, hm⟩ := hren_adv_1029
      exact ⟨sAs, dAs,
        RepLinkedList.mono (Bytes.repAddressRef_heapMono₂ addrTy) ext_1083 hs,
        RepLinkedList.mono (Bytes.repAddressRef_heapMono₂ addrTy) ext_1083 hd, hl, hm⟩
    obtain ⟨hmv_specs, ext_1137⟩ :=
      members_val_spec bridge.rolesSpec htwf_adv hex_adv hf_out
        recAs rmAs (rawSpecs.map RawRecSpec.toCI)
        (by simp [recAs, hrm_len]) (by simp [recAs]) (hg_adv.sub hsub1147)
        (RepLinkedList.mono (Bytes.repAddressRef_heapMono₂ addrTy)
          (ext_840_978.trans (ext_1029.trans ext_1083)) hrec_rep_840)
        (RepLinkedList.mono (Bytes.repAddressRef_heapMono₂ addrTy)
          (ext_884_978.trans (ext_1029.trans ext_1083)) hrm_rep_884)
        (fun i hi => by
          have hi_s : i < rawSpecs.length := by simpa [recAs] using hi
          have hs_mem : rawSpecs[i] ∈ rawSpecs := List.getElem_mem hi_s
          refine ⟨by rw [hκ_adv, List.getElem_map]; exact hf_spec i hi_s,
            by rw [List.getElem_map]; exact (hspec_info _ hs_mem).2.2.1,
            fun ext1 hsub1 hrep1 ev1 => ?_⟩
          rw [hκ_adv, List.getElem_map]
          dsimp only [recAs] at hrep1
          rw [List.getElem_map] at hrep1
          exact (hspec_idx i hi_s).2
            (ext_840_978.trans (ext_1029.trans (ext_1083.trans ext1)))
            (fun x hx => hsub1147 x (hsub1 x hx)) hrep1 ev1)
        (addrSet_mono (ext_1029.trans ext_1083) haset_978)
        hren_adv_1083 ev1149
    have hmv_nonrec : ∀ c ∈ nonrecs,
        c.toConstantVal.levelParams.Perm (List.range c.toConstantVal.levelParams.length) ∧
        ∃ cvm_f mval_f hint_f,
          c_adv.env.find? (f_id c.name) = some (.defnInfo cvm_f mval_f hint_f) ∧
          cvm_f.levelParams = List.range c.toConstantVal.levelParams.length ∧
          cvm_f.type =
            (posOf c.toConstantVal.levelParams c.toConstantVal.type).renameConsts f_id := by
      intro c hc
      rcases List.mem_append.mp hc with hi | hct
      · exact hmv_inds c hi
      · exact hmv_ctors c hct
    have hmv_spec : ∀ s ∈ rawSpecs,
        s.cv.levelParams.Perm (List.range s.cv.levelParams.length) ∧
        ∃ cvm_f mval_f hint_f,
          c_adv.env.find? (f_id s.cv.name) = some (.defnInfo cvm_f mval_f hint_f) ∧
          cvm_f.levelParams = List.range s.cv.levelParams.length ∧
          cvm_f.type = (posOf s.cv.levelParams s.cv.type).renameConsts f_id := by
      intro s hs
      exact hmv_specs s.toCI (List.mem_map_of_mem hs)
    -- 7. Build `c_pub`, `c_rhs`, `DeclStoreInv c_pub.env`, `DeclStoreInv c_rhs.env`
    let c_pub : Ctx := ⟨E, pushList (nonrecs.map posCI) env, t, lim⟩
    let rawRecs := zipRawSpecs rawSpecs rmAs
    let c_rhs : Ctx := ⟨E, pushList (rawRecs.map RawRecEntry.prov_p) c_pub.env, t, lim⟩
    have hnd_nr : (nonrecs.map (·.name)).Nodup := (List.nodup_append.mp hbn_nd).1
    have hnd_sp : (rawSpecs.map (·.cv.name)).Nodup := (List.nodup_append.mp hbn_nd).2.1
    have hdisj_nr_sp : ∀ x ∈ nonrecs.map (·.name), x ∉ rawSpecs.map (·.cv.name) :=
      fun x hx hy => (List.nodup_append.mp hbn_nd).2.2 x hx x hy rfl
    have hfr_env_nr : ∀ c ∈ nonrecs, env.find? c.name = none := by
      intro c hc
      obtain ⟨ci₀, hm₀, hnm⟩ := (hnr_info c hc).2.2.2.2
      rw [← hnm]; exact hfresh ci₀ hm₀
    have hfr_adv_nr : ∀ c ∈ nonrecs, c_adv.env.find? c.name = none := by
      intro c hc
      obtain ⟨ci₀, hm₀, hnm⟩ := (hnr_info c hc).2.2.2.2
      rw [← hnm]; exact hfr_inst_adv ci₀.name (List.mem_map_of_mem hm₀)
    have hfr_env_sp : ∀ s ∈ rawSpecs, env.find? s.cv.name = none := by
      intro s hs
      obtain ⟨ci₀, hm₀, hnm⟩ := (hspec_info s hs).2.2.2.2
      rw [← hnm]; exact hfresh ci₀ hm₀
    have hfr_adv_sp : ∀ s ∈ rawSpecs, c_adv.env.find? s.cv.name = none := by
      intro s hs
      obtain ⟨ci₀, hm₀, hnm⟩ := (hspec_info s hs).2.2.2.2
      rw [← hnm]; exact hfr_inst_adv ci₀.name (List.mem_map_of_mem hm₀)
    have hpos_nr_names : ∀ c ∈ nonrecs, (posCI c).name = c.name := by
      intro c hc
      rcases (hnr_info c hc).2.2.1 with ⟨_, rfl⟩ | ⟨_, _, _, rfl⟩ <;> rfl
    have hchain_nr0 : NonRecChain env c_adv.env f_id nonrecs :=
      build_nonRecChain hS_adv nonrecs env c_adv.env hnd_nr hfr_env_nr hfr_adv_nr
        (fun c hc => by
          obtain ⟨hb, hnres, hk, _, _⟩ := hnr_info c hc
          obtain ⟨hp, cvm_f, mval_f, hint_f, hfa, hlf, htf⟩ := hmv_nonrec c hc
          exact ⟨hb, hnres, hk, hp, cvm_f, mval_f, hint_f, hfa, hfa, hlf, htf⟩)
        hcr_nr
    have hS_pub : DeclStoreInv c_pub.env :=
      declStoreInv_push_pos_nonrecs nonrecs hnd_nr hS₀ (fun _ => rfl) hfr_env_nr hchain_nr0
    obtain ⟨hR_pub, hlf_pub, hex_pub, hg_pub⟩ := hctx_pub_fn hS_pub
    have hef_pub : EnvFacts c_pub := hS_pub.toEnvFacts htwf hR_pub
    have hfr_pub_sp : ∀ s ∈ rawSpecs, c_pub.env.find? s.cv.name = none := by
      intro s hs
      rw [find?_pushList_of_ne (nonrecs.map posCI) env s.cv.name fun cp hcp => by
        obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hcp
        rw [hpos_nr_names c hc]
        exact fun heq => hdisj_nr_sp c.name (List.mem_map_of_mem hc)
          (by rw [heq]; exact List.mem_map_of_mem hs)]
      exact hfr_env_sp s hs
    have hsome_nr_pos : ∀ k,
        ((pushList nonrecs env).find? k).isSome = (c_pub.env.find? k).isSome :=
      fun k => (isSome_pushList_posCI_iff nonrecs env k hpos_nr_names).symm
    have hS_rhs0 :
        DeclStoreInv (pushList (rawSpecs.map RawRecSpec.prov_p) c_pub.env) :=
      declStoreInv_push_pos_specs_prov rawSpecs hnd_sp hS_pub hfr_pub_sp fun s hs => by
        obtain ⟨hbase, _, _, hcr_s, _⟩ := hspec_info s hs
        obtain ⟨_, cvm_f, mval_f, hint_f, hf_adv, hlps_f, hty_f⟩ := hmv_spec s hs
        have hwf_f := hS_adv.store.wf _ (Ix.Kernel.Semantics.Env.find?_mem hf_adv)
        have htf : (posCV s.cv).type.hasFvar = false := by
          have h1 : ((posOf s.cv.levelParams s.cv.type).renameConsts f_id).hasFvar = false :=
            hty_f ▸ hwf_f.1
          rwa [hasFvar_renameConsts] at h1
        have htp : (posCV s.cv).type.allLevelParamsDefined (posCV s.cv).levelParams = true := by
          have h1 :
              ((posOf s.cv.levelParams s.cv.type).renameConsts f_id).allLevelParamsDefined
                (List.range s.cv.levelParams.length) = true :=
            hlps_f ▸ hty_f ▸ hwf_f.2.1
          rwa [allLevelParamsDefined_renameConsts] at h1
        have htr : (posCV s.cv).type.constsResolve c_pub.env = true := by
          have h1 : (posOf s.cv.levelParams s.cv.type).constsResolve (pushList nonrecs env) =
              true := by
            rw [constsResolve_posOf]; exact hcr_s
          exact constsResolve_congr_isSome (fun k hk => hsome_nr_pos k ▸ hk) _ h1
        have htb : (posCV s.cv).type.looseBVarsBounded 0 = true := by
          have h1 :
              ((posOf s.cv.levelParams s.cv.type).renameConsts f_id).looseBVarsBounded 0 = true :=
            hty_f ▸ hwf_f.2.2.2.1
          rwa [looseBVarsBounded_renameConsts] at h1
        exact ⟨hbase, htf, htp, htr, htb⟩
    have hrhs_env_eq :
        c_rhs.env = pushList (rawSpecs.map RawRecSpec.prov_p) c_pub.env := by
      dsimp only [c_rhs, rawRecs]
      rw [zipRawSpecs_map_prov_p rawSpecs rmAs hrm_len]
    have hS_rhs : DeclStoreInv c_rhs.env := hrhs_env_eq ▸ hS_rhs0
    obtain ⟨hR_rhs, hlf_rhs0, hg_rhs0⟩ := hctx_rhs_fn hS_rhs0
    have hlf_rhs : LoadFacts c_rhs := by
      show LoadFacts ⟨E, c_rhs.env, t, lim⟩
      rw [hrhs_env_eq]; exact hlf_rhs0
    have hg_rhs : Good c_rhs calls := by
      show Good ⟨E, c_rhs.env, t, lim⟩ calls
      rw [hrhs_env_eq]; exact hg_rhs0
    have hef_rhs : EnvFacts c_rhs :=
      hS_rhs.toEnvFacts htwf (by show CtxRoleFacts ⟨E, c_rhs.env, t, lim⟩; rw [hrhs_env_eq]; exact hR_rhs)
    -- 8. Run `check_recs_spec` (`ev1343`)
    have ext_1137_1293 : Heap.Extends m1137 m1293 :=
      (ObsFn.heap_extends ev1203).trans
        ((ObsFn.heap_extends ev1267).trans
          ((ObsFn.heap_extends ev1246).trans (ObsFn.heap_extends ev1305)))
    have ext_978_1293 : Heap.Extends m978 m1293 :=
      ext_1029.trans (ext_1083.trans (ext_1137.trans ext_1137_1293))
    have ext_884_1293 : Heap.Extends m884 m1293 := ext_884_978.trans ext_978_1293
    have ext_840_1293 : Heap.Extends m840 m1293 := ext_840_884.trans ext_884_1293
    have ext_mb_1293 : Heap.Extends m_mb m1293 :=
      ext_mb_423.trans (ext_453.trans (ext_453_978.trans ext_978_1293))
    have hproj_rhs : ∀ sn i entry, c_rhs.env.findProj? sn i = some entry →
        blockNames.contains sn = false := by
      intro sn i entry hfp
      have hfp1 : c_rhs.env.findProj? sn i = c_pub.env.findProj? sn i := by
        rw [hrhs_env_eq]
        exact findProj_pushList_base (rawSpecs.map RawRecSpec.prov_p) c_pub.env sn i fun cp hcp => by
          obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hcp
          exact (hspec_info s hs).1
      have hfp2 : c_pub.env.findProj? sn i = env.findProj? sn i :=
        findProj_pushList_base (nonrecs.map posCI) env sn i fun cp hcp => by
          obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hcp
          rw [hpos_nr_names c hc]; exact (hnr_info c hc).1
      rw [hfp1, hfp2] at hfp
      cases hcon : blockNames.contains sn with
      | false => rfl
      | true =>
        have hmem_bn : sn ∈ blockNames := List.mem_of_elem_eq_true hcon
        have hbf : isBaseKey sn = true ∧ env.find? sn = none := by
          rcases List.mem_append.mp hmem_bn with hnr_m | hsp_m
          · obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hnr_m
            exact ⟨(hnr_info c hc).1, hfr_env_nr c hc⟩
          · obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hsp_m
            exact ⟨(hspec_info s hs).1, hfr_env_sp s hs⟩
        have hnone := hAux₀.fresh_projTable hbf.1 hbf.2
        unfold Env.findProj? at hfp
        rw [hnone] at hfp
        exact nomatch hfp
    have hren_1293 : RenameMap c_pub.κ c_pub.κ f_id m1293 v926 v977 := by
      obtain ⟨sAs, dAs, hs, hd, hl, hm⟩ := hren_978
      exact ⟨sAs, dAs,
        RepLinkedList.mono (Bytes.repAddressRef_heapMono₂ addrTy) ext_978_1293 hs,
        RepLinkedList.mono (Bytes.repAddressRef_heapMono₂ addrTy) ext_978_1293 hd, hl, hm⟩
    have hraws_rec_rep :
        RepList addrListEnum (Bytes.RepAddressRef addrTy) m1293 (rawRecs.map (·.a_rec)) v839 := by
      dsimp only [rawRecs]
      rw [zipRawSpecs_map_a_rec rawSpecs rmAs hrm_len]
      exact RepLinkedList.mono (Bytes.repAddressRef_heapMono₂ addrTy) ext_840_1293 hrec_rep_840
    have hraws_rm_rep :
        RepList addrListEnum (Bytes.RepAddressRef addrTy) m1293 (rawRecs.map (·.a_rm))
          x_rec_models := by
      dsimp only [rawRecs]
      rw [zipRawSpecs_map_a_rm rawSpecs rmAs hrm_len]
      exact RepLinkedList.mono (Bytes.repAddressRef_heapMono₂ addrTy) ext_884_1293 hrm_rep_884
    obtain ⟨recs, _, hcv_map, hpr_map, hpp_map, hf2_recs, hw_all, _, _⟩ :=
      check_recs_spec (c_pub := c_pub) (c_rhs := c_rhs) (c_adv := c_adv)
        hCore bridge.rolesSpec bridge.calleesSpec
        rfl rfl ht_adv hlim_adv
        hef_pub hlf_pub hex_pub hef_rhs hlf_rhs hef_adv hlf_adv hex_adv
        hf_out hproj_rhs
        (fun k cvj cnP cnF hf => (hc_wf k cvj cnP cnF hf).2.1)
        rawRecs
        (hg_pub.sub hsub1341) (hg_rhs.sub hsub1341) (hg_adv.sub hsub1341)
        (hrc_mb.mono ext_mb_1293)
        hraws_rec_rep hraws_rm_rep
        (addrSet_mono ext_978_1293 haset_978)
        hren_1293
        (hs8.mono ext_884_1293)
        (fun e he => by
          obtain ⟨i, hi_r, he_eq⟩ := List.mem_iff_getElem.mp he
          have hi_s : i < rawSpecs.length := by
            simpa [rawRecs, zipRawSpecs_length rawSpecs rmAs hrm_len] using hi_r
          have hget := zipRawSpecs_getElem rawSpecs rmAs hrm_len i hi_s
          rw [hget] at he_eq
          subst he_eq
          have hs_mem : rawSpecs[i] ∈ rawSpecs := List.getElem_mem hi_s
          refine ⟨hf_spec i hi_s, (hspec_info _ hs_mem).2.2.1,
            hspec_canonical _ hs_mem, fun ext1 hsub1 hrep1 ev1 => ?_⟩
          exact (hspec_idx i hi_s).2 (ext_840_1293.trans ext1)
            (fun x hx => hsub1341 x (hsub1 x hx)) hrep1 ev1)
        ev1343
    -- 9. Assemble `ModeledBlockWitness`
    have hrec_cvs_eq : recs.map (·.cv) = rawSpecs.map (·.cv) :=
      hcv_map.trans (zipRawSpecs_map_cv rawSpecs rmAs hrm_len)
    have hrec_names_eq : recs.map (·.cv.name) = rawSpecs.map (·.cv.name) := by
      have h1 := congrArg (List.map (·.name)) hrec_cvs_eq
      simpa [List.map_map, Function.comp_def] using h1
    have hbn_recs_eq : (nonrecs.map (·.name)) ++ (recs.map (·.cv.name)) = blockNames := by
      simp only [blockNames, hrec_names_eq]
    have hrec_to_spec : ∀ w ∈ recs, ∃ s ∈ rawSpecs,
        w.cv = s.cv ∧ w.mI = s.mI ∧ w.rP = s.rP ∧ w.rawRules = s.rawRules := by
      intro w hw
      obtain ⟨e, he_mem, hw_eq⟩ := forall₂_mem_right hf2_recs w hw
      obtain ⟨i, hi_r, he_eq⟩ := List.mem_iff_getElem.mp he_mem
      have hi_s : i < rawSpecs.length := by
        simpa [rawRecs, zipRawSpecs_length rawSpecs rmAs hrm_len] using hi_r
      rw [zipRawSpecs_getElem rawSpecs rmAs hrm_len i hi_s] at he_eq
      subst he_eq
      exact ⟨rawSpecs[i], List.getElem_mem hi_s, hw_eq⟩
    have hspec_to_rec : ∀ s ∈ rawSpecs, ∃ w ∈ recs,
        w.cv = s.cv ∧ w.mI = s.mI ∧ w.rP = s.rP ∧ w.rawRules = s.rawRules := by
      intro s hs
      obtain ⟨i, hi_s, rfl⟩ := List.mem_iff_getElem.mp hs
      have he_mem : (zipRawSpecs rawSpecs rmAs)[i]'(by
          rw [zipRawSpecs_length rawSpecs rmAs hrm_len]; exact hi_s) ∈ rawRecs :=
        List.getElem_mem _
      obtain ⟨w, hw_mem, hw_eq⟩ := forall₂_mem_left hf2_recs _ he_mem
      rw [zipRawSpecs_getElem rawSpecs rmAs hrm_len i hi_s] at hw_eq
      exact ⟨w, hw_mem, hw_eq⟩
    -- Shared helper for `env_iota` bridges (`hchains`, `hfind_pub_M`, `hrecs_rules`)
    have hiota_bridges : ∀ (env_iota : Env .anon),
        EnvExt c_adv.env env_iota →
        (∀ k, (∀ w ∈ recs, ∀ j, k ≠ auxKey (auxKey w.cv.name .model) (.iota j)) →
          env_iota.find? k = c_adv.env.find? k) →
        NonRecChain env env_iota f_id nonrecs ∧
        RecProvChain (pushList nonrecs env) (pushList (nonrecs.map posCI) env_iota) f_id recs ∧
        (∀ k ci, c_pub.env.find? k = some ci →
          (pushList (nonrecs.map posCI) env_iota).find? k = some ci) ∧
        EnvExt c_pub.env
          (pushList (recs.map (·.prov_p)) (pushList (nonrecs.map posCI) env_iota)) ∧
        EnvExt c_rhs.env
          (pushList (recs.map (·.prov_p)) (pushList (nonrecs.map posCI) env_iota)) := by
      intro env_iota hext_iota hout_iota
      have hfr_iota_nr : ∀ c ∈ nonrecs, env_iota.find? c.name = none := by
        intro c hc
        rw [hout_iota c.name fun _ _ _ => ne_auxKey_of_isBaseKey (hnr_info c hc).1]
        exact hfr_adv_nr c hc
      have hfr_iota_rec : ∀ w ∈ recs, env_iota.find? w.cv.name = none := by
        intro w hw
        obtain ⟨s, hs, hcv_eq, _, _, _⟩ := hrec_to_spec w hw
        rw [hcv_eq, hout_iota s.cv.name fun _ _ _ => ne_auxKey_of_isBaseKey (hspec_info s hs).1]
        exact hfr_adv_sp s hs
      have hnr_chain : NonRecChain env env_iota f_id nonrecs :=
        build_nonRecChain hS_adv nonrecs env env_iota hnd_nr hfr_env_nr hfr_iota_nr
          (fun c hc => by
            obtain ⟨hb, hnres, hk, _, _⟩ := hnr_info c hc
            obtain ⟨hp, cvm_f, mval_f, hint_f, hfa, hlf, htf⟩ := hmv_nonrec c hc
            exact ⟨hb, hnres, hk, hp, cvm_f, mval_f, hint_f, hfa, hext_iota.find hfa, hlf, htf⟩)
          hcr_nr
      have hnd_pos_nr : ((nonrecs.map posCI).map (·.name)).Nodup := by
        have hmap : (nonrecs.map posCI).map (·.name) = nonrecs.map (·.name) := by
          rw [List.map_map]
          exact List.map_congr_left fun c hc => hpos_nr_names c hc
        rwa [hmap]
      obtain ⟨hfind_pub_Mp, hext_pub_Mp⟩ :=
        envExt_pushList_shared (nonrecs.map posCI) (hadv_step.ext.trans hext_iota) hnd_pos_nr
          (fun cp hcp => by
            obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hcp
            rw [hpos_nr_names c hc]; exact hfr_env_nr c hc)
          (fun cp hcp => by
            obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hcp
            rw [hpos_nr_names c hc]; exact hfr_iota_nr c hc)
          (fun cp hcp T => by
            obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hcp
            rw [hpos_nr_names c hc]; exact ne_projTableName_of_isBaseKey (hnr_info c hc).1)
          (fun cp hcp => Or.inr (by
            obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hcp
            rw [hpos_nr_names c hc]
            have hb : isBaseKey c.name = true := (hnr_info c hc).1
            refine ⟨hAux₀.fresh_projTable hb (hfr_env_nr c hc), ?_⟩
            rw [hout_iota (projTableName c.name) fun w _ j =>
              (ne_projTableName_auxKey_iota (auxKey w.cv.name .model) c.name j).symm]
            exact hAux_adv.fresh_projTable hb (hfr_adv_nr c hc)))
      have hnd_rec : (recs.map (·.cv.name)).Nodup := hrec_names_eq ▸ hnd_sp
      have hfr_M_r : ∀ w ∈ recs, (pushList nonrecs env).find? w.cv.name = none := by
        intro w hw
        obtain ⟨s, hs, hcv_eq, _, _, _⟩ := hrec_to_spec w hw
        rw [hcv_eq, find?_pushList_of_ne nonrecs env s.cv.name fun c hc heq =>
          hdisj_nr_sp c.name (List.mem_map_of_mem hc) (by rw [heq]; exact List.mem_map_of_mem hs)]
        exact hfr_env_sp s hs
      have hfr_M_p : ∀ w ∈ recs,
          (pushList (nonrecs.map posCI) env_iota).find? w.cv.name = none := by
        intro w hw
        obtain ⟨s, hs, hcv_eq, _, _, _⟩ := hrec_to_spec w hw
        rw [find?_pushList_of_ne (nonrecs.map posCI) env_iota w.cv.name fun cp hcp => by
          obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hcp
          rw [hpos_nr_names c hc, hcv_eq]
          exact fun heq => hdisj_nr_sp c.name (List.mem_map_of_mem hc)
            (by rw [heq]; exact List.mem_map_of_mem hs)]
        exact hfr_iota_rec w hw
      have hrec_chain :
          RecProvChain (pushList nonrecs env) (pushList (nonrecs.map posCI) env_iota) f_id recs :=
        build_recProvChain hS_adv recs (pushList nonrecs env)
          (pushList (nonrecs.map posCI) env_iota) hnd_rec hfr_M_r hfr_M_p fun w hw => by
          obtain ⟨s, hs, hcv_eq, _, _, _⟩ := hrec_to_spec w hw
          obtain ⟨hb, hnres, _, hcr_s, _⟩ := hspec_info s hs
          obtain ⟨hp, cvm_f, mval_f, hint_f, hfa, hlf, htf⟩ := hmv_spec s hs
          rw [← hcv_eq] at hb hnres hcr_s hp hfa hlf htf
          have hfp : (pushList (nonrecs.map posCI) env_iota).find? (f_id w.cv.name) =
              some (.defnInfo cvm_f mval_f hint_f) := by
            rw [find?_pushList_of_ne (nonrecs.map posCI) env_iota (f_id w.cv.name) fun cp hcp => by
              obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hcp
              rw [hpos_nr_names c hc]
              intro heq
              have hnone := hfr_adv_nr c hc
              rw [heq, hfa] at hnone
              exact nomatch hnone]
            exact hext_iota.find hfa
          exact ⟨hb, hnres, hp, hcr_s, cvm_f, mval_f, hint_f, hfa, hfp, hlf, htf⟩
      have hnd_prov_p : ((recs.map (·.prov_p)).map (·.name)).Nodup := by
        have hmap : (recs.map (·.prov_p)).map (·.name) = recs.map (·.cv.name) := by
          rw [List.map_map]; rfl
        rwa [hmap]
      have hfr_pub_rec : ∀ w ∈ recs, c_pub.env.find? w.cv.name = none := by
        intro w hw
        obtain ⟨s, hs, hcv_eq, _, _, _⟩ := hrec_to_spec w hw
        rw [hcv_eq]; exact hfr_pub_sp s hs
      have hnpt_prov_p : ∀ cp ∈ recs.map (·.prov_p), ∀ T, cp.name ≠ projTableName T := by
        intro cp hcp T
        obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hcp
        obtain ⟨s, hs, hcv_eq, _, _, _⟩ := hrec_to_spec w hw
        show w.cv.name ≠ projTableName T
        rw [hcv_eq]; exact ne_projTableName_of_isBaseKey (hspec_info s hs).1
      have hext_Mp_Sp :
          EnvExt (pushList (nonrecs.map posCI) env_iota)
            (pushList (recs.map (·.prov_p)) (pushList (nonrecs.map posCI) env_iota)) :=
        envExt_pushList_fresh_base (recs.map (·.prov_p)) hnd_prov_p
          (fun cp hcp => by
            obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hcp
            exact hfr_M_p w hw)
          hnpt_prov_p
      obtain ⟨_, hext_rhs_Sp0⟩ :=
        envExt_pushList_shared (recs.map (·.prov_p)) hext_pub_Mp hnd_prov_p
          (fun cp hcp => by
            obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hcp
            exact hfr_pub_rec w hw)
          (fun cp hcp => by
            obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hcp
            exact hfr_M_p w hw)
          hnpt_prov_p
          (fun cp hcp => by
            obtain ⟨w, _, rfl⟩ := List.mem_map.mp hcp
            exact Or.inl fun _ _ h => nomatch h)
      have hrhs_recs_eq : c_rhs.env = pushList (recs.map (·.prov_p)) c_pub.env := by
        dsimp only [c_rhs]; rw [hpp_map]
      exact ⟨hnr_chain, hrec_chain, hfind_pub_Mp, hext_pub_Mp.trans hext_Mp_Sp,
        hrhs_recs_eq ▸ hext_rhs_Sp0⟩
    have hsome_rhs_to_real : ∀ k,
        (c_rhs.env.find? k).isSome =
          ((pushList (recs.map (·.prov_r)) (pushList nonrecs env)).find? k).isSome := by
      intro k
      have hrhs_recs_eq : c_rhs.env = pushList (recs.map (·.prov_p)) c_pub.env := by
        dsimp only [c_rhs]; rw [hpp_map]
      rw [hrhs_recs_eq]
      exact isSome_pushList_prov_iff recs c_pub.env (pushList nonrecs env) k
        (fun x => isSome_pushList_posCI_iff nonrecs env x hpos_nr_names)
    refine ⟨{
      c_pub := c_pub
      c_rhs := c_rhs
      c_adv := c_adv
      f_id := f_id
      advSet := fun b => b ∈ advAs
      nonrecs := nonrecs
      recs := recs
      hadv_step := hadv_step
      hnames_nodup := hbn_recs_eq ▸ hbn_nd
      hnames_fresh_adv := fun k hk => by
        rw [hbn_recs_eq] at hk
        rcases List.mem_append.mp hk with hnr_m | hsp_m
        · obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hnr_m
          exact hfr_adv_nr c hc
        · obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hsp_m
          exact hfr_adv_sp s hs
      hcov_installs := fun ci₀ hm₀ => by
        rcases hcov_raw ci₀ hm₀ with hnr_c | ⟨s, hs, hst⟩
        · exact Or.inl hnr_c
        · obtain ⟨w, hw, hcv_w, hmI_w, hrP_w, hrls_w⟩ := hspec_to_rec s hs
          have htoCI_eq : ConstantInfo.recInfo w.cv w.mI w.rP w.rawRules = s.toCI := by
            simp only [RawRecSpec.toCI, hcv_w, hmI_w, hrP_w, hrls_w]
          rw [← htoCI_eq] at hst
          exact Or.inr ⟨w, hw, storedAs_checked_r hst⟩
      hin_installs_nonrec := fun c hc => (hnr_info c hc).2.2.2.2
      hin_installs_rec := fun w hw => by
        obtain ⟨s, hs, hcv_w, _, _, _⟩ := hrec_to_spec w hw
        rw [hcv_w]; exact (hspec_info s hs).2.2.2.2
      hf_out := fun k hk => hf_out k (hbn_recs_eq ▸ hk)
      hchains := fun env_iota hext_iota hout_iota => by
        obtain ⟨hc1, hc2, _, _, _⟩ := hiota_bridges env_iota hext_iota hout_iota
        exact ⟨hc1, hc2⟩
      hctor_pub_wf := fun ck cvj cnP cnF hf => by
        obtain ⟨hlp, _, hmr, hhd⟩ := hc_wf ck cvj cnP cnF hf
        exact ⟨hlp, hmr, hhd⟩
      hfind_pub_M := fun env_iota hext_iota hout_iota => by
        obtain ⟨_, _, hfM, hextM, _⟩ := hiota_bridges env_iota hext_iota hout_iota
        exact ⟨hfM, hextM⟩
      hrecs_rules := fun w hw => by
        obtain ⟨_, hrp_le, hstrip, hdom_fn, hdom_len, hdom_nli, hdom_drop,
            hpins, hrls_facts, hraw_run⟩ := hw_all w hw
        obtain ⟨s, hs, hcv_w, _, _, _⟩ := hrec_to_spec w hw
        have hw_perm : w.cv.levelParams.Perm (List.range w.cv.levelParams.length) := by
          rw [hcv_w]; exact (hmv_spec s hs).1
        refine ⟨hrp_le, hstrip, hdom_fn, hdom_len, hdom_nli, hdom_drop, hpins, ?_, ?_,
          hbn_recs_eq.symm ▸ hraw_run⟩
        · intro r hr
          obtain ⟨hnl, hcr_rhs, _⟩ := hrls_facts r hr
          exact ⟨hnl,
            constsResolve_congr_isSome (fun k hk => hsome_rhs_to_real k ▸ hk) _ hcr_rhs⟩
        · intro env_iota hext_iota hout_iota r hr t' hinf
          obtain ⟨_, _, _, _, hext_rhs_Sp⟩ := hiota_bridges env_iota hext_iota hout_iota
          exact ⟨posOf w.cv.levelParams t',
            posRulesJ_infer_weaken hext_rhs_Sp (posRulesJ_infer_posOf hw_perm hinf)⟩
    }⟩

/-! ## Section 5: Modeled Dispatch, Native Seam, & Top-Level `Decls S₀` / `L5 S₀` -/

/-- Loader (L1), role/callee (L6), and assembly (L7) witness for a modeled inductive declaration
`.indDecl block₀ nP`: exhibits a checked safe `"Induct"` member whose `KernelCheck::check_const`
derivation does not take the native `block_is_modeled = 0` branch, together with a
`check_modeled_block` observation and its `ModeledFamilyBridge`.

The inductive arm of `check_const` no longer runs the family check on a modeled block (it checks
the declared shape only), so the observation is part of the seam, not derived from the member's
check. `check_modeled_block` has no caller in the program, so no run supplies one: this seam is
not inhabited for a modeled block, and the legacy step below no longer covers modeled inductives.
The route is superseded; the family check is reached from the recursor arm only. -/
structure DeclModeledExtraFacts (calls : List (Call F)) (env : Env .anon)
    (block₀ : List (ConstantInfo .anon)) (nP : Nat) : Prop where
  installsNodup : ((IxVM.Consistency.installs (.indDecl block₀ nP)).map (·.name)).Nodup
  installsFresh :
    ∀ ci₀ ∈ IxVM.Consistency.installs (.indDecl block₀ nP), env.find? ci₀.name = none
  modeledWitness :
    ∃ (E : Ixon.Env) (t : Ix.Kernel.RoleTable) (lim : Option Nat)
      (cl : Call F) (rc nl ty np ni nct iblk iidx ap r_cl : SourceValue F)
      (h'_cl : Heap F) (subcalls : List (Call F)),
      t.wf = true ∧
      cl ∈ calls ∧
      RCRep t lim cl.heap rc ∧
      ObsFn W "KernelCheck::check_const"
        [rc, .construct kciEnum "Induct" [nl, ty, np, ni, nct, .field 0, iblk, iidx], ap]
        cl.heap r_cl h'_cl subcalls ∧
      (∀ x ∈ subcalls, x ∈ calls) ∧
      (∀ (m_bm1 m_bm2 : Heap F) (cs_bm : List (Call F)),
        Heap.Extends cl.heap m_bm1 → (∀ x ∈ cs_bm, x ∈ calls) →
        ¬ ObsFn W "KernelModeled::block_is_modeled" [iblk] m_bm1 (.field 0) m_bm2 cs_bm) ∧
      ∃ (m_mb : Heap F) (r_mb : SourceValue F) (h'_mb : Heap F) (cs_mb : List (Call F)),
        Heap.Extends cl.heap m_mb ∧
        ObsFn W "KernelModeled::check_modeled_block" [rc, iblk] m_mb r_mb h'_mb cs_mb ∧
        (∀ x ∈ cs_mb, x ∈ calls) ∧
        ModeledFamilyBridge.{u} calls env block₀ nP E t lim rc iblk m_mb cs_mb

/-- **Modeled Inductive Declaration Step Theorem (`L5-M`)**: combines the seam's
`check_modeled_block` observation, `modeledBlockWitness_of_check_family` and
`modeledBlock_install_step` to step `DeclInvM` across a modeled `.indDecl block₀ nP`. Legacy: see
`DeclModeledExtraFacts`. -/
theorem modeledIndDecl_step (hCore : IxVM.Consistency.Core S₀)
    {calls : List (Call F)} {env : Env .anon}
    {block₀ : List (ConstantInfo .anon)} {nP : Nat}
    (hchk : S0.Checked calls env (.indDecl block₀ nP))
    (hx : DeclModeledExtraFacts.{u} calls env block₀ nP) :
    ∃ env₂, CleanInstallStep env (.indDecl block₀ nP) env₂ ∧
      ∀ (V : Type u) [Ix.Kernel.SetTheory V], DeclInvM V env → DeclInvM V env₂ := by
  obtain ⟨E, t, lim, cl, rc, nl, ty, np, ni, nct, iblk, iidx, ap, r_cl, h'_cl, subcalls,
      htwf, _, hrc, ev_chk, hsub, hnot_native, m_mb, r_mb, h'_mb, cs_mb, ext_mb, ev_mb,
      hsub_mb', bridge⟩ :=
    hx.modeledWitness
  exact modeledBlock_install_step hchk hx.installsNodup hx.installsFresh
    (modeledBlockWitness_of_check_family hCore htwf (hrc.mono ext_mb) hsub_mb'
      hx.installsFresh ev_mb bridge)

/-- Combined per-declaration seam assumptions owed by L1/L6/L7 (and `L5-N` for native inductive
blocks). -/
structure DeclExtraFacts (calls : List (Call F)) (env : Env .anon)
    (d : Declaration .anon) : Prop where
  valueFacts : DeclValueExtraFacts calls env d
  unpinnedInd :
    ∀ block₀ nP, d = .indDecl block₀ nP → Ix.Kernel.basisPinHit block₀ = none → block₀ ≠ [] →
      DeclModeledExtraFacts.{u} calls env block₀ nP ∨ NativeIndStep.{u} calls env block₀ nP

/-- Global seam hypothesis supplying `DeclExtraFacts` for every `S0.Checked` declaration in a
bounded call trace. -/
def AllDeclExtraFacts : Prop :=
  ∀ (calls : List (Call F)) (env : Env .anon) (d : Declaration .anon),
    IxVM.Consistency.Bounded calls → S0.Checked calls env d → DeclExtraFacts.{u} calls env d

/-- **Unified `DeclInvM` step preservation across all declarations** (`L5-V` + `L5-M` +
`NativeIndStep`). -/
theorem decl_step_S₀ (hLevels : IxVM.Consistency.Levels)
    (hCore : IxVM.Consistency.Core S₀)
    {calls : List (Call F)} {env : Env .anon} {d : Declaration .anon}
    (hchk : S0.Checked calls env d)
    (hx : DeclExtraFacts.{u} calls env d) :
    ∃ env₂, CleanInstallStep env d env₂ ∧
      ∀ (V : Type u) [Ix.Kernel.SetTheory V], DeclInvM V env → DeclInvM V env₂ :=
  valueOrPinnedDecl_step_M hLevels hCore hchk hx.valueFacts fun block₀ nP hd hpin => by
    cases block₀ with
    | nil =>
      have hempty : IxVM.Consistency.installs (.indDecl [] nP) = [] := by
        simp [IxVM.Consistency.installs, hpin]
      exact ⟨env, CleanInstallStep.empty hempty, fun _ _ h => h⟩
    | cons c₀ rest =>
      rcases hx.unpinnedInd (c₀ :: rest) nP hd hpin (List.cons_ne_nil c₀ rest) with hmod | hnat
      · exact modeledIndDecl_step hCore (hd ▸ hchk) hmod
      · exact hnat

/-- **`IxVM.Consistency.Decls.{u} S₀`** witnessed by `DeclInvM`. -/
theorem l5_decls_S₀ (hLevels : IxVM.Consistency.Levels)
    (hCore : IxVM.Consistency.Core S₀)
    (hExtra : AllDeclExtraFacts.{u}) :
    IxVM.Consistency.Decls.{u} S₀ :=
  ⟨fun (V : Type u) [Ix.Kernel.SetTheory V] (env : Env .anon) => DeclInvM V env,
    fun V _ => DeclInvM.empty V,
    fun _ _ _ h => h.toEnvModelOk,
    fun calls env d hbnd hchk =>
      let ⟨env₂, hclean, hstep⟩ := decl_step_S₀ hLevels hCore hchk (hExtra calls env d hbnd hchk)
      ⟨env₂, hclean.step, hstep⟩⟩

/-- **Top-level Obligation `L5` at `S₀`** (`IxVM.Consistency.L5.{u} S₀`). -/
theorem l5_S₀ (hExtra : AllDeclExtraFacts.{u}) :
    IxVM.Consistency.L5.{u} S₀ :=
  fun _ hLevels _ hCore => l5_decls_S₀ hLevels hCore hExtra

end IxVM.Refinement.Decl
