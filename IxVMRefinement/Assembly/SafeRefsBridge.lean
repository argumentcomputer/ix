import IxVMRefinement.Assembly.RolePreludeBridge
import IxVMRefinement.Assembly.ProjSafe
import IxVMRefinement.Assembly.RecordReadBare
import IxC.Kernel.Verify.Frontend.Prepare
import IxC.Ixon.Verify.ConstantBounds

/-! # Safe-reference validation, constructor index checking, and role-prefix bridge (`SafeRefsBridge`)

Proves the standalone unconditional components of `SafeRefsInputs` and isolates the residual
circuit and interface boundary obligations on `ProjSafe` into `SafeExprRefsGap`:

1. **Constructor index consistency (`iprj_store_eq_of_mutsMemberChecked`,
   `check_inductive_shape_ctors_cidx`, `check_modeled_ctors_cidx`,
   `indBlockCtorIdx_of_exact_noCollision`)**:
   - Unconditionally proves `ct.cidx.toNat = j` for `ind.ctors[j]? = some ct` on any safe walked
     mutual inductive block in an exact-decoded collision-free store `E₀`, covering both the
     native (`check_inductive_shape_ctors`) and modeled (`check_modeled_ctors`) paths of
     `KernelCheck::check_const`.
2. **`KernelCheck::safe_refs_only` unconditional theorems (`safe_refs_only_raw_spec`,
   `safe_refs_only_refOnly_resolve`)**:
   - Evaluates to `.field 0` or `.field 1` while monotonically extending the heap on any
     `L1.RawConvExpr`.
   - Along `.ref`-only reachable reference indices (`reachRefOnlyExpr`, matching
     `KernelCheck::safe_refs_only` where `KExprNode::Proj` recurses on `e1`), every referenced
     constant in an exact-decoded collision-free store `E₀` satisfies `L1.ConstantTablesValid`
     and is never a `.muts` block; every standalone record (`ownerOf a c_a = a`) satisfies
     `¬ OutsideLogicAt E₀ a` and `(resolveSource (recordAt E₀) a c_a).isSome = true`; every
     `.dPrj`/`.iPrj`/`.rPrj` projection whose owning block is stored in `E₀` satisfies
     `(resolveSource (recordAt E₀) a c_a).isSome = true`; and every `.cPrj` projection whose
     owning block is safe and walked in `E₀` satisfies both `¬ OutsideLogicAt E₀ a` and
     `(resolveSource (recordAt E₀) a c_a).isSome = true`.
3. **Role-prefix order & `preparePrelude` splitting (`order_filter_role_eq_of_subset`,
   `usedCompiledReach_role_subset`, `frontOf_append_nonPrelude`,
   `preparePrelude_append_of_hoist_empty`)**:
   - Unconditionally proves `order.filter (· ∈ order_role) = order_role` whenever `order_role`
     embeds into `order` with monotone indices, proves reachability embedding under
     `RecursorEdge` preservation, and proves `frontOf` suffix preservation for non-role walked
     declarations (`x ∉ order_role`).
4. **Minimal residual isolation (`SafeExprRefsGap`, `safeRefsInputs`)**:
   - Isolates the exact circuit and interface boundary obligations (`KExprNode::Proj` skipping
     `taddr` in `KernelCheck::safe_refs_only`, `ProjSafe` signature omissions, and bare role/indRec
     lowering) and discharges `SafeRefsInputs`. -/

set_option maxHeartbeats 1600000

namespace IxVM.Refinement.Assembly

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open IxVM (F)

/-! ## Section 0: Store Agreement & Table Helpers -/

private theorem field_zero_ne_one : (Value.field (0 : F) : SourceValue F) ≠ .field 1 := by
  intro h
  injection h with h01
  exact zero_ne_one h01

private theorem sub_one_bool_dichot {y r : SourceValue F}
    (hy : y = .field 0 ∨ y = .field 1)
    (op : evalBinOp .sub (.field 1 : SourceValue F) y = .ok r) :
    (r = .field 0 ∨ r = .field 1) ∧ (r = .field 1 → y = .field 0) := by
  rcases hy with rfl | rfl
  · simp only [evalBinOp, sub_zero, Except.ok.injEq] at op
    exact ⟨Or.inr op.symm, fun _ => rfl⟩
  · simp only [evalBinOp, sub_self, Except.ok.injEq] at op
    refine ⟨Or.inl op.symm, fun hr1 => ?_⟩
    exact absurd (op.trans hr1) field_zero_ne_one

private theorem mul_bool_dichot {x y r : SourceValue F}
    (hx : x = .field 0 ∨ x = .field 1)
    (hy : y = .field 0 ∨ y = .field 1)
    (op : evalBinOp .mul x y = .ok r) :
    (r = .field 0 ∨ r = .field 1) ∧ (r = .field 1 → x = .field 1 ∧ y = .field 1) := by
  rcases hx with rfl | rfl
  · rcases hy with rfl | rfl
    · simp only [evalBinOp, mul_zero, Except.ok.injEq] at op
      exact ⟨Or.inl op.symm, fun hr1 => absurd (op.trans hr1) field_zero_ne_one⟩
    · simp only [evalBinOp, zero_mul, Except.ok.injEq] at op
      exact ⟨Or.inl op.symm, fun hr1 => absurd (op.trans hr1) field_zero_ne_one⟩
  · rcases hy with rfl | rfl
    · simp only [evalBinOp, mul_zero, Except.ok.injEq] at op
      exact ⟨Or.inl op.symm, fun hr1 => absurd (op.trans hr1) field_zero_ne_one⟩
    · simp only [evalBinOp, mul_one, Except.ok.injEq] at op
      exact ⟨Or.inr op.symm, fun _ => ⟨rfl, rfl⟩⟩

/-- In an exact-decoded environment `E₀` loaded by `calls` with no hash collision, any hashed
bytes at address `x` decoding via `deConstantExact` to `c_ld` must match `Ix.Cert.recordAt E₀ x`. -/
theorem loaded_recordAt_eq_of_exact_noCollision
    {calls cs_ld : List (Call F)} {E₀ : Ixon.Env} {V : IxVM.Refinement.View}
    {extra : List ByteArray} {x : _root_.Address} {bytes : ByteArray}
    {c₀ c_ld : Ixon.Constant}
    (hexact₀ : L1.EnvDecoded E₀)
    (hload₀ : IxVM.Consistency.LoadedBy calls E₀)
    (hnoCol : ¬ V.HashedCollision extra calls)
    (hrec₀ : Ix.Cert.recordAt E₀ x = some c₀)
    (hhash : Hashed cs_ld bytes)
    (hsub : ∀ cl ∈ cs_ld, cl ∈ calls)
    (hblake : _root_.Address.blake3Pure bytes = x)
    (hdec : Ixon.deConstantExact bytes = .ok c_ld) :
    c₀ = c_ld := by
  have ⟨lc₀, hget₀, hlc₀⟩ : ∃ lc₀, E₀.consts.get? x = some lc₀ ∧ lc₀.get? = some c₀ := by
    unfold Ix.Cert.recordAt at hrec₀
    cases hg : E₀.consts.get? x with
    | none => rw [hg] at hrec₀; cases hrec₀
    | some lc₀ => rw [hg] at hrec₀; exact ⟨lc₀, rfl, hrec₀⟩
  obtain ⟨c₀', hlc₀', hexact₀'⟩ := hexact₀ x lc₀ hget₀
  have hc_eq : c₀ = c₀' := Option.some.inj (hlc₀.symm.trans hlc₀')
  subst hc_eq
  obtain ⟨hhash₀, hblake₀⟩ := hload₀.1 x lc₀ hget₀
  have hhash_calls : Hashed calls bytes := Core.hashed_mono hsub hhash
  have hraw_eq : lc₀.rawBytes = bytes := by
    by_cases heq : lc₀.rawBytes = bytes
    · exact heq
    · exact absurd (.inl ⟨x, lc₀.rawBytes, bytes,
        .inr (.inr ⟨hhash₀, hblake₀⟩), hhash_calls, Ne.symm heq, hblake⟩) hnoCol
  rw [hraw_eq] at hexact₀'
  exact Except.ok.inj (hexact₀'.symm.trans hdec)

private theorem emptyTables_of_constantTablesValid_prj {c : Ixon.Constant}
    (htv : L1.ConstantTablesValid c)
    (hprj : (∃ p, c.info = .dPrj p) ∨ (∃ p, c.info = .iPrj p) ∨
      (∃ p, c.info = .rPrj p) ∨ (∃ p, c.info = .cPrj p)) :
    Ix.Kernel.Reader.emptyTables c = true := by
  rcases hprj with ⟨p, hi⟩ | ⟨p, hi⟩ | ⟨p, hi⟩ | ⟨p, hi⟩ <;> {
    simp only [L1.ConstantTablesValid, hi] at htv
    rcases htv with ⟨h1, h2, h3, h4⟩
    simp [Ix.Kernel.Reader.emptyTables, h1, h2, h3, h4]
  }

/-! ## Section 1: Constructor Index Consistency (`indBlockCtorIdx_of_exact_noCollision`) -/

/-- When `MutsMemberCheckedAtFull` holds at inductive member `i` (`ms[i]? = some (.indc ind)`)
with no hash collision, every valid preimage of `Core.iprjAddr owner i` decodes to
`⟨.iPrj ⟨i.toUInt64, owner⟩, #[], #[], #[], #[]⟩` and `i < UInt64.size`. -/
theorem iprj_store_eq_of_mutsMemberChecked
    {calls : List (Call F)} {bAddr : _root_.Address} {t : Ix.Kernel.RoleTable}
    {owner : _root_.Address} {ms : Array Ixon.MutConst} {i : Nat} {ind : Ixon.Inductive}
    {V : IxVM.Refinement.View} {extra : List ByteArray}
    (hbound : IxVM.Consistency.Bounded calls)
    (hnoCol : ¬ V.HashedCollision extra calls)
    (hm : Claim.MutsMemberCheckedAtFull calls bAddr t owner ms i)
    (hms : ms[i]? = some (.indc ind)) :
    i < UInt64.size ∧
      ∀ (raw' : ByteArray) (c' : Ixon.Constant),
        _root_.Address.blake3Pure raw' = Core.iprjAddr owner i →
        Ixon.deConstantExact raw' = .ok c' →
        (V.Preimage (Core.iprjAddr owner i) raw' ∨ raw' ∈ extra ∨ Hashed calls raw') →
        c' = ⟨.iPrj ⟨i.toUInt64, owner⟩, #[], #[], #[], #[]⟩ := by
  have hchk : Claim.CheckedAtFull calls bAddr t (Core.iprjAddr owner i) := by
    have h0 := mutsMemberCheckedAtFull_to_checkedAtFull hbound hm hms
    simpa only [Core.Specs.Callees.memberProjInfo, Core.iprjAddr] using h0
  obtain ⟨_, _, _, _, _, _, _, _, _, cs_load, _, bytes, E_ld,
    _, _, _, _, hhash_ld, hblake_ld, _, hL1, hsub_ld, _, _, _, _⟩ :=
    checkedAtFull_loadedL1 hbound hchk
  obtain ⟨c_ld, hdec_ld, _, _, _, _, _⟩ := hL1
  have hhashed_calls : Hashed calls bytes := Core.hashed_mono hsub_ld hhash_ld
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, cs_pa, _, _,
    hmem_pa, hblk_pa, ev_pa, hcl_pa, hsub_pa, _, _, _, _, _, _, _, _, _⟩ := hm
  obtain ⟨b_arr, hb_ref, rfl⟩ := hblk_pa
  have hlen : ms.toList.length < 2 ^ 39 :=
    RomBound.bounded_length_lt hbound hcl_pa (List.Mem.head _) hmem_pa
  have hi_sz : i < ms.size := (Array.getElem?_eq_some_iff.mp hms).1
  have hi_len : i < ms.toList.length := by simpa using hi_sz
  have hi_lt : i < UInt64.size := by
    have : (2 ^ 39 : Nat) < UInt64.size := by decide
    omega
  have hwf_iprj :
      (⟨.iPrj ⟨i.toUInt64, Core.ixAddr b_arr⟩, #[], #[], #[], #[]⟩ : Ixon.Constant).wireWF := by
    rw [L1.emptyTablesConstant_wireWF]
    show (Core.ixAddr b_arr).hash.size = 32
    exact b_arr.size_toArray
  have hser_iprj :
      bytes = Ixon.serConstant ⟨.iPrj ⟨i.toUInt64, Core.ixAddr b_arr⟩, #[], #[], #[], #[]⟩ := by
    by_cases heq_b : bytes = Ixon.serConstant ⟨.iPrj ⟨i.toUInt64, Core.ixAddr b_arr⟩, #[], #[], #[], #[]⟩
    · exact heq_b
    · have hi_val : ((i : F)).val = i :=
        ZMod.val_natCast_of_lt (by unfold Aiur.Library.U32.Goldilocks.modulus; omega)
      obtain ⟨v1, m2, cs12, v31, m32, cs42, v198, m199, cs201,
        m231, m244, m257, m270, v282, m283, cs293, m306, cs321,
        ev14, ev44, sg206, hm239, hm252, hm265, hm278, hm314, ev295, ev323, hc332⟩ :=
        Obs.«Ingress::projection_addr».obs ev_pa
      obtain ⟨hm2, _, mc', hget_pa, hmc⟩ := L1.muts_member_at_spec hmem_pa ev14
      subst m2
      rw [hi_val] at hget_pa
      have hms_list : ms.toList[i]? = some (.indc ind) := by simpa using hms
      rw [hms_list] at hget_pa
      cases hget_pa
      obtain ⟨ni, hni, hxi, hv31, hm32⟩ := Lib.u64_from_field_spec ev44
      subst m32
      have hni_eq : ni = i := by
        have hv := congrArg ZMod.val (Value.field.inj hxi).symm
        rwa [ZMod.val_natCast_of_lt (Nat.lt_trans hni (by decide)), hi_val] at hv
      subst ni
      rw [hv31] at sg206
      have e1 : Heap.Extends m199 m231 := by rw [hm239]; exact Heap.Extends.snoc _ _
      have e2 : Heap.Extends m231 m244 := by rw [hm252]; exact Heap.Extends.snoc _ _
      have e3 : Heap.Extends m244 m257 := by rw [hm265]; exact Heap.Extends.snoc _ _
      have e4 : Heap.Extends m257 m270 := by rw [hm278]; exact Heap.Extends.snoc _ _
      have e5 : Heap.Extends m270 m306 := by rw [hm314]; exact Heap.Extends.snoc _ _
      have c1 : m306[m199.length]? = some (.construct Core.Specs.Callees.ixExprListEnum "Nil" []) :=
        (e2.trans (e3.trans (e4.trans e5))).getElem?_eq (by rw [hm239]; simp)
      have c2 : m306[m231.length]? = some (.construct Core.addrListEnum "Nil" []) :=
        (e3.trans (e4.trans e5)).getElem?_eq (by rw [hm252]; simp)
      have c3 : m306[m244.length]? = some (.construct Core.Specs.Callees.ixUnivListEnum "Nil" []) :=
        (e4.trans e5).getElem?_eq (by rw [hm265]; simp)
      have c4 : m306[m257.length]? = some (.construct Core.Specs.Callees.ixBinderListEnum "Nil" []) :=
        e5.getElem?_eq (by rw [hm278]; simp)
      have c5 : m306[m270.length]? = some (.construct Core.byteListEnum "Nil" []) := by
        rw [hm314]; simp
      have hrepi : Aiur.Library.RepU64 m306 i.toUInt64 (TagN.u64Value i) := by
        have e := Lib.repU64_ofNatLT m306 (m := i)
          (Nat.lt_trans hi_len (Nat.lt_trans hlen (by decide)))
        rwa [UInt64.ofNatLT_eq_ofNat] at e
      obtain ⟨iv, rfl⟩ := hmc
      have hinfo_rep :
          Core.Specs.Callees.ProjInfoRep m306 (.iPrj ⟨i.toUInt64, Core.ixAddr b_arr⟩) v198 := by
        cases sg206 with
        | Defn _ hv67 _ _ _ =>
          simp only [Core.Specs.Callees.mutCtor] at hv67
          injection hv67 with _ hc _
          exact absurd hc (by decide)
        | Indc _ _ _ he124 he150 _ =>
          subst he150
          rw [he124]
          exact ⟨TagN.u64Value i, _, b_arr, rfl, hrepi,
            Aiur.Library.Bytes.repAddressRef_heapMono₂ Core.addrTy
              (e1.trans (e2.trans (e3.trans (e4.trans e5)))) hb_ref, rfl⟩
        | Recr _ _ _ hv157 _ _ _ =>
          simp only [Core.Specs.Callees.mutCtor] at hv157
          injection hv157 with _ hc _
          exact absurd hc (by decide)
      have hbytes := Core.put_constant_step ⟨{}, .empty, t, none⟩ ev295 _ _
        (.iPrj ⟨i.toUInt64, Core.ixAddr b_arr⟩) [] rfl
        ⟨_, _, _, _, _, rfl, hinfo_rep,
          Aiur.RepLinkedList.nil c1, Aiur.RepLinkedList.nil c2,
          Aiur.RepLinkedList.nil c3, Aiur.RepLinkedList.nil c4⟩
        (Aiur.RepLinkedList.nil c5)
      rw [List.append_nil] at hbytes
      have hstream : L1.Stream m283
          (Ixon.serConstant ⟨.iPrj ⟨i.toUInt64, Core.ixAddr b_arr⟩, #[], #[], #[], #[]⟩).data.toList
          v282 := hbytes
      have hcall_b3 := (L1.bytes_to_addr_spec hstream ev323).2.2
      have hcall_pa : (⟨"Blake3::hash", [v282], m283⟩ : Call F) ∈ cs_pa := by
        rw [hc332]; simp [hcall_b3]
      have hhash_pa :
          Hashed cs_pa (Ixon.serConstant ⟨.iPrj ⟨i.toUInt64, Core.ixAddr b_arr⟩, #[], #[], #[], #[]⟩) :=
        ⟨_, hcall_pa, rfl, v282, rfl, hstream⟩
      have hhashed_pa :
          Hashed calls (Ixon.serConstant ⟨.iPrj ⟨i.toUInt64, Core.ixAddr b_arr⟩, #[], #[], #[], #[]⟩) :=
        Core.hashed_mono hsub_pa hhash_pa
      exact absurd (.inl ⟨Core.iprjAddr (Core.ixAddr b_arr) i,
        Ixon.serConstant ⟨.iPrj ⟨i.toUInt64, Core.ixAddr b_arr⟩, #[], #[], #[], #[]⟩,
        bytes, .inr (.inr ⟨hhashed_pa, rfl⟩), hhashed_calls, heq_b, hblake_ld⟩) hnoCol
  refine ⟨hi_lt, fun raw' c' hbl' hdec' hsrc' => ?_⟩
  have hraw_eq : raw' = bytes := by
    by_cases heq : raw' = bytes
    · exact heq
    · have hsrc_wit :
          (V.Preimage (Core.iprjAddr (Core.ixAddr b_arr) i) raw' ∨
            (raw' ∈ extra ∧ _root_.Address.blake3Pure raw' = Core.iprjAddr (Core.ixAddr b_arr) i) ∨
            (Hashed calls raw' ∧ _root_.Address.blake3Pure raw' = Core.iprjAddr (Core.ixAddr b_arr) i)) := by
        rcases hsrc' with hp | he | hh
        · exact .inl hp
        · exact .inr (.inl ⟨he, hbl'⟩)
        · exact .inr (.inr ⟨hh, hbl'⟩)
      exact absurd (.inl ⟨Core.iprjAddr (Core.ixAddr b_arr) i, raw', bytes,
        hsrc_wit, hhashed_calls, Ne.symm heq, hblake_ld⟩) hnoCol
  subst hraw_eq
  rw [hser_iprj] at hdec'
  have hrt := Ixon.Verify.deConstantExact_serConstant _ hwf_iprj
  exact Except.ok.inj (hdec'.symm.trans hrt)

/-- Along `KernelCheck::check_inductive_shape_ctors` on a safe inductive member `i`, every
constructor at `k ≤ j < ind.ctors.size` satisfies `ct.cidx.toNat = j`. -/
theorem check_inductive_shape_ctors_cidx
    {calls : List (Call F)} {E₀ : Ixon.Env} {V : IxVM.Refinement.View} {extra : List ByteArray}
    {blk : _root_.Address} {b_arr : Aiur.Library.Bytes.Address}
    {cb : Ixon.Constant} {ms : Array Ixon.MutConst} {i j : Nat}
    {ind : Ixon.Inductive} {ct : Ixon.Constructor}
    (hbound : IxVM.Consistency.Bounded calls)
    (hload₀ : IxVM.Consistency.LoadedBy calls E₀)
    (hexact₀ : L1.EnvDecoded E₀)
    (hnoCol : ¬ V.HashedCollision extra calls)
    (hrec_blk : Ix.Cert.recordAt E₀ blk = some cb)
    (hcb : cb.info = .muts ms)
    (hms_i : ms[i]? = some (.indc ind))
    (hct_j : ind.ctors[j]? = some ct)
    (hi_lt : i < 72057594037927936)
    (hnc_lt : ind.ctors.size < 72057594037927936)
    (hb_eq : Core.ixAddr b_arr = blk) :
    ∀ (m k : Nat) {x_rc x_ind_ty x_np x_ni x_nl blkPtr x_il r : SourceValue F}
      {h h' : Heap F} {cs : List (Call F)},
      m + k = ind.ctors.size →
      k ≤ j →
      (∀ cl ∈ cs, cl ∈ calls) →
      Aiur.Library.Bytes.RepAddressRef Core.addrTy h b_arr blkPtr →
      ObsFn Core.W "KernelCheck::check_inductive_shape_ctors"
        [x_rc, x_ind_ty, x_np, x_ni, .field (ind.ctors.size : F), x_nl,
         blkPtr, .field (i : F), x_il, .field 0, .field (k : F)] h r h' cs →
      ct.cidx.toNat = j := by
  have hj_sz : j < ind.ctors.size := (Array.getElem?_eq_some_iff.mp hct_j).1
  have hi_val : ((i : F)).val = i :=
    ZMod.val_natCast_of_lt (by unfold Aiur.Library.U32.Goldilocks.modulus; omega)
  intro m
  induction m with
  | zero =>
    intro k _ _ _ _ _ _ _ _ _ _ _ hmk hkj _ _ _
    omega
  | succ m ih =>
    intro k x_rc x_ind_ty x_np x_ni x_nl blkPtr x_il r h h' cs hmk hkj hsub hbp ev
    have hk_lt : k < ind.ctors.size := by omega
    have hk_val : ((k : F)).val = k :=
      ZMod.val_natCast_of_lt (by unfold Aiur.Library.U32.Goldilocks.modulus; omega)
    have hnc_val : ((ind.ctors.size : F)).val = ind.ctors.size :=
      ZMod.val_natCast_of_lt (by unfold Aiur.Library.U32.Goldilocks.modulus; omega)
    cases Obs.«KernelCheck::check_inductive_shape_ctors».obs ev with
    | n0 op17 _ _ _ =>
      simp only [evalBinOp, Except.ok.injEq, Value.field.injEq] at op17
      have heq_f : (ind.ctors.size : F) = (k : F) := sub_eq_zero.mp op17
      have heq_n : ind.ctors.size = k := by
        have hv := congrArg ZMod.val heq_f
        rwa [hnc_val, hk_val] at hv
      omega
    | other _ m34 p41 cs47 _ _ _ _ x_c_cidx _ _ _ _ m144 _ _ m319 _ _ m356 _ m387 _ m400 _ _ m430
        _ _ m476 _ _ m546 _ _ m646 _ cs657 v670
        _ _ ev49 ld43 ev154 _ _ heq233 _ _ _ ev331 hm395 ev368 ev412 ev442 ev488 ev558
        sg653 op754 ev659 hc756 =>
      have hsub47 : ∀ cl ∈ cs47, cl ∈ calls := fun cl hcl => hsub cl (by rw [hc756]; simp [hcl])
      obtain ⟨e_cprj, _, _, blkBytes, cb', ms', ind', ct', _, v_c,
        hhash_blk, hblake_blk, hexact_blk, _, hcb'_info, hms'_i, hct'_k, _, hld_vc, hraw_ct⟩ :=
        L1.get_ci_cprj_spec (RomBound.bounded_mono hbound hsub47) hbp ev49
      by_cases hkj_eq : k = j
      · subst hkj_eq
        rw [hb_eq] at hblake_blk
        have hcb_eq : cb = cb' := loaded_recordAt_eq_of_exact_noCollision
          hexact₀ hload₀ hnoCol hrec_blk hhash_blk hsub47 hblake_blk hexact_blk
        subst hcb_eq
        rw [hcb] at hcb'_info
        injection hcb'_info with hms_eq
        subst hms_eq
        rw [hi_val] at hms'_i
        have hms_list : ms.toList[i]? = some (.indc ind) := by simpa using hms_i
        rw [hms_list] at hms'_i
        injection hms'_i with hind_eq
        injection hind_eq with hind_eq'
        subst hind_eq'
        rw [hk_val] at hct'_k
        have hct_list : ind.ctors.toList[k]? = some ct := by simpa using hct_j
        rw [hct_list] at hct'_k
        injection hct'_k with hct_eq
        subst hct_eq
        obtain ⟨_, hcidx_lt, _, _, _, _, _, _, _, _, rfl, _⟩ := hraw_ct
        rw [hld_vc] at ld43
        injection ld43 with hv_eq
        injection hv_eq with _ _ hargs
        injection hargs with _ hargs; injection hargs with _ hargs
        injection hargs with _ hargs; injection hargs with _ hargs
        injection hargs with hcidx_f _
        have hcidx_eq_f : (ct.cidx.toNat : F) = (k : F) :=
          Value.field.inj (hcidx_f.trans heq233)
        have hcidx_val : ((ct.cidx.toNat : F)).val = ct.cidx.toNat :=
          ZMod.val_natCast_of_lt (by unfold Aiur.Library.U32.Goldilocks.modulus; omega)
        have hv := congrArg ZMod.val hcidx_eq_f
        rwa [hcidx_val, hk_val] at hv
      · have hsub657 : ∀ cl ∈ cs657, cl ∈ calls := fun cl hcl =>
          hsub cl (by rw [hc756]; simp [hcl])
        have e_387 : Heap.Extends m319 m387 := by rw [hm395]; exact Heap.Extends.snoc m319 _
        have e_pos : Heap.Extends m546 m646 := by
          cases sg653 with
          | other hne _ _ _ => exact absurd rfl hne
          | n0 _ _ ev_pos _ => exact ev_pos.heap_extends
        have e_all : Heap.Extends h m646 :=
          e_cprj.trans (ev154.heap_extends.trans (ev331.heap_extends.trans
            (e_387.trans (ev368.heap_extends.trans (ev412.heap_extends.trans
              (ev442.heap_extends.trans (ev488.heap_extends.trans
                (ev558.heap_extends.trans e_pos))))))))
        have hv670 : v670 = .field ((k + 1 : Nat) : F) := by
          simp only [evalBinOp, Except.ok.injEq] at op754
          rw [← op754]
          push_cast
          rfl
        rw [hv670] at ev659
        exact ih (k + 1) (by omega) (by omega) hsub657
          (Aiur.Library.Bytes.repAddressRef_heapMono₂ Core.addrTy e_all hbp) ev659

/-- Along `KernelCheck::check_modeled_ctors` on a safe inductive member `i`, every
constructor at `k ≤ j < ind.ctors.size` satisfies `ct.cidx.toNat = j`. -/
theorem check_modeled_ctors_cidx
    {calls : List (Call F)} {E₀ : Ixon.Env} {V : IxVM.Refinement.View} {extra : List ByteArray}
    {blk : _root_.Address} {b_arr : Aiur.Library.Bytes.Address}
    {cb : Ixon.Constant} {ms : Array Ixon.MutConst} {i j : Nat}
    {ind : Ixon.Inductive} {ct : Ixon.Constructor}
    (hbound : IxVM.Consistency.Bounded calls)
    (hload₀ : IxVM.Consistency.LoadedBy calls E₀)
    (hexact₀ : L1.EnvDecoded E₀)
    (hnoCol : ¬ V.HashedCollision extra calls)
    (hrec_blk : Ix.Cert.recordAt E₀ blk = some cb)
    (hcb : cb.info = .muts ms)
    (hms_i : ms[i]? = some (.indc ind))
    (hct_j : ind.ctors[j]? = some ct)
    (hi_lt : i < 72057594037927936)
    (hnc_lt : ind.ctors.size < 72057594037927936)
    (hb_eq : Core.ixAddr b_arr = blk) :
    ∀ (m k : Nat) {x_rc x_np x_ni x_nl blkPtr r : SourceValue F}
      {h h' : Heap F} {cs : List (Call F)},
      m + k = ind.ctors.size →
      k ≤ j →
      (∀ cl ∈ cs, cl ∈ calls) →
      Aiur.Library.Bytes.RepAddressRef Core.addrTy h b_arr blkPtr →
      ObsFn Core.W "KernelCheck::check_modeled_ctors"
        [x_rc, x_np, x_ni, .field (ind.ctors.size : F), x_nl,
         blkPtr, .field (i : F), .field 0, .field (k : F)] h r h' cs →
      ct.cidx.toNat = j := by
  have hj_sz : j < ind.ctors.size := (Array.getElem?_eq_some_iff.mp hct_j).1
  have hi_val : ((i : F)).val = i :=
    ZMod.val_natCast_of_lt (by unfold Aiur.Library.U32.Goldilocks.modulus; omega)
  intro m
  induction m with
  | zero =>
    intro k _ _ _ _ _ _ _ _ _ hmk hkj _ _ _
    omega
  | succ m ih =>
    intro k x_rc x_np x_ni x_nl blkPtr r h h' cs hmk hkj hsub hbp ev
    have hk_lt : k < ind.ctors.size := by omega
    have hk_val : ((k : F)).val = k :=
      ZMod.val_natCast_of_lt (by unfold Aiur.Library.U32.Goldilocks.modulus; omega)
    have hnc_val : ((ind.ctors.size : F)).val = ind.ctors.size :=
      ZMod.val_natCast_of_lt (by unfold Aiur.Library.U32.Goldilocks.modulus; omega)
    cases Obs.«KernelCheck::check_modeled_ctors».obs ev with
    | n0 op17 _ _ _ =>
      simp only [evalBinOp, Except.ok.injEq, Value.field.injEq] at op17
      have heq_f : (ind.ctors.size : F) = (k : F) := sub_eq_zero.mp op17
      have heq_n : ind.ctors.size = k := by
        have hv := congrArg ZMod.val heq_f
        rwa [hnc_val, hk_val] at hv
      omega
    | other _ m34 p41 cs47 _ _ _ _ x_c_cidx _ _ _ _ m144 _ _ m319 _ _ m356 _ m387 _ m400 _ _ m430
        _ cs502 v513
        _ _ ev49 ld43 ev154 _ _ heq233 _ _ _ ev331 hm395 ev368 ev412 ev442 op583 ev504 hc585 =>
      have hsub47 : ∀ cl ∈ cs47, cl ∈ calls := fun cl hcl => hsub cl (by rw [hc585]; simp [hcl])
      obtain ⟨e_cprj, _, _, blkBytes, cb', ms', ind', ct', _, v_c,
        hhash_blk, hblake_blk, hexact_blk, _, hcb'_info, hms'_i, hct'_k, _, hld_vc, hraw_ct⟩ :=
        L1.get_ci_cprj_spec (RomBound.bounded_mono hbound hsub47) hbp ev49
      by_cases hkj_eq : k = j
      · subst hkj_eq
        rw [hb_eq] at hblake_blk
        have hcb_eq : cb = cb' := loaded_recordAt_eq_of_exact_noCollision
          hexact₀ hload₀ hnoCol hrec_blk hhash_blk hsub47 hblake_blk hexact_blk
        subst hcb_eq
        rw [hcb] at hcb'_info
        injection hcb'_info with hms_eq
        subst hms_eq
        rw [hi_val] at hms'_i
        have hms_list : ms.toList[i]? = some (.indc ind) := by simpa using hms_i
        rw [hms_list] at hms'_i
        injection hms'_i with hind_eq
        injection hind_eq with hind_eq'
        subst hind_eq'
        rw [hk_val] at hct'_k
        have hct_list : ind.ctors.toList[k]? = some ct := by simpa using hct_j
        rw [hct_list] at hct'_k
        injection hct'_k with hct_eq
        subst hct_eq
        obtain ⟨_, hcidx_lt, _, _, _, _, _, _, _, _, rfl, _⟩ := hraw_ct
        rw [hld_vc] at ld43
        injection ld43 with hv_eq
        injection hv_eq with _ _ hargs
        injection hargs with _ hargs; injection hargs with _ hargs
        injection hargs with _ hargs; injection hargs with _ hargs
        injection hargs with hcidx_f _
        have hcidx_eq_f : (ct.cidx.toNat : F) = (k : F) :=
          Value.field.inj (hcidx_f.trans heq233)
        have hcidx_val : ((ct.cidx.toNat : F)).val = ct.cidx.toNat :=
          ZMod.val_natCast_of_lt (by unfold Aiur.Library.U32.Goldilocks.modulus; omega)
        have hv := congrArg ZMod.val hcidx_eq_f
        rwa [hcidx_val, hk_val] at hv
      · have hsub502 : ∀ cl ∈ cs502, cl ∈ calls := fun cl hcl =>
          hsub cl (by rw [hc585]; simp [hcl])
        have e_387 : Heap.Extends m319 m387 := by rw [hm395]; exact Heap.Extends.snoc m319 _
        have e_all : Heap.Extends h m430 :=
          e_cprj.trans (ev154.heap_extends.trans (ev331.heap_extends.trans
            (e_387.trans (ev368.heap_extends.trans (ev412.heap_extends.trans
              ev442.heap_extends)))))
        have hv513 : v513 = .field ((k + 1 : Nat) : F) := by
          simp only [evalBinOp, Except.ok.injEq] at op583
          rw [← op583]
          push_cast
          rfl
        rw [hv513] at ev504
        exact ih (k + 1) (by omega) (by omega) hsub502
          (Aiur.Library.Bytes.repAddressRef_heapMono₂ Core.addrTy e_all hbp) ev504

/-- **Unconditional constructor index consistency**: on any safe walked mutual inductive block in
an exact-decoded collision-free store `E₀`, `ct.cidx.toNat = j` for `ind.ctors[j]? = some ct`.
(`ProjSafe.SafeRefsInputs.indBlockCtorIdx` omits `L1.EnvDecoded E₀` and `¬ V.HashedCollision`,
both of which are in context at its sole call site in `RecordReadBare`.) -/
theorem indBlockCtorIdx_of_exact_noCollision
    {calls : List (Call F)} {bAddr : _root_.Address} {t : Ix.Kernel.RoleTable}
    {E₀ : Ixon.Env} {V : IxVM.Refinement.View} {extra : List ByteArray}
    {blk : _root_.Address} {cb : Ixon.Constant}
    {ms : Array Ixon.MutConst} {i j : Nat} {ind : Ixon.Inductive} {ct : Ixon.Constructor}
    (hbound : IxVM.Consistency.Bounded calls)
    (hload₀ : IxVM.Consistency.LoadedBy calls E₀)
    (hexact₀ : L1.EnvDecoded E₀)
    (hnoCol : ¬ V.HashedCollision extra calls)
    (hwk : WkAll calls bAddr t E₀ blk)
    (hsafe : ¬ IxVM.Consistency.OutsideLogicAt E₀ blk)
    (hrec_blk : Ix.Cert.recordAt E₀ blk = some cb)
    (hcb : cb.info = .muts ms)
    (hms_i : ms[i]? = some (.indc ind))
    (hct_j : ind.ctors[j]? = some ct) :
    ct.cidx.toNat = j := by
  obtain ⟨cb₀, hrec₀, hchk_or⟩ := (wkAll_closedSubwalk calls bAddr t E₀).checked blk hwk
  have hcb_eq₀ : cb₀ = cb := Option.some.inj (hrec₀.symm.trans hrec_blk)
  subst cb₀
  have hm_i : Claim.MutsMemberCheckedAtFull calls bAddr t blk ms i := by
    rcases hchk_or with ⟨ms', hms'_eq, hmem_chk⟩ | hchk_blk
    · rw [hcb] at hms'_eq
      injection hms'_eq with hms'_eq'
      subst ms'
      exact hmem_chk i (Array.getElem?_eq_some_iff.mp hms_i).1
    · obtain ⟨_, _, _, _, _, _, _, _, _, cs_ld, _, bytes_b, E_b,
        _, _, _, _, hhash_b, hblake_b, _, hL1_b, hsub_b, _, _, _, _⟩ :=
        checkedAtFull_loadedL1 hbound hchk_blk
      obtain ⟨c_b, hdec_b, _, _, _, _, hraw_b⟩ := hL1_b
      have hcb_eq_b : cb = c_b := loaded_recordAt_eq_of_exact_noCollision
        hexact₀ hload₀ hnoCol hrec_blk hhash_b hsub_b hblake_b hdec_b
      subst c_b
      simp only [L1.RawCIRep, hcb] at hraw_b
  obtain ⟨hi_u64, hstore_iprj⟩ := iprj_store_eq_of_mutsMemberChecked hbound hnoCol hm_i hms_i
  have hchk_iprj : Claim.CheckedAtFull calls bAddr t (Core.iprjAddr blk i) := by
    have h0 := mutsMemberCheckedAtFull_to_checkedAtFull hbound hm_i hms_i
    simpa only [Core.Specs.Callees.memberProjInfo, Core.iprjAddr] using h0
  obtain ⟨_, _, m_chk, _, rc, ap, ptr, v, r_chk, cs_ld, cs_chk, bytes_i, E_ld,
    _, _, _, _, hhash_i, hblake_i, hload_ld, hL1_i, hsub_ld, hld_v, ev_chk, _, hsub_chk⟩ :=
    checkedAtFull_loadedL1 hbound hchk_iprj
  obtain ⟨c_i, hdec_i, _, _, v', hld_v', hraw_i⟩ := hL1_i
  have hv_eq : v' = v := Except.ok.inj (hld_v'.symm.trans hld_v)
  subst v'
  have hc_i_eq : c_i = ⟨.iPrj ⟨i.toUInt64, blk⟩, #[], #[], #[], #[]⟩ :=
    hstore_iprj bytes_i c_i hblake_i hdec_i (.inr (.inr (Core.hashed_mono hsub_ld hhash_i)))
  subst c_i
  have hi_toNat : i.toUInt64.toNat = i := Nat.mod_eq_of_lt hi_u64
  simp only [L1.RawCIRep, hi_toNat] at hraw_i
  obtain ⟨hi_lt, lcB, cb_ld, ms_ld, ind_ld, _, hget_lcB, _, _, hexact_lcB, _,
    hcb_ld, hms_ld, _, hraw_ind⟩ := hraw_i
  obtain ⟨hhash_lcB, hblake_lcB⟩ := hload_ld.1 blk lcB hget_lcB
  have hcb_eq_ld : cb = cb_ld := loaded_recordAt_eq_of_exact_noCollision
    hexact₀ hload₀ hnoCol hrec_blk hhash_lcB hsub_ld hblake_lcB hexact_lcB
  subst cb_ld
  rw [hcb] at hcb_ld
  injection hcb_ld with hms_ld_eq
  subst ms_ld
  have hms_list : ms.toList[i]? = some (.indc ind) := by simpa using hms_i
  rw [hms_list] at hms_ld
  injection hms_ld with hind_ld_eq
  injection hind_ld_eq with hind_ld_eq'
  subst ind_ld
  have hind_safe : ind.isUnsafe = false := by
    have hinl : IxVM.Consistency.InLogic cb := by
      by_contra hnot
      exact hsafe ⟨cb, hrec_blk, .inl hnot⟩
    simp only [IxVM.Consistency.InLogic, hcb] at hinl
    exact (hinl (.indc ind) (List.mem_of_getElem? hms_list)).1
  obtain ⟨_, _, _, hnc_lt, _, tyPtr, blkPtr, b_arr, hb_eq, hbp_m, rfl, _⟩ := hraw_ind
  simp only [L1.repBoolField, hind_safe, Bool.false_eq_true, ↓reduceIte] at ev_chk
  match Obs.«KernelCheck::check_const».obs ev_chk with
  | .Axiom_n1 (hv37 := hv) .. | .Axiom_other_n0 (hv37 := hv) ..
  | .Axiom_other_other (hv37 := hv) ..
  | .Defn (hv269 := hv) .. | .Thm (hv526 := hv) ..
  | .Opaque (hv825 := hv) .. | .Quot (hv1076 := hv) ..
  | .Ctor_n0_n0 (hv1884 := hv) .. | .Ctor_n0_other (hv1884 := hv) ..
  | .Ctor_other_n0 (hv1884 := hv) .. | .Ctor_other_other (hv1884 := hv) ..
  | .Rec_n0 (hv2574 := hv) .. | .Rec_other (hv2574 := hv) .. =>
    injection hv with _ htag _; exact absurd htag (by decide)
  | .Induct_other_other (hv1240 := hv_ind) (hne1870 := hne_u) .. =>
    injection hv_ind with _ _ hargs
    injection hargs with _ hargs; injection hargs with _ hargs
    injection hargs with _ hargs; injection hargs with _ hargs
    injection hargs with _ hargs; injection hargs with hiu _
    exact absurd hiu.symm hne_u
  | .Induct_n0 (m2 := m2) (x_nlvls := xnl) (x_ty := xty)
      (x_n_params := xnp) (x_n_indices := xni) (x_num_ctors := xnc)
      (x_ind_is_unsafe := xiu) (x_ind_block := xblk) (x_ind_idx := xidx)
      (m1283 := m1283) (m1333 := m1333) (m1354 := m1354) (m1376 := m1376)
      (m1396 := m1396) (m1427 := m1427) (m1440 := m1440) (m1470 := m1470)
      (m1492 := m1492) (cs1529 := cs_sh)
      (ev14 := ev_iu) (hv1240 := hv_ind) (ev1295 := ev_ws)
      (hm1362 := hm1354) (hm1384 := hm1376) (ev1343 := ev_emb)
      (hm1435 := hm1427) (ev1408 := ev_es) (ev1452 := ev_saf)
      (ev1482 := ev_mk) (ev1505 := ev_mod) (ev1531 := ev_sh) (hc1634 := hc) .. =>
    injection hv_ind with _ _ hargs
    injection hargs with hnl hargs; injection hargs with hty hargs
    injection hargs with hnp hargs; injection hargs with hni hargs
    injection hargs with hnc hargs; injection hargs with hiu hargs
    injection hargs with hblk hargs; injection hargs with hidx _
    subst hnl hty hnp hni hnc hiu hblk hidx
    have e_1376 : Heap.Extends m1283 m1376 := by rw [hm1376]; exact Heap.Extends.snoc m1283 _
    have e_1354 : Heap.Extends m1376 m1354 := by rw [hm1354]; exact Heap.Extends.snoc m1376 _
    have e_1427 : Heap.Extends m1333 m1427 := by rw [hm1427]; exact Heap.Extends.snoc m1333 _
    have e_to_1492 : Heap.Extends m_chk m1492 :=
      ev_iu.heap_extends.trans (ev_ws.heap_extends.trans
        (e_1376.trans (e_1354.trans (ev_emb.heap_extends.trans
          (e_1427.trans (ev_es.heap_extends.trans (ev_saf.heap_extends.trans
            (ev_mk.heap_extends.trans ev_mod.heap_extends))))))))
    have hsub_sh : ∀ cl ∈ cs_sh, cl ∈ calls := fun cl hcl =>
      hsub_chk cl (by rw [hc]; simp [hcl])
    cases Obs.«KernelCheck::check_inductive_shape».obs ev_sh with
    | run _ m2_sh _ _ m50_sh _ m63_sh _ cs135 _ hm58 ev14_sh ev75_sh ev137 hc225 =>
      have e_50 : Heap.Extends m1492 m50_sh := by rw [hm58]; exact Heap.Extends.snoc m1492 _
      have e_to_63 : Heap.Extends m_chk m63_sh :=
        e_to_1492.trans (e_50.trans (ev14_sh.heap_extends.trans ev75_sh.heap_extends))
      have hsub_ctors : ∀ cl ∈ cs135, cl ∈ calls := fun cl hcl =>
        hsub_sh cl (by rw [hc225]; simp [hcl])
      exact check_inductive_shape_ctors_cidx hbound hload₀ hexact₀ hnoCol
        hrec_blk hcb hms_i hct_j hi_lt hnc_lt hb_eq
        ind.ctors.size 0 (by omega) (Nat.zero_le _) hsub_ctors
        (Aiur.Library.Bytes.repAddressRef_heapMono₂ Core.addrTy e_to_63 hbp_m) ev137
  | .Induct_other_n0 (m2 := m2) (x_nlvls := xnl) (x_ty := xty)
      (x_n_params := xnp) (x_n_indices := xni) (x_num_ctors := xnc)
      (x_ind_block := xblk) (x_ind_idx := xidx)
      (m1283 := m1283) (m1333 := m1333) (m1354 := m1354) (m1376 := m1376)
      (m1396 := m1396) (m1427 := m1427) (m1440 := m1440) (m1470 := m1470)
      (m1492 := m1492) (m1653 := m1653) (m1688 := m1688) (m1736 := m1736)
      (cs1759 := cs_mc)
      (ev14 := ev_iu) (hv1240 := hv_ind) (ev1295 := ev_ws)
      (hm1362 := hm1354) (hm1384 := hm1376) (ev1343 := ev_emb)
      (hm1435 := hm1427) (ev1408 := ev_es) (ev1452 := ev_saf)
      (ev1482 := ev_mk) (ev1505 := ev_mod) (ev1663 := ev_fa)
      (hm1744 := hm1736) (ev1700 := ev_rsl) (ev1761 := ev_mc) (hc1869 := hc) .. =>
    injection hv_ind with _ _ hargs
    injection hargs with hnl hargs; injection hargs with hty hargs
    injection hargs with hnp hargs; injection hargs with hni hargs
    injection hargs with hnc hargs; injection hargs with _ hargs
    injection hargs with hblk hargs; injection hargs with hidx _
    subst hnl hty hnp hni hnc hblk hidx
    have e_1376 : Heap.Extends m1283 m1376 := by rw [hm1376]; exact Heap.Extends.snoc m1283 _
    have e_1354 : Heap.Extends m1376 m1354 := by rw [hm1354]; exact Heap.Extends.snoc m1376 _
    have e_1427 : Heap.Extends m1333 m1427 := by rw [hm1427]; exact Heap.Extends.snoc m1333 _
    have e_1736 : Heap.Extends m1653 m1736 := by rw [hm1736]; exact Heap.Extends.snoc m1653 _
    have e_to_1688 : Heap.Extends m_chk m1688 :=
      ev_iu.heap_extends.trans (ev_ws.heap_extends.trans
        (e_1376.trans (e_1354.trans (ev_emb.heap_extends.trans
          (e_1427.trans (ev_es.heap_extends.trans (ev_saf.heap_extends.trans
            (ev_mk.heap_extends.trans (ev_mod.heap_extends.trans
              (ev_fa.heap_extends.trans (e_1736.trans ev_rsl.heap_extends)))))))))))
    have hsub_mc : ∀ cl ∈ cs_mc, cl ∈ calls := fun cl hcl =>
      hsub_chk cl (by rw [hc]; simp [hcl])
    exact check_modeled_ctors_cidx hbound hload₀ hexact₀ hnoCol
      hrec_blk hcb hms_i hct_j hi_lt hnc_lt hb_eq
      ind.ctors.size 0 (by omega) (Nat.zero_le _) hsub_mc
      (Aiur.Library.Bytes.repAddressRef_heapMono₂ Core.addrTy e_to_1688 hbp_m) ev_mc

/-! ## Section 2: `KernelCheck::safe_refs_only` Unconditional Theorems -/

/-- `.ref`-only reachable table indices in `e` through `sharing`, matching
`KernelCheck::safe_refs_only` where `KExprNode::Proj(_, _, e1)` recurses on `e1`. -/
def reachRefOnlyExpr (sh : Array (List Nat)) : Ixon.Expr → List Nat
  | .var _ | .sort _ | .recur _ _ | .str _ | .nat _ => []
  | .ref idx _ => [idx.toNat]
  | .prj _ _ inner => reachRefOnlyExpr sh inner
  | .app f g => reachRefOnlyExpr sh f ++ reachRefOnlyExpr sh g
  | .lam t b | .all t b => reachRefOnlyExpr sh t ++ reachRefOnlyExpr sh b
  | .letE _ _ t v b => reachRefOnlyExpr sh t ++ reachRefOnlyExpr sh v ++ reachRefOnlyExpr sh b
  | .share idx => sh[idx.toNat]?.getD []

/-- Sharing table of `.ref`-only reachable indices. -/
def buildReachRefOnlyTbl (sharing : List Ixon.Expr) : Array (List Nat) :=
  sharing.foldl (fun acc entry => acc.push (reachRefOnlyExpr acc entry)) #[]

private theorem buildReachRefOnlyTbl_size :
    ∀ (es : List Ixon.Expr) (acc : Array (List Nat)),
      (es.foldl (fun a entry => a.push (reachRefOnlyExpr a entry)) acc).size =
        acc.size + es.length
  | [], acc => by simp
  | _ :: es, acc => by
    simp only [List.foldl_cons, List.length_cons]
    rw [buildReachRefOnlyTbl_size es]
    simp [Array.size_push]
    omega

private theorem buildReachRefOnlyTbl_prefix :
    ∀ (es : List Ixon.Expr) (acc : Array (List Nat)) (i : Nat),
      i < acc.size →
      (es.foldl (fun a entry => a.push (reachRefOnlyExpr a entry)) acc)[i]? = acc[i]?
  | [], _, _, _ => rfl
  | _ :: es, acc, i, hi => by
    simp only [List.foldl_cons]
    rw [buildReachRefOnlyTbl_prefix es _ i (by simp; omega)]
    have hne : i ≠ acc.size := by omega
    simp [Array.getElem?_push, hne]

private theorem buildReachRefOnlyTbl_take_getElem? (sharing : List Ixon.Expr)
    {n i : Nat} {s : Ixon.Expr} (hi_n : i < n) (hsh : sharing[i]? = some s) :
    (buildReachRefOnlyTbl (sharing.take n))[i]? =
      some (reachRefOnlyExpr (buildReachRefOnlyTbl (sharing.take i)) s) := by
  have hi_len : i < sharing.length := (List.getElem?_eq_some_iff.mp hsh).1
  have hsplit : sharing.take n =
      sharing.take i ++ (s :: (sharing.drop (i + 1)).take (n - 1 - i)) := by
    have h1 : sharing.take n = (sharing.take i ++ sharing.drop i).take n := by
      rw [List.take_append_drop]
    have hdrop : sharing.drop i = s :: sharing.drop (i + 1) := by
      rw [List.drop_eq_getElem_cons hi_len]
      have hs_eq : sharing[i] = s := Option.some.inj ((List.getElem?_eq_getElem hi_len).symm.trans hsh)
      rw [hs_eq]
    rw [h1, hdrop, List.take_append]
    simp only [List.length_take, Nat.min_eq_left (Nat.le_of_lt hi_len)]
    have hsub : n - i = (n - 1 - i) + 1 := by omega
    rw [List.take_of_length_le (by simp; omega), hsub, List.take_succ_cons]
  unfold buildReachRefOnlyTbl
  rw [hsplit, List.foldl_append, List.foldl_cons]
  have hsz : ((sharing.take i).foldl (fun acc entry => acc.push (reachRefOnlyExpr acc entry)) #[]).size = i := by
    rw [buildReachRefOnlyTbl_size]; simp [Nat.min_eq_left (Nat.le_of_lt hi_len)]
  rw [buildReachRefOnlyTbl_prefix _ _ i (by simp [hsz]), Array.getElem?_push]
  simp [hsz]

/-- Combined boolean evaluation, heap extension, and `.ref`-only constant resolution along any
`L1.RawConvExpr` evaluated by `KernelCheck::safe_refs_only`. -/
theorem safe_refs_only_raw_spec
    {calls : List (Call F)} {bAddr : _root_.Address} {t : Ix.Kernel.RoleTable}
    {E₀ : Ixon.Env} {V : IxVM.Refinement.View} {extra : List ByteArray}
    {c : Ixon.Constant} {recurAddrs : List _root_.Address}
    {blobs : List (_root_.Address × ByteArray)} {h₀ : Heap F}
    {bound : Nat} {e : Ixon.Expr} {kp : SourceValue F}
    (hbound : IxVM.Consistency.Bounded calls)
    (hload₀ : IxVM.Consistency.LoadedBy calls E₀)
    (hexact₀ : L1.EnvDecoded E₀)
    (hnoCol : ¬ V.HashedCollision extra calls)
    (raw : L1.RawConvExpr c.refs.toList recurAddrs c.univs.toList c.sharing.toList blobs h₀ bound e kp) :
    ∀ (n : Nat) {h h' : Heap F} {r : SourceValue F} {cs : List (Call F)},
      n ≤ c.sharing.toList.length →
      (bound ≤ n ∨ (bound = 4294967295 ∧ n = c.sharing.toList.length)) →
      Heap.Extends h₀ h →
      (∀ cl ∈ cs, cl ∈ calls) →
      ObsFn Core.W "KernelCheck::safe_refs_only" [kp] h r h' cs →
      (r = .field 0 ∨ r = .field 1) ∧
      Heap.Extends h h' ∧
      (r = .field 1 →
        ∀ {i : Nat} {a : _root_.Address},
          i ∈ reachRefOnlyExpr (buildReachRefOnlyTbl (c.sharing.toList.take n)) e →
          c.refs[i]? = some a →
          ∀ c_a, Ix.Cert.recordAt E₀ a = some c_a →
            L1.ConstantTablesValid c_a ∧
            (∀ ms, c_a.info ≠ .muts ms) ∧
            (Ix.Cert.ownerOf a c_a = a →
              ¬ IxVM.Consistency.OutsideLogicAt E₀ a ∧
              (Ix.Kernel.Reader.resolveSource (Ix.Cert.recordAt E₀) a c_a).isSome = true) ∧
            (((∃ p, c_a.info = .dPrj p) ∨ (∃ p, c_a.info = .iPrj p) ∨
                (∃ p, c_a.info = .rPrj p)) →
              (Ix.Cert.recordAt E₀ (Ix.Cert.ownerOf a c_a)).isSome = true →
              (Ix.Kernel.Reader.resolveSource (Ix.Cert.recordAt E₀) a c_a).isSome = true) ∧
            ((∃ p, c_a.info = .cPrj p) →
              (Ix.Cert.recordAt E₀ (Ix.Cert.ownerOf a c_a)).isSome = true →
              WkAll calls bAddr t E₀ (Ix.Cert.ownerOf a c_a) →
              ¬ IxVM.Consistency.OutsideLogicAt E₀ (Ix.Cert.ownerOf a c_a) →
              ¬ IxVM.Consistency.OutsideLogicAt E₀ a ∧
              (Ix.Kernel.Reader.resolveSource (Ix.Cert.recordAt E₀) a c_a).isSome = true)) := by
  induction raw with
  | var _ cell =>
    intro n h h' r cs _ _ hext _ ev
    have cell_h := hext.getElem?_eq cell
    cases Obs.«KernelCheck::safe_refs_only».obs ev with
    | BVar _ ld hr hh' _ =>
      exact ⟨Or.inr hr, by rw [hh'], fun _ _ _ hm => nomatch hm⟩
    | Srt _ ld _ _ _ | Const _ _ _ _ _ _ _ _ ld _ _ _ _ _
    | App _ _ _ _ _ _ _ ld _ _ _ _ | Lam _ _ _ _ _ _ _ _ ld _ _ _ _
    | Forall _ _ _ _ _ _ _ _ ld _ _ _ _ | Let _ _ _ _ _ _ _ _ _ _ _ _ ld _ _ _ _ _ _
    | Lit _ ld _ _ _ | Proj _ _ _ _ ld _ _ =>
      exact (Core.load_cell_ne cell_h ld (by decide)).elim
  | sort _ _ _ cell =>
    intro n h h' r cs _ _ hext _ ev
    have cell_h := hext.getElem?_eq cell
    cases Obs.«KernelCheck::safe_refs_only».obs ev with
    | Srt _ ld hr hh' _ =>
      exact ⟨Or.inr hr, by rw [hh'], fun _ _ _ hm => nomatch hm⟩
    | BVar _ ld _ _ _ | Const _ _ _ _ _ _ _ _ ld _ _ _ _ _
    | App _ _ _ _ _ _ _ ld _ _ _ _ | Lam _ _ _ _ _ _ _ _ ld _ _ _ _
    | Forall _ _ _ _ _ _ _ _ ld _ _ _ _ | Let _ _ _ _ _ _ _ _ _ _ _ _ ld _ _ _ _ _ _
    | Lit _ ld _ _ _ | Proj _ _ _ _ ld _ _ =>
      exact (Core.load_cell_ne cell_h ld (by decide)).elim
  | str _ _ _ _ _ cell =>
    intro n h h' r cs _ _ hext _ ev
    have cell_h := hext.getElem?_eq cell
    cases Obs.«KernelCheck::safe_refs_only».obs ev with
    | Lit _ ld hr hh' _ =>
      exact ⟨Or.inr hr, by rw [hh'], fun _ _ _ hm => nomatch hm⟩
    | BVar _ ld _ _ _ | Srt _ ld _ _ _ | Const _ _ _ _ _ _ _ _ ld _ _ _ _ _
    | App _ _ _ _ _ _ _ ld _ _ _ _ | Lam _ _ _ _ _ _ _ _ ld _ _ _ _
    | Forall _ _ _ _ _ _ _ _ ld _ _ _ _ | Let _ _ _ _ _ _ _ _ _ _ _ _ ld _ _ _ _ _ _
    | Proj _ _ _ _ ld _ _ =>
      exact (Core.load_cell_ne cell_h ld (by decide)).elim
  | nat _ _ _ _ _ _ _ cell =>
    intro n h h' r cs _ _ hext _ ev
    have cell_h := hext.getElem?_eq cell
    cases Obs.«KernelCheck::safe_refs_only».obs ev with
    | Lit _ ld hr hh' _ =>
      exact ⟨Or.inr hr, by rw [hh'], fun _ _ _ hm => nomatch hm⟩
    | BVar _ ld _ _ _ | Srt _ ld _ _ _ | Const _ _ _ _ _ _ _ _ ld _ _ _ _ _
    | App _ _ _ _ _ _ _ ld _ _ _ _ | Lam _ _ _ _ _ _ _ _ ld _ _ _ _
    | Forall _ _ _ _ _ _ _ _ ld _ _ _ _ | Let _ _ _ _ _ _ _ _ _ _ _ _ ld _ _ _ _ _ _
    | Proj _ _ _ _ ld _ _ =>
      exact (Core.load_cell_ne cell_h ld (by decide)).elim
  | recur _ _ _ ra _ _ cell =>
    intro n h h' r cs _ _ hext hsub ev
    have cell_h := hext.getElem?_eq cell
    cases Obs.«KernelCheck::safe_refs_only».obs ev with
    | Const x_caddr _ v63 m64 p71 cs77 y89 _ ld ev79 ld73 ev101 op95 hc110 =>
      have hxs := (Core.load_cell cell_h ld).2
      simp only [List.cons.injEq, and_true] at hxs
      rcases hxs with ⟨rfl, _⟩
      have hsub77 : ∀ cl ∈ cs77, cl ∈ calls := fun cl hcl => hsub cl (by rw [hc110]; simp [hcl])
      obtain ⟨ext_ci, _, E_ld, _, _, _, c_ld, _, _, _, v_ld, hld_v, hraw_ld⟩ :=
        L1.get_ci_loadedL1_spec (RomBound.bounded_mono hbound hsub77)
          (Aiur.Library.Bytes.repAddressRef_heapMono₂ Core.addrTy hext ra) ev79
      have hv_eq : v_ld = v63 := Except.ok.inj (hld_v.symm.trans ld73)
      subst hv_eq
      obtain ⟨hh', _, hy89, _, _⟩ := L1.is_unsafe_ci_raw_spec hraw_ld ev101
      subst hh'
      obtain ⟨hr_bool, _⟩ := sub_one_bool_dichot hy89 op95
      exact ⟨hr_bool, ext_ci, fun _ _ _ hm => nomatch hm⟩
    | BVar _ ld _ _ _ | Srt _ ld _ _ _
    | App _ _ _ _ _ _ _ ld _ _ _ _ | Lam _ _ _ _ _ _ _ _ ld _ _ _ _
    | Forall _ _ _ _ _ _ _ _ ld _ _ _ _ | Let _ _ _ _ _ _ _ _ _ _ _ _ ld _ _ _ _ _ _
    | Lit _ ld _ _ _ | Proj _ _ _ _ ld _ _ =>
      exact (Core.load_cell_ne cell_h ld (by decide)).elim
  | @ref bound addr rIdx uIdxs a' d ap lsp ls _ href hd ra _ _ cell =>
    intro n h h' r cs _ _ hext hsub ev
    have cell_h := hext.getElem?_eq cell
    cases Obs.«KernelCheck::safe_refs_only».obs ev with
    | Const x_caddr _ v63 m64 p71 cs77 y89 _ ld ev79 ld73 ev101 op95 hc110 =>
      have hxs := (Core.load_cell cell_h ld).2
      simp only [List.cons.injEq, and_true] at hxs
      rcases hxs with ⟨rfl, _⟩
      have hsub77 : ∀ cl ∈ cs77, cl ∈ calls := fun cl hcl => hsub cl (by rw [hc110]; simp [hcl])
      obtain ⟨ext_ci, bytes_ld, E_ld, hhash_ld, hblake_ld, hload_ld,
        c_ld, hexact_ld, _, htv_ld, v_ld, hld_v, hraw_ld⟩ :=
        L1.get_ci_loadedL1_spec (RomBound.bounded_mono hbound hsub77)
          (Aiur.Library.Bytes.repAddressRef_heapMono₂ Core.addrTy hext ra) ev79
      have hv_eq : v_ld = v63 := Except.ok.inj (hld_v.symm.trans ld73)
      subst hv_eq
      rw [hd] at hblake_ld
      rw [hblake_ld] at hraw_ld
      obtain ⟨hh', _, hy89, _, hinlogic⟩ := L1.is_unsafe_ci_raw_spec hraw_ld ev101
      subst hh'
      obtain ⟨hr_bool, hy0_of_r1⟩ := sub_one_bool_dichot hy89 op95
      refine ⟨hr_bool, ext_ci, fun hr1 {i a} hi hc_ref c_a hrec_a => ?_⟩
      have hy0 : y89 = .field 0 := hy0_of_r1 hr1
      simp only [reachRefOnlyExpr, List.mem_singleton] at hi
      subst hi
      have href_arr : c.refs[rIdx.toNat]? = some a' := by simpa using href
      have ha_eq : a' = a := Option.some.inj (href_arr.symm.trans hc_ref)
      rw [ha_eq] at hblake_ld hraw_ld hinlogic
      have hc_eq : c_a = c_ld := loaded_recordAt_eq_of_exact_noCollision
        hexact₀ hload₀ hnoCol hrec_a hhash_ld hsub77 hblake_ld hexact_ld
      rw [← hc_eq] at htv_ld hraw_ld hinlogic
      have hno_muts : ∀ ms, c_a.info ≠ .muts ms := by
        intro ms hms
        simp only [L1.RawCIRep, hms] at hraw_ld
      refine ⟨htv_ld, hno_muts, ?_, ?_, ?_⟩
      · intro hown
        have hinl : IxVM.Consistency.InLogic c_a := hinlogic hy0 hown
        have hnot_out : ¬ IxVM.Consistency.OutsideLogicAt E₀ a := by
          rintro ⟨c_x, hrec_x, hnot_c | ⟨cb_x, hrec_cb, hnot_cb⟩⟩
          · have hcx : c_x = c_a := Option.some.inj (hrec_x.symm.trans hrec_a)
            rw [hcx] at hnot_c
            exact hnot_c hinl
          · have hcx : c_x = c_a := Option.some.inj (hrec_x.symm.trans hrec_a)
            rw [hcx, hown] at hrec_cb
            have hcb : cb_x = c_a := Option.some.inj (hrec_cb.symm.trans hrec_a)
            rw [hcb] at hnot_cb
            exact hnot_cb hinl
        refine ⟨hnot_out, ?_⟩
        cases hinfo : c_a.info with
        | defn _ | recr _ | axio _ | quot _ =>
          simp [Ix.Kernel.Reader.resolveSource, hinfo]
        | muts ms => exact absurd hinfo (hno_muts ms)
        | dPrj p =>
          have hemp := emptyTables_of_constantTablesValid_prj htv_ld (.inl ⟨p, hinfo⟩)
          simp only [L1.RawCIRep, hinfo] at hraw_ld
          obtain ⟨_, lcB, cb_ld, ms_ld, d_ld, _, hget_B, _, _, hexact_B, _, hcb_ld, hms_ld, _, _⟩ := hraw_ld
          obtain ⟨hhash_B, hblake_B⟩ := hload_ld.1 p.block lcB hget_B
          have hp_eq : p.block = a := by simpa [Ix.Cert.ownerOf, hinfo] using hown
          rw [hp_eq] at hblake_B
          have hcb_eq : c_a = cb_ld := loaded_recordAt_eq_of_exact_noCollision
            hexact₀ hload₀ hnoCol hrec_a hhash_B hsub77 hblake_B hexact_B
          exact absurd ((congrArg Ixon.Constant.info hcb_eq).trans hcb_ld) (hno_muts ms_ld)
        | iPrj p =>
          simp only [L1.RawCIRep, hinfo] at hraw_ld
          obtain ⟨_, lcB, cb_ld, ms_ld, _, _, hget_B, _, _, hexact_B, _, hcb_ld, _, _, _⟩ := hraw_ld
          obtain ⟨hhash_B, hblake_B⟩ := hload_ld.1 p.block lcB hget_B
          have hp_eq : p.block = a := by simpa [Ix.Cert.ownerOf, hinfo] using hown
          rw [hp_eq] at hblake_B
          have hcb_eq : c_a = cb_ld := loaded_recordAt_eq_of_exact_noCollision
            hexact₀ hload₀ hnoCol hrec_a hhash_B hsub77 hblake_B hexact_B
          exact absurd ((congrArg Ixon.Constant.info hcb_eq).trans hcb_ld) (hno_muts ms_ld)
        | rPrj p =>
          simp only [L1.RawCIRep, hinfo] at hraw_ld
          obtain ⟨_, lcB, cb_ld, ms_ld, _, _, hget_B, _, _, hexact_B, _, hcb_ld, _, _, _⟩ := hraw_ld
          obtain ⟨hhash_B, hblake_B⟩ := hload_ld.1 p.block lcB hget_B
          have hp_eq : p.block = a := by simpa [Ix.Cert.ownerOf, hinfo] using hown
          rw [hp_eq] at hblake_B
          have hcb_eq : c_a = cb_ld := loaded_recordAt_eq_of_exact_noCollision
            hexact₀ hload₀ hnoCol hrec_a hhash_B hsub77 hblake_B hexact_B
          exact absurd ((congrArg Ixon.Constant.info hcb_eq).trans hcb_ld) (hno_muts ms_ld)
        | cPrj p =>
          simp only [L1.RawCIRep, hinfo] at hraw_ld
          obtain ⟨_, _, lcB, cb_ld, ms_ld, _, _, _, hget_B, _, _, hexact_B, _, hcb_ld, _, _, _, _⟩ := hraw_ld
          obtain ⟨hhash_B, hblake_B⟩ := hload_ld.1 p.block lcB hget_B
          have hp_eq : p.block = a := by simpa [Ix.Cert.ownerOf, hinfo] using hown
          rw [hp_eq] at hblake_B
          have hcb_eq : c_a = cb_ld := loaded_recordAt_eq_of_exact_noCollision
            hexact₀ hload₀ hnoCol hrec_a hhash_B hsub77 hblake_B hexact_B
          exact absurd ((congrArg Ixon.Constant.info hcb_eq).trans hcb_ld) (hno_muts ms_ld)
      · intro hprj hown_some
        obtain ⟨cb₀, hrec_cb₀⟩ := Option.isSome_iff_exists.mp hown_some
        rcases hprj with ⟨p, hinfo⟩ | ⟨p, hinfo⟩ | ⟨p, hinfo⟩
        · have hemp := emptyTables_of_constantTablesValid_prj htv_ld (.inl ⟨p, hinfo⟩)
          simp only [Ix.Cert.ownerOf, hinfo] at hrec_cb₀
          simp only [L1.RawCIRep, hinfo] at hraw_ld
          obtain ⟨_, lcB, cb_ld, ms_ld, d_ld, _, hget_B, _, _, hexact_B, _, hcb_ld, hms_ld, _, _⟩ := hraw_ld
          obtain ⟨hhash_B, hblake_B⟩ := hload_ld.1 p.block lcB hget_B
          have hcb_eq : cb₀ = cb_ld := loaded_recordAt_eq_of_exact_noCollision
            hexact₀ hload₀ hnoCol hrec_cb₀ hhash_B hsub77 hblake_B hexact_B
          subst hcb_eq
          have hms_arr : ms_ld[p.idx.toNat]? = some (.defn d_ld) := by simpa using hms_ld
          simp [Ix.Kernel.Reader.resolveSource, hinfo, hemp, hrec_cb₀, hcb_ld, hms_arr]
        · have hemp := emptyTables_of_constantTablesValid_prj htv_ld (.inr (.inl ⟨p, hinfo⟩))
          simp only [Ix.Cert.ownerOf, hinfo] at hrec_cb₀
          simp only [L1.RawCIRep, hinfo] at hraw_ld
          obtain ⟨_, lcB, cb_ld, ms_ld, ind_ld, _, hget_B, _, _, hexact_B, _, hcb_ld, hms_ld, _, _⟩ := hraw_ld
          obtain ⟨hhash_B, hblake_B⟩ := hload_ld.1 p.block lcB hget_B
          have hcb_eq : cb₀ = cb_ld := loaded_recordAt_eq_of_exact_noCollision
            hexact₀ hload₀ hnoCol hrec_cb₀ hhash_B hsub77 hblake_B hexact_B
          subst hcb_eq
          have hms_arr : ms_ld[p.idx.toNat]? = some (.indc ind_ld) := by simpa using hms_ld
          simp [Ix.Kernel.Reader.resolveSource, hinfo, hemp, hrec_cb₀, hcb_ld, hms_arr]
        · have hemp := emptyTables_of_constantTablesValid_prj htv_ld (.inr (.inr (.inl ⟨p, hinfo⟩)))
          simp only [Ix.Cert.ownerOf, hinfo] at hrec_cb₀
          simp only [L1.RawCIRep, hinfo] at hraw_ld
          obtain ⟨_, lcB, cb_ld, ms_ld, rc_ld, _, hget_B, _, _, hexact_B, _, hcb_ld, hms_ld, _, _⟩ := hraw_ld
          obtain ⟨hhash_B, hblake_B⟩ := hload_ld.1 p.block lcB hget_B
          have hcb_eq : cb₀ = cb_ld := loaded_recordAt_eq_of_exact_noCollision
            hexact₀ hload₀ hnoCol hrec_cb₀ hhash_B hsub77 hblake_B hexact_B
          subst hcb_eq
          have hms_arr : ms_ld[p.idx.toNat]? = some (.recr rc_ld) := by simpa using hms_ld
          simp [Ix.Kernel.Reader.resolveSource, hinfo, hemp, hrec_cb₀, hcb_ld, hms_arr]
      · rintro ⟨p, hinfo⟩ hown_some hwk_own hsafe_own
        have hemp := emptyTables_of_constantTablesValid_prj htv_ld (.inr (.inr (.inr ⟨p, hinfo⟩)))
        obtain ⟨cb₀, hrec_cb₀⟩ := Option.isSome_iff_exists.mp hown_some
        simp only [Ix.Cert.ownerOf, hinfo] at hrec_cb₀ hwk_own hsafe_own
        simp only [L1.RawCIRep, hinfo] at hraw_ld
        obtain ⟨_, _, lcB, cb_ld, ms_ld, ind_ld, ct_ld, _,
          hget_B, _, _, hexact_B, _, hcb_ld, hms_ld, hct_ld, _, _⟩ := hraw_ld
        obtain ⟨hhash_B, hblake_B⟩ := hload_ld.1 p.block lcB hget_B
        have hcb_eq : cb₀ = cb_ld := loaded_recordAt_eq_of_exact_noCollision
          hexact₀ hload₀ hnoCol hrec_cb₀ hhash_B hsub77 hblake_B hexact_B
        subst hcb_eq
        have hms_arr : ms_ld[p.idx.toNat]? = some (.indc ind_ld) := by simpa using hms_ld
        have hct_arr : ind_ld.ctors[p.cidx.toNat]? = some ct_ld := by simpa using hct_ld
        have hcidx_eq_nat : ct_ld.cidx.toNat = p.cidx.toNat :=
          indBlockCtorIdx_of_exact_noCollision hbound hload₀ hexact₀ hnoCol
            hwk_own hsafe_own hrec_cb₀ hcb_ld hms_arr hct_arr
        have hcidx_eq : ct_ld.cidx = p.cidx := UInt64.toNat_inj.mp hcidx_eq_nat
        have hnot_out_a : ¬ IxVM.Consistency.OutsideLogicAt E₀ a := by
          rintro ⟨c_x, hrec_x, hnot_c | ⟨cb_x, hrec_cbx, hnot_cbx⟩⟩
          · have hcx : c_x = c_a := Option.some.inj (hrec_x.symm.trans hrec_a)
            rw [hcx] at hnot_c
            exact hnot_c (by simp [IxVM.Consistency.InLogic, hinfo])
          · have hcx : c_x = c_a := Option.some.inj (hrec_x.symm.trans hrec_a)
            rw [hcx] at hrec_cbx
            simp only [Ix.Cert.ownerOf, hinfo] at hrec_cbx
            exact hsafe_own ⟨cb_x, hrec_cbx, .inl hnot_cbx⟩
        exact ⟨hnot_out_a,
          by simp [Ix.Kernel.Reader.resolveSource, hinfo, hemp, hrec_cb₀,
            hcb_ld, hms_arr, hct_arr, hcidx_eq, guard, pure]⟩
    | BVar _ ld _ _ _ | Srt _ ld _ _ _
    | App _ _ _ _ _ _ _ ld _ _ _ _ | Lam _ _ _ _ _ _ _ _ ld _ _ _ _
    | Forall _ _ _ _ _ _ _ _ ld _ _ _ _ | Let _ _ _ _ _ _ _ _ _ _ _ _ ld _ _ _ _ _ _
    | Lit _ ld _ _ _ | Proj _ _ _ _ ld _ _ =>
      exact (Core.load_cell_ne cell_h ld (by decide)).elim
  | prj _ _ _ _ _ _ cell ih =>
    intro n h h' r cs hn hbnd hext hsub ev
    have cell_h := hext.getElem?_eq cell
    cases Obs.«KernelCheck::safe_refs_only».obs ev with
    | Proj _ _ x_e1 cs409 ld ev411 hc420 =>
      have hxs := (Core.load_cell cell_h ld).2
      simp only [List.cons.injEq, and_true] at hxs
      rcases hxs with ⟨_, _, rfl⟩
      have hsub409 : ∀ cl ∈ cs409, cl ∈ calls := fun cl hcl => hsub cl (by rw [hc420]; simp [hcl])
      exact ih n hn hbnd hext hsub409 ev411
    | BVar _ ld _ _ _ | Srt _ ld _ _ _ | Const _ _ _ _ _ _ _ _ ld _ _ _ _ _
    | App _ _ _ _ _ _ _ ld _ _ _ _ | Lam _ _ _ _ _ _ _ _ ld _ _ _ _
    | Forall _ _ _ _ _ _ _ _ ld _ _ _ _ | Let _ _ _ _ _ _ _ _ _ _ _ _ ld _ _ _ _ _ _
    | Lit _ ld _ _ _ =>
      exact (Core.load_cell_ne cell_h ld (by decide)).elim
  | app _ _ cell ihf iha =>
    intro n h h' r cs hn hbnd hext hsub ev
    have cell_h := hext.getElem?_eq cell
    cases Obs.«KernelCheck::safe_refs_only».obs ev with
    | App x_f x_a x128 y129 m130 cs139 cs153 ld ev141 ev155 op135 hc164 =>
      have hxs := (Core.load_cell cell_h ld).2
      simp only [List.cons.injEq, and_true] at hxs
      rcases hxs with ⟨rfl, rfl⟩
      have hsub1 : ∀ cl ∈ cs139, cl ∈ calls := fun cl hcl => hsub cl (by rw [hc164]; simp [hcl])
      have hsub2 : ∀ cl ∈ cs153, cl ∈ calls := fun cl hcl => hsub cl (by rw [hc164]; simp [hcl])
      obtain ⟨hb1, ext1, hres1⟩ := ihf n hn hbnd hext hsub1 ev141
      obtain ⟨hb2, ext2, hres2⟩ := iha n hn hbnd (hext.trans ext1) hsub2 ev155
      obtain ⟨hr_b, hr1_imp⟩ := mul_bool_dichot hb1 hb2 op135
      refine ⟨hr_b, ext1.trans ext2, fun hr1 {i a} hi hc_ref c_a hrec_a => ?_⟩
      obtain ⟨hx1, hy1⟩ := hr1_imp hr1
      simp only [reachRefOnlyExpr, List.mem_append] at hi
      rcases hi with hif | hia
      · exact hres1 hx1 hif hc_ref c_a hrec_a
      · exact hres2 hy1 hia hc_ref c_a hrec_a
    | BVar _ ld _ _ _ | Srt _ ld _ _ _ | Const _ _ _ _ _ _ _ _ ld _ _ _ _ _
    | Lam _ _ _ _ _ _ _ _ ld _ _ _ _ | Forall _ _ _ _ _ _ _ _ ld _ _ _ _
    | Let _ _ _ _ _ _ _ _ _ _ _ _ ld _ _ _ _ _ _ | Lit _ ld _ _ _ | Proj _ _ _ _ ld _ _ =>
      exact (Core.load_cell_ne cell_h ld (by decide)).elim
  | lam _ _ _ cell iht ihb =>
    intro n h h' r cs hn hbnd hext hsub ev
    have cell_h := hext.getElem?_eq cell
    cases Obs.«KernelCheck::safe_refs_only».obs ev with
    | Lam x_t x_b _ x188 y189 m190 cs199 cs213 ld ev201 ev215 op195 hc224 =>
      have hxs := (Core.load_cell cell_h ld).2
      simp only [List.cons.injEq, and_true] at hxs
      rcases hxs with ⟨rfl, rfl, _⟩
      have hsub1 : ∀ cl ∈ cs199, cl ∈ calls := fun cl hcl => hsub cl (by rw [hc224]; simp [hcl])
      have hsub2 : ∀ cl ∈ cs213, cl ∈ calls := fun cl hcl => hsub cl (by rw [hc224]; simp [hcl])
      obtain ⟨hb1, ext1, hres1⟩ := iht n hn hbnd hext hsub1 ev201
      obtain ⟨hb2, ext2, hres2⟩ := ihb n hn hbnd (hext.trans ext1) hsub2 ev215
      obtain ⟨hr_b, hr1_imp⟩ := mul_bool_dichot hb1 hb2 op195
      refine ⟨hr_b, ext1.trans ext2, fun hr1 {i a} hi hc_ref c_a hrec_a => ?_⟩
      obtain ⟨hx1, hy1⟩ := hr1_imp hr1
      simp only [reachRefOnlyExpr, List.mem_append] at hi
      rcases hi with hit | hib
      · exact hres1 hx1 hit hc_ref c_a hrec_a
      · exact hres2 hy1 hib hc_ref c_a hrec_a
    | BVar _ ld _ _ _ | Srt _ ld _ _ _ | Const _ _ _ _ _ _ _ _ ld _ _ _ _ _
    | App _ _ _ _ _ _ _ ld _ _ _ _ | Forall _ _ _ _ _ _ _ _ ld _ _ _ _
    | Let _ _ _ _ _ _ _ _ _ _ _ _ ld _ _ _ _ _ _ | Lit _ ld _ _ _ | Proj _ _ _ _ ld _ _ =>
      exact (Core.load_cell_ne cell_h ld (by decide)).elim
  | all _ _ _ cell iht ihb =>
    intro n h h' r cs hn hbnd hext hsub ev
    have cell_h := hext.getElem?_eq cell
    cases Obs.«KernelCheck::safe_refs_only».obs ev with
    | Forall x_t x_b _ x248 y249 m250 cs259 cs273 ld ev261 ev275 op255 hc284 =>
      have hxs := (Core.load_cell cell_h ld).2
      simp only [List.cons.injEq, and_true] at hxs
      rcases hxs with ⟨rfl, rfl, _⟩
      have hsub1 : ∀ cl ∈ cs259, cl ∈ calls := fun cl hcl => hsub cl (by rw [hc284]; simp [hcl])
      have hsub2 : ∀ cl ∈ cs273, cl ∈ calls := fun cl hcl => hsub cl (by rw [hc284]; simp [hcl])
      obtain ⟨hb1, ext1, hres1⟩ := iht n hn hbnd hext hsub1 ev261
      obtain ⟨hb2, ext2, hres2⟩ := ihb n hn hbnd (hext.trans ext1) hsub2 ev275
      obtain ⟨hr_b, hr1_imp⟩ := mul_bool_dichot hb1 hb2 op255
      refine ⟨hr_b, ext1.trans ext2, fun hr1 {i a} hi hc_ref c_a hrec_a => ?_⟩
      obtain ⟨hx1, hy1⟩ := hr1_imp hr1
      simp only [reachRefOnlyExpr, List.mem_append] at hi
      rcases hi with hit | hib
      · exact hres1 hx1 hit hc_ref c_a hrec_a
      · exact hres2 hy1 hib hc_ref c_a hrec_a
    | BVar _ ld _ _ _ | Srt _ ld _ _ _ | Const _ _ _ _ _ _ _ _ ld _ _ _ _ _
    | App _ _ _ _ _ _ _ ld _ _ _ _ | Lam _ _ _ _ _ _ _ _ ld _ _ _ _
    | Let _ _ _ _ _ _ _ _ _ _ _ _ ld _ _ _ _ _ _ | Lit _ ld _ _ _ | Proj _ _ _ _ ld _ _ =>
      exact (Core.load_cell_ne cell_h ld (by decide)).elim
  | letE _ _ _ cell iht ihv ihb =>
    intro n h h' r cs hn hbnd hext hsub ev
    have cell_h := hext.getElem?_eq cell
    cases Obs.«KernelCheck::safe_refs_only».obs ev with
    | Let x_t x_v x_b x307 y308 m309 x315 y316 m317 cs326 cs340 cs354
        ld ev328 ev342 op322 ev356 op314 hc365 =>
      have hxs := (Core.load_cell cell_h ld).2
      simp only [List.cons.injEq, and_true] at hxs
      rcases hxs with ⟨rfl, rfl, rfl⟩
      have hsub1 : ∀ cl ∈ cs326, cl ∈ calls := fun cl hcl => hsub cl (by rw [hc365]; simp [hcl])
      have hsub2 : ∀ cl ∈ cs340, cl ∈ calls := fun cl hcl => hsub cl (by rw [hc365]; simp [hcl])
      have hsub3 : ∀ cl ∈ cs354, cl ∈ calls := fun cl hcl => hsub cl (by rw [hc365]; simp [hcl])
      obtain ⟨hb1, ext1, hres1⟩ := iht n hn hbnd hext hsub1 ev328
      obtain ⟨hb2, ext2, hres2⟩ := ihv n hn hbnd (hext.trans ext1) hsub2 ev342
      obtain ⟨hb12, hr12_imp⟩ := mul_bool_dichot hb1 hb2 op322
      obtain ⟨hb3, ext3, hres3⟩ := ihb n hn hbnd ((hext.trans ext1).trans ext2) hsub3 ev356
      obtain ⟨hr_b, hr_imp⟩ := mul_bool_dichot hb12 hb3 op314
      refine ⟨hr_b, (ext1.trans ext2).trans ext3, fun hr1 {i a} hi hc_ref c_a hrec_a => ?_⟩
      obtain ⟨hx307, hy308⟩ := hr_imp hr1
      obtain ⟨hx315, hy316⟩ := hr12_imp hx307
      simp only [reachRefOnlyExpr, List.mem_append] at hi
      rcases hi with (hit | hiv) | hib
      · exact hres1 hx315 hit hc_ref c_a hrec_a
      · exact hres2 hy316 hiv hc_ref c_a hrec_a
      · exact hres3 hy308 hib hc_ref c_a hrec_a
    | BVar _ ld _ _ _ | Srt _ ld _ _ _ | Const _ _ _ _ _ _ _ _ ld _ _ _ _ _
    | App _ _ _ _ _ _ _ ld _ _ _ _ | Lam _ _ _ _ _ _ _ _ ld _ _ _ _
    | Forall _ _ _ _ _ _ _ _ ld _ _ _ _ | Lit _ ld _ _ _ | Proj _ _ _ _ ld _ _ =>
      exact (Core.load_cell_ne cell_h ld (by decide)).elim
  | @share bound idx s kp hidx hsh _ ihs =>
    intro n h h' r cs _ hbnd hext hsub ev
    have hidx_len : idx.toNat < c.sharing.toList.length :=
      (List.getElem?_eq_some_iff.mp hsh).1
    have hidx_n : idx.toNat < n := by
      rcases hbnd with hle | ⟨_, hn_eq⟩ <;> omega
    have hget := buildReachRefOnlyTbl_take_getElem? c.sharing.toList hidx_n hsh
    obtain ⟨hb, ext, hres⟩ :=
      ihs idx.toNat (Nat.le_of_lt hidx_len) (.inl (Nat.le_refl _)) hext hsub ev
    refine ⟨hb, ext, fun hr1 {i a} hi hc_ref c_a hrec_a => ?_⟩
    simp only [reachRefOnlyExpr, hget, Option.getD_some] at hi
    exact hres hr1 hi hc_ref c_a hrec_a

/-- **Unconditional `.ref`-only safe-reference resolution**: along any top-level or sharing-bounded
`RawConvExpr` where `KernelCheck::safe_refs_only` evaluates to `.field 1`, every `.ref`-reachable
index `i` in `c.refs[i]? = some a` resolves in an exact-decoded collision-free store `E₀`:
- standalone records (`ownerOf a c_a = a`) satisfy `¬ OutsideLogicAt E₀ a` and
  `(resolveSource (recordAt E₀) a c_a).isSome = true`,
- `.dPrj`/`.iPrj`/`.rPrj` records whose owner is stored in `E₀` satisfy
  `(resolveSource (recordAt E₀) a c_a).isSome = true`, and
- `.cPrj` records whose owner is stored, safe, and walked in `E₀` satisfy both
  `¬ OutsideLogicAt E₀ a` and `(resolveSource (recordAt E₀) a c_a).isSome = true`. -/
theorem safe_refs_only_refOnly_resolve
    {calls : List (Call F)} {bAddr : _root_.Address} {t : Ix.Kernel.RoleTable}
    {E₀ : Ixon.Env} {V : IxVM.Refinement.View} {extra : List ByteArray}
    {c : Ixon.Constant} {recurAddrs : List _root_.Address}
    {blobs : List (_root_.Address × ByteArray)} {h h' : Heap F} {cs : List (Call F)}
    {bound : Nat} {e : Ixon.Expr} {kp : SourceValue F}
    (hbound : IxVM.Consistency.Bounded calls)
    (hload₀ : IxVM.Consistency.LoadedBy calls E₀)
    (hexact₀ : L1.EnvDecoded E₀)
    (hnoCol : ¬ V.HashedCollision extra calls)
    (hbnd : bound ≤ c.sharing.toList.length ∨ bound = 4294967295)
    (ev : ObsFn Core.W "KernelCheck::safe_refs_only" [kp] h (.field 1) h' cs)
    (hsub : ∀ cl ∈ cs, cl ∈ calls)
    (raw : L1.RawConvExpr c.refs.toList recurAddrs c.univs.toList c.sharing.toList blobs h bound e kp) :
    ∀ {i : Nat} {a : _root_.Address},
      i ∈ reachRefOnlyExpr (buildReachRefOnlyTbl c.sharing.toList) e →
      c.refs[i]? = some a →
      ∀ c_a, Ix.Cert.recordAt E₀ a = some c_a →
        L1.ConstantTablesValid c_a ∧
        (∀ ms, c_a.info ≠ .muts ms) ∧
        (Ix.Cert.ownerOf a c_a = a →
          ¬ IxVM.Consistency.OutsideLogicAt E₀ a ∧
          (Ix.Kernel.Reader.resolveSource (Ix.Cert.recordAt E₀) a c_a).isSome = true) ∧
        (((∃ p, c_a.info = .dPrj p) ∨ (∃ p, c_a.info = .iPrj p) ∨
            (∃ p, c_a.info = .rPrj p)) →
          (Ix.Cert.recordAt E₀ (Ix.Cert.ownerOf a c_a)).isSome = true →
          (Ix.Kernel.Reader.resolveSource (Ix.Cert.recordAt E₀) a c_a).isSome = true) ∧
        ((∃ p, c_a.info = .cPrj p) →
          (Ix.Cert.recordAt E₀ (Ix.Cert.ownerOf a c_a)).isSome = true →
          WkAll calls bAddr t E₀ (Ix.Cert.ownerOf a c_a) →
          ¬ IxVM.Consistency.OutsideLogicAt E₀ (Ix.Cert.ownerOf a c_a) →
          ¬ IxVM.Consistency.OutsideLogicAt E₀ a ∧
          (Ix.Kernel.Reader.resolveSource (Ix.Cert.recordAt E₀) a c_a).isSome = true) := by
  have hbnd' : bound ≤ c.sharing.toList.length ∨
      (bound = 4294967295 ∧ c.sharing.toList.length = c.sharing.toList.length) := by
    rcases hbnd with hle | heq
    · exact .inl hle
    · exact .inr ⟨heq, rfl⟩
  intro i a hi hc_ref c_a hrec_a
  rw [← List.take_length (l := c.sharing.toList)] at hi
  exact (safe_refs_only_raw_spec (bAddr := bAddr) (t := t)
    hbound hload₀ hexact₀ hnoCol raw
    c.sharing.toList.length (Nat.le_refl _) hbnd' (Heap.Extends.refl h) hsub ev).2.2
    rfl hi hc_ref c_a hrec_a

/-! ## Section 2B: Uniform Walked Block Safety & `SafeRefTargetChecked` -/

/-- Exact twin of `iprj_store_eq_of_mutsMemberChecked` for `.recr` mutual members: any
collision-free hashed or view-backed record at `Core.rprjAddr owner i` decodes to the canonical
empty-table `.rPrj` constant. -/
theorem rprj_store_eq_of_mutsMemberChecked
    {calls : List (Call F)} {V : IxVM.Refinement.View} {extra : List ByteArray}
    {bAddr owner : _root_.Address} {t : Ix.Kernel.RoleTable}
    {ms : Array Ixon.MutConst} {i : Nat} {rc : Ixon.Recursor}
    (hbound : IxVM.Consistency.Bounded calls)
    (hnoCol : ¬ V.HashedCollision extra calls)
    (hm : Claim.MutsMemberCheckedAtFull calls bAddr t owner ms i)
    (hms : ms[i]? = some (.recr rc)) :
    i < UInt64.size ∧
    ∀ raw' c',
      _root_.Address.blake3Pure raw' = Core.rprjAddr owner i →
      Ixon.deConstantExact raw' = .ok c' →
      (V.Preimage (Core.rprjAddr owner i) raw' ∨ raw' ∈ extra ∨ Hashed calls raw') →
        c' = ⟨.rPrj ⟨i.toUInt64, owner⟩, #[], #[], #[], #[]⟩ := by
  have hchk : Claim.CheckedAtFull calls bAddr t (Core.rprjAddr owner i) := by
    have h0 := mutsMemberCheckedAtFull_to_checkedAtFull hbound hm hms
    simpa only [Core.Specs.Callees.memberProjInfo, Core.rprjAddr] using h0
  obtain ⟨_, _, _, _, _, _, _, _, _, cs_load, _, bytes, E_ld,
    _, _, _, _, hhash_ld, hblake_ld, _, hL1, hsub_ld, _, _, _, _⟩ :=
    checkedAtFull_loadedL1 hbound hchk
  obtain ⟨c_ld, hdec_ld, _, _, _, _, _⟩ := hL1
  have hhashed_calls : Hashed calls bytes := Core.hashed_mono hsub_ld hhash_ld
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, cs_pa, _, _,
    hmem_pa, hblk_pa, ev_pa, hcl_pa, hsub_pa, _, _, _, _, _, _, _, _, _⟩ := hm
  obtain ⟨b_arr, hb_ref, rfl⟩ := hblk_pa
  have hlen : ms.toList.length < 2 ^ 39 :=
    RomBound.bounded_length_lt hbound hcl_pa (List.Mem.head _) hmem_pa
  have hi_sz : i < ms.size := (Array.getElem?_eq_some_iff.mp hms).1
  have hi_len : i < ms.toList.length := by simpa using hi_sz
  have hi_lt : i < UInt64.size := by
    have : (2 ^ 39 : Nat) < UInt64.size := by decide
    omega
  have hwf_rprj :
      (⟨.rPrj ⟨i.toUInt64, Core.ixAddr b_arr⟩, #[], #[], #[], #[]⟩ : Ixon.Constant).wireWF := by
    rw [L1.emptyTablesConstant_wireWF]
    show (Core.ixAddr b_arr).hash.size = 32
    exact b_arr.size_toArray
  have hser_rprj :
      bytes = Ixon.serConstant ⟨.rPrj ⟨i.toUInt64, Core.ixAddr b_arr⟩, #[], #[], #[], #[]⟩ := by
    by_cases heq_b : bytes = Ixon.serConstant ⟨.rPrj ⟨i.toUInt64, Core.ixAddr b_arr⟩, #[], #[], #[], #[]⟩
    · exact heq_b
    · have hi_val : ((i : F)).val = i :=
        ZMod.val_natCast_of_lt (by unfold Aiur.Library.U32.Goldilocks.modulus; omega)
      obtain ⟨v1, m2, cs12, v31, m32, cs42, v198, m199, cs201,
        m231, m244, m257, m270, v282, m283, cs293, m306, cs321,
        ev14, ev44, sg206, hm239, hm252, hm265, hm278, hm314, ev295, ev323, hc332⟩ :=
        Obs.«Ingress::projection_addr».obs ev_pa
      obtain ⟨hm2, _, mc', hget_pa, hmc⟩ := L1.muts_member_at_spec hmem_pa ev14
      subst m2
      rw [hi_val] at hget_pa
      have hms_list : ms.toList[i]? = some (.recr rc) := by simpa using hms
      rw [hms_list] at hget_pa
      cases hget_pa
      obtain ⟨ni, hni, hxi, hv31, hm32⟩ := Lib.u64_from_field_spec ev44
      subst m32
      have hni_eq : ni = i := by
        have hv := congrArg ZMod.val (Value.field.inj hxi).symm
        rwa [ZMod.val_natCast_of_lt (Nat.lt_trans hni (by decide)), hi_val] at hv
      subst ni
      rw [hv31] at sg206
      have e1 : Heap.Extends m199 m231 := by rw [hm239]; exact Heap.Extends.snoc _ _
      have e2 : Heap.Extends m231 m244 := by rw [hm252]; exact Heap.Extends.snoc _ _
      have e3 : Heap.Extends m244 m257 := by rw [hm265]; exact Heap.Extends.snoc _ _
      have e4 : Heap.Extends m257 m270 := by rw [hm278]; exact Heap.Extends.snoc _ _
      have e5 : Heap.Extends m270 m306 := by rw [hm314]; exact Heap.Extends.snoc _ _
      have c1 : m306[m199.length]? = some (.construct Core.Specs.Callees.ixExprListEnum "Nil" []) :=
        (e2.trans (e3.trans (e4.trans e5))).getElem?_eq (by rw [hm239]; simp)
      have c2 : m306[m231.length]? = some (.construct Core.addrListEnum "Nil" []) :=
        (e3.trans (e4.trans e5)).getElem?_eq (by rw [hm252]; simp)
      have c3 : m306[m244.length]? = some (.construct Core.Specs.Callees.ixUnivListEnum "Nil" []) :=
        (e4.trans e5).getElem?_eq (by rw [hm265]; simp)
      have c4 : m306[m257.length]? = some (.construct Core.Specs.Callees.ixBinderListEnum "Nil" []) :=
        e5.getElem?_eq (by rw [hm278]; simp)
      have c5 : m306[m270.length]? = some (.construct Core.byteListEnum "Nil" []) := by
        rw [hm314]; simp
      have hrepi : Aiur.Library.RepU64 m306 i.toUInt64 (TagN.u64Value i) := by
        have e := Lib.repU64_ofNatLT m306 (m := i)
          (Nat.lt_trans hi_len (Nat.lt_trans hlen (by decide)))
        rwa [UInt64.ofNatLT_eq_ofNat] at e
      obtain ⟨rv, rfl⟩ := hmc
      have hinfo_rep :
          Core.Specs.Callees.ProjInfoRep m306 (.rPrj ⟨i.toUInt64, Core.ixAddr b_arr⟩) v198 := by
        cases sg206 with
        | Defn _ hv67 _ _ _ =>
          simp only [Core.Specs.Callees.mutCtor] at hv67
          injection hv67 with _ hc _
          exact absurd hc (by decide)
        | Indc _ _ hv112 _ _ _ =>
          simp only [Core.Specs.Callees.mutCtor] at hv112
          injection hv112 with _ hc _
          exact absurd hc (by decide)
        | Recr _ _ _ _ he169 he195 _ =>
          subst he195
          rw [he169]
          exact ⟨TagN.u64Value i, _, b_arr, rfl, hrepi,
            Aiur.Library.Bytes.repAddressRef_heapMono₂ Core.addrTy
              (e1.trans (e2.trans (e3.trans (e4.trans e5)))) hb_ref, rfl⟩
      have hbytes := Core.put_constant_step ⟨{}, .empty, t, none⟩ ev295 _ _
        (.rPrj ⟨i.toUInt64, Core.ixAddr b_arr⟩) [] rfl
        ⟨_, _, _, _, _, rfl, hinfo_rep,
          Aiur.RepLinkedList.nil c1, Aiur.RepLinkedList.nil c2,
          Aiur.RepLinkedList.nil c3, Aiur.RepLinkedList.nil c4⟩
        (Aiur.RepLinkedList.nil c5)
      rw [List.append_nil] at hbytes
      have hstream : L1.Stream m283
          (Ixon.serConstant ⟨.rPrj ⟨i.toUInt64, Core.ixAddr b_arr⟩, #[], #[], #[], #[]⟩).data.toList
          v282 := hbytes
      have hcall_b3 := (L1.bytes_to_addr_spec hstream ev323).2.2
      have hcall_pa : (⟨"Blake3::hash", [v282], m283⟩ : Call F) ∈ cs_pa := by
        rw [hc332]; simp [hcall_b3]
      have hhash_pa :
          Hashed cs_pa (Ixon.serConstant ⟨.rPrj ⟨i.toUInt64, Core.ixAddr b_arr⟩, #[], #[], #[], #[]⟩) :=
        ⟨_, hcall_pa, rfl, v282, rfl, hstream⟩
      have hhashed_pa :
          Hashed calls (Ixon.serConstant ⟨.rPrj ⟨i.toUInt64, Core.ixAddr b_arr⟩, #[], #[], #[], #[]⟩) :=
        Core.hashed_mono hsub_pa hhash_pa
      exact absurd (.inl ⟨Core.rprjAddr (Core.ixAddr b_arr) i,
        Ixon.serConstant ⟨.rPrj ⟨i.toUInt64, Core.ixAddr b_arr⟩, #[], #[], #[], #[]⟩,
        bytes, .inr (.inr ⟨hhashed_pa, rfl⟩), hhashed_calls, heq_b, hblake_ld⟩) hnoCol
  refine ⟨hi_lt, fun raw' c' hbl' hdec' hsrc' => ?_⟩
  have hraw_eq : raw' = bytes := by
    by_cases heq : raw' = bytes
    · exact heq
    · have hsrc_wit :
          (V.Preimage (Core.rprjAddr (Core.ixAddr b_arr) i) raw' ∨
            (raw' ∈ extra ∧ _root_.Address.blake3Pure raw' = Core.rprjAddr (Core.ixAddr b_arr) i) ∨
            (Hashed calls raw' ∧ _root_.Address.blake3Pure raw' = Core.rprjAddr (Core.ixAddr b_arr) i)) := by
        rcases hsrc' with hp | he | hh
        · exact .inl hp
        · exact .inr (.inl ⟨he, hbl'⟩)
        · exact .inr (.inr ⟨hh, hbl'⟩)
      exact absurd (.inl ⟨Core.rprjAddr (Core.ixAddr b_arr) i, raw', bytes,
        hsrc_wit, hhashed_calls, Ne.symm heq, hblake_ld⟩) hnoCol
  subst hraw_eq
  rw [hser_rprj] at hdec'
  have hrt := Ixon.Verify.deConstantExact_serConstant _ hwf_rprj
  exact Except.ok.inj (hdec'.symm.trans hrt)

/-- Unsafe flag weight (`0` or `1`) of a constructor in `KernelCheck::ctors_safety_counts`. -/
private def ctorUnsafeBit (ct : Ixon.Constructor) : Nat :=
  if ct.isUnsafe then 1 else 0

/-- Unsafe weight of a mutual block member in `KernelCheck::muts_safety_counts`. -/
private def mutUnsafeCount : Ixon.MutConst → Nat
  | .defn d => if (Ix.Kernel.Reader.safetyDecline d).isNone then 0 else 1
  | .indc ind => (if ind.isUnsafe then 1 else 0) + (ind.ctors.toList.map ctorUnsafeBit).sum
  | .recr rc => if rc.isUnsafe then 1 else 0

/-- Total member + constructor count of a mutual block member in `KernelCheck::muts_safety_counts`. -/
private def mutConstCount : Ixon.MutConst → Nat
  | .defn _ => 1
  | .indc ind => 1 + ind.ctors.toList.length
  | .recr _ => 1

private theorem sum_ctorUnsafeBit_le_length :
    ∀ (cs : List Ixon.Constructor), (cs.map ctorUnsafeBit).sum ≤ cs.length
  | [] => Nat.le_refl 0
  | ct :: rest => by
    have hih := sum_ctorUnsafeBit_le_length rest
    simp only [List.map_cons, List.sum_cons, List.length_cons, ctorUnsafeBit]
    cases ct.isUnsafe <;> omega

private theorem sum_ctorUnsafeBit_eq_zero_iff :
    ∀ (cs : List Ixon.Constructor),
      (cs.map ctorUnsafeBit).sum = 0 ↔ ∀ ct ∈ cs, ct.isUnsafe = false
  | [] => by simp
  | ct :: rest => by
    rw [List.map_cons, List.sum_cons, Nat.add_eq_zero_iff, sum_ctorUnsafeBit_eq_zero_iff rest]
    constructor
    · rintro ⟨hct, hrest⟩ c hc
      rcases List.mem_cons.mp hc with rfl | hm
      · cases h : ct.isUnsafe <;> simp [ctorUnsafeBit, h] at hct ⊢
      · exact hrest c hm
    · intro hall
      refine ⟨?_, fun c hm => hall c (List.mem_cons_of_mem _ hm)⟩
      have h0 := hall ct List.mem_cons_self
      simp [ctorUnsafeBit, h0]

private theorem sum_ctorUnsafeBit_lt_length_of_mem :
    ∀ {cs : List Ixon.Constructor} {ct : Ixon.Constructor},
      ct ∈ cs → ct.isUnsafe = false → (cs.map ctorUnsafeBit).sum < cs.length
  | [], _, hm, _ => nomatch hm
  | c :: rest, ct, hm, hsafe => by
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    rcases List.mem_cons.mp hm with rfl | hmem
    · have hle := sum_ctorUnsafeBit_le_length rest
      simp [ctorUnsafeBit, hsafe]; omega
    · have hlt := sum_ctorUnsafeBit_lt_length_of_mem hmem hsafe
      simp only [ctorUnsafeBit]
      cases c.isUnsafe <;> omega

private theorem mutUnsafeCount_le_mutConstCount (m : Ixon.MutConst) :
    mutUnsafeCount m ≤ mutConstCount m := by
  cases m with
  | defn d =>
    simp only [mutUnsafeCount, mutConstCount]
    cases (Ix.Kernel.Reader.safetyDecline d).isNone <;> omega
  | indc ind =>
    have hle := sum_ctorUnsafeBit_le_length ind.ctors.toList
    simp only [mutUnsafeCount, mutConstCount]
    cases ind.isUnsafe <;> omega
  | recr rc =>
    simp only [mutUnsafeCount, mutConstCount]
    cases rc.isUnsafe <;> omega

private theorem mutUnsafeCount_eq_zero_iff (m : Ixon.MutConst) :
    mutUnsafeCount m = 0 ↔ IxVM.Consistency.InLogicMut m := by
  cases m with
  | defn d =>
    simp only [mutUnsafeCount, IxVM.Consistency.InLogicMut]
    cases h : Ix.Kernel.Reader.safetyDecline d <;> simp
  | indc ind =>
    simp only [mutUnsafeCount, IxVM.Consistency.InLogicMut, Nat.add_eq_zero_iff,
      sum_ctorUnsafeBit_eq_zero_iff]
    cases ind.isUnsafe <;> simp
  | recr rc =>
    simp only [mutUnsafeCount, IxVM.Consistency.InLogicMut]
    cases rc.isUnsafe <;> simp

private theorem sum_mutUnsafeCount_eq_zero_iff :
    ∀ (ms : List Ixon.MutConst),
      (ms.map mutUnsafeCount).sum = 0 ↔ ∀ m ∈ ms, IxVM.Consistency.InLogicMut m
  | [] => by simp
  | m :: rest => by
    rw [List.map_cons, List.sum_cons, Nat.add_eq_zero_iff, mutUnsafeCount_eq_zero_iff,
      sum_mutUnsafeCount_eq_zero_iff rest]
    constructor
    · rintro ⟨hm, hrest⟩ x hx
      rcases List.mem_cons.mp hx with rfl | hmem
      · exact hm
      · exact hrest x hmem
    · intro hall
      exact ⟨hall m List.mem_cons_self, fun x hmem => hall x (List.mem_cons_of_mem _ hmem)⟩

private theorem sum_mutUnsafeCount_lt_of_mem :
    ∀ {ms : List Ixon.MutConst} {m : Ixon.MutConst},
      m ∈ ms → mutUnsafeCount m < mutConstCount m →
      (ms.map mutUnsafeCount).sum < (ms.map mutConstCount).sum
  | [], _, hm, _ => nomatch hm
  | x :: rest, m, hm, hlt => by
    simp only [List.map_cons, List.sum_cons]
    rcases List.mem_cons.mp hm with rfl | hmem
    · have hle : (rest.map mutUnsafeCount).sum ≤ (rest.map mutConstCount).sum := by
        clear hm hlt
        induction rest with
        | nil => exact Nat.le_refl 0
        | cons y ys ih =>
          have hy := mutUnsafeCount_le_mutConstCount y
          simp only [List.map_cons, List.sum_cons]; omega
      omega
    · have hih := sum_mutUnsafeCount_lt_of_mem hmem hlt
      have hx := mutUnsafeCount_le_mutConstCount x
      omega

private theorem sum_ctor_resourceSize_ge_length :
    ∀ (cs : List Ixon.Constructor), cs.length ≤ (cs.map Ixon.Constructor.resourceSize).sum
  | [] => Nat.le_refl 0
  | ct :: rest => by
    have hih := sum_ctor_resourceSize_ge_length rest
    simp only [List.length_cons, List.map_cons, List.sum_cons, Ixon.Constructor.resourceSize]
    omega

private theorem mutConstCount_le_resourceSize (m : Ixon.MutConst) :
    mutConstCount m ≤ m.resourceSize := by
  cases m with
  | defn d => simp [mutConstCount, Ixon.MutConst.resourceSize, Ixon.Definition.resourceSize]; omega
  | indc ind =>
    have hct := sum_ctor_resourceSize_ge_length ind.ctors.toList
    simp only [mutConstCount, Ixon.MutConst.resourceSize, Ixon.Inductive.resourceSize]
    omega
  | recr rc => simp [mutConstCount, Ixon.MutConst.resourceSize, Ixon.Recursor.resourceSize]; omega

private theorem sum_mutConstCount_le_resourceSum :
    ∀ (ms : List Ixon.MutConst),
      (ms.map mutConstCount).sum ≤ (ms.map Ixon.MutConst.resourceSize).sum
  | [] => Nat.le_refl 0
  | m :: rest => by
    have hm := mutConstCount_le_resourceSize m
    have hih := sum_mutConstCount_le_resourceSum rest
    simp only [List.map_cons, List.sum_cons]; omega

private theorem sum_mutConstCount_lt_bound {rawBytes : ByteArray} {cb : Ixon.Constant}
    {ms : Array Ixon.MutConst}
    (hsz : rawBytes.size < 4294967296)
    (hdeExact : Ixon.deConstantExact rawBytes = .ok cb)
    (hms : cb.info = .muts ms) :
    (ms.toList.map mutConstCount).sum < 8589934592 := by
  have hres := Ixon.Verify.ConstantBounds.deConstantExact_resource_bound rawBytes cb hdeExact
  have hsum := sum_mutConstCount_le_resourceSum ms.toList
  have hinfo : (ms.toList.map Ixon.MutConst.resourceSize).sum ≤ cb.resourceSize := by
    dsimp [Ixon.Constant.resourceSize]
    rw [hms]
    dsimp [Ixon.ConstantInfo.resourceSize]
    omega
  omega

private theorem mul_sub_eq_zero_nat {u n : Nat} (hun : u ≤ n) (hn : n < 8589934592)
    (h : ((u : F)) * (((n : F)) - ((u : F))) = 0) : u = 0 ∨ u = n := by
  rcases mul_eq_zero.mp h with hu0 | hsub0
  · refine .inl ?_
    have heq : (u : F) = ((0 : Nat) : F) := by simpa using hu0
    rw [ZMod.natCast_eq_natCast_iff',
      Nat.mod_eq_of_lt (by unfold Aiur.Library.U32.Goldilocks.modulus; omega),
      Nat.mod_eq_of_lt (by unfold Aiur.Library.U32.Goldilocks.modulus; omega)] at heq
    exact heq
  · refine .inr ?_
    have heq : (n : F) = (u : F) := sub_eq_zero.mp hsub0
    rw [ZMod.natCast_eq_natCast_iff',
      Nat.mod_eq_of_lt (by unfold Aiur.Library.U32.Goldilocks.modulus; omega),
      Nat.mod_eq_of_lt (by unfold Aiur.Library.U32.Goldilocks.modulus; omega)] at heq
    exact heq.symm

private theorem repBool_false_of_zero {b : Bool} {v : SourceValue F}
    (hb : Claim.RepBool b v) (hv : v = .field 0) : b = false := by
  cases b with
  | false => rfl
  | true => exact absurd (hb.symm.trans hv) (fun h => one_ne_zero (Value.field.inj h))

private theorem repBool_true_of_ne_zero {b : Bool} {v : SourceValue F}
    (hb : Claim.RepBool b v) (hv : v ≠ .field 0) : b = true := by
  cases b with
  | false => exact absurd hb hv
  | true => rfl

private theorem defn_is_unsafe_ci_count_spec {kind : Ix.DefKind} {safety : Ix.DefinitionSafety}
    {x_kind x_safety r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (hk : Claim.RepDefKind kind x_kind)
    (hs : Claim.RepDefinitionSafety safety x_safety)
    (ev : ObsFn Core.W "Ingress::defn_is_unsafe_ci" [x_kind, x_safety] h r h' cs) :
    h' = h ∧
      r = .field (((if (Ix.Kernel.Reader.safetyDeclineOf kind safety).isNone then 0 else 1 : Nat) : F)) := by
  rcases Obs.«Ingress::defn_is_unsafe_ci».obs ev with
    ⟨hv15, rfl, rfl, -⟩ |
    ⟨_, hv25, hv41, rfl, rfl, -⟩ |
    ⟨_, hv25, hne46, rfl, rfl, -⟩ |
    ⟨_, _, hv58, hv74, rfl, rfl, -⟩ |
    ⟨_, _, hv58, hne79, rfl, rfl, -⟩
  · cases kind <;> simp [Claim.RepDefKind] at hk
    · rw [hk] at hv15; simp at hv15
    · rw [hk] at hv15; simp at hv15
    · exact ⟨rfl, by simp [Ix.Kernel.Reader.safetyDeclineOf]⟩
  · cases kind <;> simp [Claim.RepDefKind] at hk
    · rw [hk] at hv25; simp at hv25
    · cases safety <;> simp [Claim.RepDefinitionSafety] at hs
      · exact ⟨rfl, by simp [Ix.Kernel.Reader.safetyDeclineOf]⟩
      · rw [hs] at hv41; simp at hv41
      · rw [hs] at hv41; simp at hv41
    · rw [hk] at hv25; simp at hv25
  · cases kind <;> simp [Claim.RepDefKind] at hk
    · rw [hk] at hv25; simp at hv25
    · cases safety <;> simp [Claim.RepDefinitionSafety] at hs
      · exact absurd hs (hne46 [] rfl)
      · exact ⟨rfl, by simp [Ix.Kernel.Reader.safetyDeclineOf]⟩
      · exact ⟨rfl, by simp [Ix.Kernel.Reader.safetyDeclineOf]⟩
    · rw [hk] at hv25; simp at hv25
  · cases kind <;> simp [Claim.RepDefKind] at hk
    · cases safety <;> simp [Claim.RepDefinitionSafety] at hs
      · rw [hs] at hv74; simp at hv74
      · exact ⟨rfl, by simp [Ix.Kernel.Reader.safetyDeclineOf]⟩
      · rw [hs] at hv74; simp at hv74
    · rw [hk] at hv58; simp at hv58
    · rw [hk] at hv58; simp at hv58
  · cases kind <;> simp [Claim.RepDefKind] at hk
    · cases safety <;> simp [Claim.RepDefinitionSafety] at hs
      · exact ⟨rfl, by simp [Ix.Kernel.Reader.safetyDeclineOf]⟩
      · exact absurd hs (hne79 [] rfl)
      · exact ⟨rfl, by simp [Ix.Kernel.Reader.safetyDeclineOf]⟩
    · rw [hk] at hv58; simp at hv58
    · rw [hk] at hv58; simp at hv58

private theorem ctors_safety_counts_spec (cs : List Ixon.Constructor) :
    ∀ {h h' : Heap F} {x_cs r : SourceValue F} {calls : List (Call F)} (u n : Nat),
      Aiur.Library.List.RepList Obs.Names.«Lists::Node<Ixon::Constructor>»
        Claim.RepConstructor h cs x_cs →
      ObsFn Core.W "KernelCheck::ctors_safety_counts"
        [x_cs, .field (u : F), .field (n : F)] h r h' calls →
      h' = h ∧
        r = .tuple [.field (((u + (cs.map ctorUnsafeBit).sum : Nat) : F)),
                    .field (((n + cs.length : Nat) : F))] := by
  induction cs with
  | nil =>
    intro h h' x_cs r calls u n rep ev
    cases Obs.«KernelCheck::ctors_safety_counts».obs ev with
    | Nil ld12 he24 he39 _ =>
      exact ⟨he39, by simpa using he24⟩
    | Cons _ _ _ _ _ _ _ _ _ _ _ _ _ _ ld12 _ _ _ _ _ =>
      obtain ⟨_, _, hbad, -⟩ := Lib.rep_cons_of_load rep ld12
      cases hbad
  | cons ct rest ih =>
    intro h h' x_cs r calls u n rep ev
    cases Obs.«KernelCheck::ctors_safety_counts».obs ev with
    | Nil ld12 _ _ _ =>
      cases Lib.rep_nil_of_load rep ld12
    | Cons x_rest x_is_unsafe _ _ _ _ _ _ v139 m140 _ _ v155 v156 ld12 sg147 op177 op193 ev153 _ =>
      obtain ⟨ct', rest', heq, hct, hrest⟩ := Lib.rep_cons_of_load rep ld12
      injection heq with h1 h2
      subst ct' rest'
      obtain ⟨uVal, _, _, hv, hu, _, _⟩ := hct
      injection hv with _ _ hargs
      simp only [List.cons.injEq] at hargs
      have hu_eq : uVal = x_is_unsafe := hargs.1.symm
      subst uVal
      have hv156 : v156 = .field (((n + 1 : Nat) : F)) := by
        simpa [Nat.cast_add] using L1.binop_add op193
      subst v156
      cases sg147 with
      | n0 hv128 he129 he130 _ =>
        subst he130 he129
        have hfalse := repBool_false_of_zero hu hv128
        have hv155 : v155 = .field (((u + 0 : Nat) : F)) := by
          simpa [Nat.cast_add] using L1.binop_add op177
        subst v155
        obtain ⟨hh', hr⟩ := ih (u + 0) (n + 1) hrest ev153
        refine ⟨hh', ?_⟩
        rw [hr]
        simp only [List.map_cons, List.sum_cons, List.length_cons, ctorUnsafeBit, hfalse]
        congr 2 <;> [skip; congr 1] <;> congr 1 <;> congr 1 <;> omega
      | other hne132 he136 he137 _ =>
        subst he137 he136
        have htrue := repBool_true_of_ne_zero hu hne132
        have hv155 : v155 = .field (((u + 1 : Nat) : F)) := by
          simpa [Nat.cast_add] using L1.binop_add op177
        subst v155
        obtain ⟨hh', hr⟩ := ih (u + 1) (n + 1) hrest ev153
        refine ⟨hh', ?_⟩
        rw [hr]
        simp only [List.map_cons, List.sum_cons, List.length_cons, ctorUnsafeBit, htrue]
        congr 2 <;> [skip; congr 1] <;> congr 1 <;> congr 1 <;> omega

private theorem muts_safety_counts_spec (ms : List Ixon.MutConst) :
    ∀ {h h' : Heap F} {x_ms r : SourceValue F} {calls : List (Call F)} (u n : Nat),
      Aiur.Library.List.RepList Obs.Names.«Lists::Node<Ixon::MutConst>»
        Claim.RepMutConst h ms x_ms →
      ObsFn Core.W "KernelCheck::muts_safety_counts"
        [x_ms, .field (u : F), .field (n : F)] h r h' calls →
      Heap.Extends h h' ∧
        r = .tuple [.field (((u + (ms.map mutUnsafeCount).sum : Nat) : F)),
                    .field (((n + (ms.map mutConstCount).sum : Nat) : F))] := by
  induction ms with
  | nil =>
    intro h h' x_ms r calls u n rep ev
    cases Obs.«KernelCheck::muts_safety_counts».obs ev with
    | Nil ld12 he24 he39 _ =>
      exact ⟨by rw [he39], by simpa using he24⟩
    | Cons_Defn _ _ _ _ _ _ _ _ _ _ _ _ _ ld12 _ _ _ _ _
    | Cons_Indc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ld12 _ _ _ _ _ _ _ _
    | Cons_Recr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ld12 _ _ _ _ _ =>
      obtain ⟨_, _, hbad, -⟩ := Lib.rep_cons_of_load rep ld12
      cases hbad
  | cons m rest ih =>
    intro h h' x_ms r calls u n rep ev
    cases Obs.«KernelCheck::muts_safety_counts».obs ev with
    | Nil ld12 _ _ _ =>
      cases Lib.rep_nil_of_load rep ld12
    | Cons_Defn x_rest x_kind x_safety _ _ _ _ _ v136 v137 m146 y152 _ ld12 ev165 op158 op195 ev134 _ =>
      obtain ⟨m', rest', heq, hm, hrest⟩ := Lib.rep_cons_of_load rep ld12
      injection heq with h1 h2
      subst m' rest'
      cases m with
      | indc _ => obtain ⟨_, hv, _⟩ := hm; simp at hv
      | recr _ => obtain ⟨_, hv, _⟩ := hm; simp at hv
      | defn d =>
        obtain ⟨dv, hv_m, kVal, sVal, _, _, _, hv_d, hk, hs, _, _, _⟩ := hm
        injection hv_m with _ _ hargs_m
        simp only [List.cons.injEq, and_true] at hargs_m
        rw [← hargs_m] at hv_d
        injection hv_d with _ _ hargs_d
        simp only [List.cons.injEq] at hargs_d
        rcases hargs_d with ⟨rfl, rfl, _⟩
        obtain ⟨hm146, hy152⟩ := defn_is_unsafe_ci_count_spec hk hs ev165
        subst m146 hy152
        have hv136 : v136 = .field (((u + mutUnsafeCount (.defn d) : Nat) : F)) := by
          simpa [mutUnsafeCount, Ix.Kernel.Reader.safetyDecline, Nat.cast_add] using L1.binop_add op158
        have hv137 : v137 = .field (((n + 1 : Nat) : F)) := by
          simpa [Nat.cast_add] using L1.binop_add op195
        subst v136 v137
        obtain ⟨hext, hr⟩ := ih (u + mutUnsafeCount (.defn d)) (n + 1) hrest ev134
        refine ⟨hext, ?_⟩
        rw [hr]
        simp only [List.map_cons, List.sum_cons, mutConstCount]
        congr 2 <;> [skip; congr 1] <;> congr 1 <;> congr 1 <;> omega
    | Cons_Indc x_rest x_is_unsafe _ _ _ _ x_ctors v285 m286 _ m295 _ x_cu x_cn _ v350 v351 x365 x390
        ld12 sg293 ev307 op380 op372 op405 op397 ev348 _ =>
      obtain ⟨m', rest', heq, hm, hrest⟩ := Lib.rep_cons_of_load rep ld12
      injection heq with h1 h2
      subst m' rest'
      cases m with
      | defn _ => obtain ⟨_, hv, _⟩ := hm; simp at hv
      | recr _ => obtain ⟨_, hv, _⟩ := hm; simp at hv
      | indc ind =>
        obtain ⟨iv, hv_m, uVal, _, ctorsPtr, hv_i, hu, _, hctors⟩ := hm
        injection hv_m with _ _ hargs_m
        simp only [List.cons.injEq, and_true] at hargs_m
        rw [← hargs_m] at hv_i
        injection hv_i with _ _ hargs_i
        simp only [List.cons.injEq, and_true] at hargs_i
        rcases hargs_i with ⟨rfl, _, _, _, _, rfl⟩
        have hiu : m286 = h ∧ v285 = .field (((if ind.isUnsafe then 1 else 0 : Nat) : F)) := by
          cases sg293 with
          | n0 hv274 he275 he276 _ =>
            have hf := repBool_false_of_zero hu hv274
            exact ⟨he276, by simpa [hf] using he275⟩
          | other hne278 he282 he283 _ =>
            have ht := repBool_true_of_ne_zero hu hne278
            exact ⟨he283, by simpa [ht] using he282⟩
        obtain ⟨rfl, hv285⟩ := hiu
        subst hv285
        obtain ⟨rfl, hct_tup⟩ := ctors_safety_counts_spec ind.ctors.toList 0 0 hctors ev307
        simp only [Nat.zero_add, Value.tuple.injEq, List.cons.injEq, and_true] at hct_tup
        rcases hct_tup with ⟨rfl, rfl⟩
        have hx365 : x365 = .field (((u + (if ind.isUnsafe then 1 else 0) : Nat) : F)) := by
          simpa [Nat.cast_add] using L1.binop_add op380
        subst hx365
        have hv350 : v350 = .field (((u + mutUnsafeCount (.indc ind) : Nat) : F)) := by
          simpa [mutUnsafeCount, Nat.add_assoc, Nat.cast_add] using L1.binop_add op372
        have hx390 : x390 = .field (((n + 1 : Nat) : F)) := by
          simpa [Nat.cast_add] using L1.binop_add op405
        subst hx390
        have hv351 : v351 = .field (((n + mutConstCount (.indc ind) : Nat) : F)) := by
          simpa [mutConstCount, Nat.add_assoc, Nat.cast_add] using L1.binop_add op397
        subst hv350 hv351
        obtain ⟨hext, hr⟩ := ih (u + mutUnsafeCount (.indc ind)) (n + mutConstCount (.indc ind)) hrest ev348
        refine ⟨hext, ?_⟩
        rw [hr]
        simp only [List.map_cons, List.sum_cons]
        congr 2 <;> [skip; congr 1] <;> congr 1 <;> congr 1 <;> omega
    | Cons_Recr x_rest _ x_is_unsafe _ _ _ _ _ _ _ v515 m516 _ _ v531 v532
        ld12 sg523 op553 op569 ev529 _ =>
      obtain ⟨m', rest', heq, hm, hrest⟩ := Lib.rep_cons_of_load rep ld12
      injection heq with h1 h2
      subst m' rest'
      cases m with
      | defn _ => obtain ⟨_, hv, _⟩ := hm; simp at hv
      | indc _ => obtain ⟨_, hv, _⟩ := hm; simp at hv
      | recr rc =>
        obtain ⟨rv, hv_m, _, uVal, _, _, hv_r, _, hu, _, _⟩ := hm
        injection hv_m with _ _ hargs_m
        simp only [List.cons.injEq, and_true] at hargs_m
        rw [← hargs_m] at hv_r
        injection hv_r with _ _ hargs_r
        simp only [List.cons.injEq] at hargs_r
        rcases hargs_r with ⟨_, rfl, _⟩
        have hru : m516 = h ∧ v515 = .field (((if rc.isUnsafe then 1 else 0 : Nat) : F)) := by
          cases sg523 with
          | n0 hv504 he505 he506 _ =>
            have hf := repBool_false_of_zero hu hv504
            exact ⟨he506, by simpa [hf] using he505⟩
          | other hne508 he512 he513 _ =>
            have ht := repBool_true_of_ne_zero hu hne508
            exact ⟨he513, by simpa [ht] using he512⟩
        obtain ⟨rfl, hv515⟩ := hru
        subst hv515
        have hv531 : v531 = .field (((u + mutUnsafeCount (.recr rc) : Nat) : F)) := by
          simpa [mutUnsafeCount, Nat.cast_add] using L1.binop_add op553
        have hv532 : v532 = .field (((n + 1 : Nat) : F)) := by
          simpa [Nat.cast_add] using L1.binop_add op569
        subst hv531 hv532
        obtain ⟨hext, hr⟩ := ih (u + mutUnsafeCount (.recr rc)) (n + 1) hrest ev529
        refine ⟨hext, ?_⟩
        rw [hr]
        simp only [List.map_cons, List.sum_cons, mutConstCount]
        congr 2 <;> [skip; congr 1] <;> congr 1 <;> congr 1 <;> omega

/-- `KernelCheck::check_block_member_kinds` enforces uniform safety across the entire mutual block:
if any member has `mutUnsafeCount m < mutConstCount m` (e.g., any single safe definition,
inductive, constructor, or recursor in the block), then every member of `ms` satisfies
`InLogicMut`, hence `InLogic cb` holds. -/
theorem check_block_member_kinds_inLogic
    {calls : List (Call F)} {E₀ : Ixon.Env} {V : IxVM.Refinement.View} {extra : List ByteArray}
    {blk : _root_.Address} {cb : Ixon.Constant} {ms : Array Ixon.MutConst}
    {x_block_addr r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (hload₀ : IxVM.Consistency.LoadedBy calls E₀)
    (hexact₀ : L1.EnvDecoded E₀)
    (hnoCol : ¬ V.HashedCollision extra calls)
    (ha : Core.S0.addr h x_block_addr blk)
    (ev : ObsFn Core.W "KernelCheck::check_block_member_kinds" [x_block_addr] h r h' cs)
    (hsub : ∀ cl ∈ cs, cl ∈ calls)
    (hrec_blk : Ix.Cert.recordAt E₀ blk = some cb)
    (hcb : cb.info = .muts ms)
    (hlt_mem : ∃ m ∈ ms.toList, mutUnsafeCount m < mutConstCount m) :
    IxVM.Consistency.InLogic cb := by
  cases Obs.«KernelCheck::check_block_member_kinds».obs ev with
  | other m2 cs12 x_info _ _ _ _ ev14 hne329 _ _ hc335 =>
    obtain ⟨_, rawBytes, c_ld, _, hh_ld, hblk_ld, _, hexact_ld, hrep, _⟩ :=
      Claim.load_verified_constant_de ha ev14
    have hsub12 : ∀ cl ∈ cs12, cl ∈ calls := fun cl hcl => hsub cl (by rw [hc335]; simp [hcl])
    have hcb_eq : cb = c_ld := loaded_recordAt_eq_of_exact_noCollision
      hexact₀ hload₀ hnoCol hrec_blk hh_ld hsub12 hblk_ld hexact_ld
    subst c_ld
    obtain ⟨infoVal, _, _, _, _, hv_c, hinfo, _, _, _, _⟩ := hrep
    injection hv_c with _ _ hargs
    simp only [List.cons.injEq] at hargs
    rw [← hargs.1, hcb] at hinfo
    obtain ⟨mv, hmv, _⟩ := hinfo
    exact absurd hmv (hne329 [mv] rfl)
  | Muts m2 cs12 _ _ _ _ x_members _ m90 _ _ m132 _ _ _ _ x_n_unsafe x_n_all v234 y243 _ _ _ _
      ev14 ev102 ev151 _ _ ev187 op258 op249 heq267 _ _ _ _ _ hc328 =>
    obtain ⟨_, rawBytes, c_ld, hsz, hh_ld, hblk_ld, _, hexact_ld, hrep, _⟩ :=
      Claim.load_verified_constant_de ha ev14
    have hsub12 : ∀ cl ∈ cs12, cl ∈ calls := fun cl hcl => hsub cl (by rw [hc328]; simp [hcl])
    have hcb_eq : cb = c_ld := loaded_recordAt_eq_of_exact_noCollision
      hexact₀ hload₀ hnoCol hrec_blk hh_ld hsub12 hblk_ld hexact_ld
    subst c_ld
    obtain ⟨infoVal, _, _, _, _, hv_c, hinfo, _, _, _, _⟩ := hrep
    injection hv_c with _ _ hargs
    simp only [List.cons.injEq] at hargs
    rw [← hargs.1, hcb] at hinfo
    obtain ⟨mv, hmv, hms_rep⟩ := hinfo
    injection hmv with _ _ hmv_args
    simp only [List.cons.injEq, and_true] at hmv_args
    subst hmv_args
    have ext_m2_132 : Heap.Extends m2 m132 := ev102.heap_extends.trans ev151.heap_extends
    have hms_rep132 :=
      Aiur.Library.List.repList_heapMono₂ _ Claim.repMutConst_heapMono₂ ext_m2_132 hms_rep
    obtain ⟨_, htup⟩ := muts_safety_counts_spec ms.toList 0 0 hms_rep132 ev187
    simp only [Nat.zero_add, Value.tuple.injEq, List.cons.injEq, and_true] at htup
    rcases htup with ⟨rfl, rfl⟩
    have hy243 := L1.binop_sub op258
    subst hy243
    have hv234 := L1.binop_mul op249
    have hmul0 :
        (((ms.toList.map mutUnsafeCount).sum : F)) *
          ((((ms.toList.map mutConstCount).sum : F)) - (((ms.toList.map mutUnsafeCount).sum : F))) = 0 :=
      Value.field.inj (hv234.symm.trans heq267)
    obtain ⟨m₀, hm₀, hlt₀⟩ := hlt_mem
    have hlt_sum : (ms.toList.map mutUnsafeCount).sum < (ms.toList.map mutConstCount).sum :=
      sum_mutUnsafeCount_lt_of_mem hm₀ hlt₀
    have hbound_sum : (ms.toList.map mutConstCount).sum < 8589934592 :=
      sum_mutConstCount_lt_bound hsz hexact_ld hcb
    rcases mul_sub_eq_zero_nat (Nat.le_of_lt hlt_sum) hbound_sum hmul0 with hu0 | hun
    · simp only [IxVM.Consistency.InLogic, hcb]
      exact (sum_mutUnsafeCount_eq_zero_iff ms.toList).mp hu0
    · omega

private theorem bool_false_of_repBoolField_zero {b : Bool}
    (h : L1.repBoolField b = .field 0) : b = false := by
  cases b with
  | false => rfl
  | true => exact absurd h (fun heq => one_ne_zero (Value.field.inj heq))

private theorem safetyDecline_eq_none_of_is_unsafe_ci_zero {d : Ixon.Definition}
    {tyPtr valPtr hint : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (ev : ObsFn Core.W "KernelCheck::is_unsafe_ci"
      [L1.defnValShape d tyPtr valPtr hint] h (.field 0) h' cs) :
    Ix.Kernel.Reader.safetyDecline d = none := by
  cases hk : d.kind with
  | thm => simp [Ix.Kernel.Reader.safetyDecline, Ix.Kernel.Reader.safetyDeclineOf, hk]
  | opaq =>
    simp only [L1.defnValShape, hk] at ev
    cases Obs.«KernelCheck::is_unsafe_ci».obs ev with
    | Opaque _ _ _ _ _ _ _ hv he _ _ =>
      simp only [Value.construct.injEq, List.cons.injEq, and_true] at hv
      rcases hv with ⟨_, _, _, _, _, hu_eq⟩
      have hf := bool_false_of_repBoolField_zero (hu_eq.trans he)
      simpa [Ix.Kernel.Reader.safetyDecline, Ix.Kernel.Reader.safetyDeclineOf, hk] using hf
    | Axiom _ _ _ hv | Defn_Safe _ _ _ _ _ hv | Defn_other _ _ _ _ _ _ hv
    | Thm _ _ _ _ _ hv | Quot _ _ _ _ _ _ _ hv
    | Induct _ _ _ _ _ _ _ _ _ _ _ _ _ hv | Ctor _ _ _ _ _ _ _ _ _ _ _ _ _ _ hv
    | Rec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hv =>
      simp [Core.kciEnum] at hv
  | defn =>
    simp only [L1.defnValShape, hk] at ev
    cases Obs.«KernelCheck::is_unsafe_ci».obs ev with
    | Defn_Safe _ _ _ _ _ hv _ _ _ =>
      simp only [Value.construct.injEq, List.cons.injEq, and_true] at hv
      rcases hv with ⟨_, _, _, _, _, hs_eq, _⟩
      have hsafe : d.safety = .safe := by
        cases hds : d.safety <;> rw [hds] at hs_eq <;> simp [L1.repDefSafetyVal] at hs_eq
        rfl
      simp [Ix.Kernel.Reader.safetyDecline, Ix.Kernel.Reader.safetyDeclineOf, hk, hsafe]
    | Defn_other _ _ _ _ _ _ _ _ he _ _ =>
      exact absurd he.symm field_zero_ne_one
    | Axiom _ _ _ hv | Thm _ _ _ _ _ hv | Opaque _ _ _ _ _ _ _ hv | Quot _ _ _ _ _ _ _ hv
    | Induct _ _ _ _ _ _ _ _ _ _ _ _ _ hv | Ctor _ _ _ _ _ _ _ _ _ _ _ _ _ _ hv
    | Rec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hv =>
      simp [Core.kciEnum] at hv

/-- Observed `Ingress::get_ci` + `KernelCheck::is_unsafe_ci = .field 0` witness at target `a`. -/
def SafeRefTargetChecked (calls : List (Call F)) (a : _root_.Address) : Prop :=
  ∃ (b_arr : Aiur.Library.Bytes.Address) (x_caddr p_ci v_ci : SourceValue F)
    (h₀ h₁ h₂ : Heap F) (cs_ci cs_u : List (Call F)),
    Core.ixAddr b_arr = a ∧
    Aiur.Library.Bytes.RepAddressRef Core.addrTy h₀ b_arr x_caddr ∧
    ObsFn Core.W "Ingress::get_ci" [x_caddr] h₀ p_ci h₁ cs_ci ∧
    (∀ cl ∈ cs_ci, cl ∈ calls) ∧
    loadValue h₁ p_ci = .ok v_ci ∧
    ObsFn Core.W "KernelCheck::is_unsafe_ci" [v_ci] h₁ (.field 0) h₂ cs_u

/-- Extract `KernelCheck::check_block_member_kinds` on `blk` from an inductive member check
`MutsMemberCheckedAtFull calls bAddr t blk ms i` with `ms[i]? = some (.indc ind)`. -/
private theorem ind_block_checked_member_kinds
    {calls : List (Call F)} {bAddr blk : _root_.Address} {t : Ix.Kernel.RoleTable}
    {E₀ : Ixon.Env} {V : IxVM.Refinement.View} {extra : List ByteArray}
    {cb : Ixon.Constant} {ms : Array Ixon.MutConst} {i : Nat} {ind : Ixon.Inductive}
    (hbound : IxVM.Consistency.Bounded calls)
    (hload₀ : IxVM.Consistency.LoadedBy calls E₀)
    (hexact₀ : L1.EnvDecoded E₀)
    (hnoCol : ¬ V.HashedCollision extra calls)
    (hrec_blk : Ix.Cert.recordAt E₀ blk = some cb)
    (hcb : cb.info = .muts ms)
    (hms_i : ms[i]? = some (.indc ind))
    (hm_i : Claim.MutsMemberCheckedAtFull calls bAddr t blk ms i) :
    ∃ (x_blk r : SourceValue F) (h h' : Heap F) (cs : List (Call F)),
      Core.S0.addr h x_blk blk ∧
      ObsFn Core.W "KernelCheck::check_block_member_kinds" [x_blk] h r h' cs ∧
      (∀ cl ∈ cs, cl ∈ calls) := by
  obtain ⟨hi_u64, hstore_iprj⟩ := iprj_store_eq_of_mutsMemberChecked hbound hnoCol hm_i hms_i
  have hchk_iprj : Claim.CheckedAtFull calls bAddr t (Core.iprjAddr blk i) := by
    have h0 := mutsMemberCheckedAtFull_to_checkedAtFull hbound hm_i hms_i
    simpa only [Core.Specs.Callees.memberProjInfo, Core.iprjAddr] using h0
  obtain ⟨_, _, m_chk, _, rc, ap, ptr, v, r_chk, cs_ld, cs_chk, bytes_i, E_ld,
    _, _, _, _, hhash_i, hblake_i, hload_ld, hL1_i, hsub_ld, hld_v, ev_chk, _, hsub_chk⟩ :=
    checkedAtFull_loadedL1 hbound hchk_iprj
  obtain ⟨c_i, hdec_i, _, _, v', hld_v', hraw_i⟩ := hL1_i
  have hv_eq : v' = v := Except.ok.inj (hld_v'.symm.trans hld_v)
  subst v'
  have hc_i_eq : c_i = ⟨.iPrj ⟨i.toUInt64, blk⟩, #[], #[], #[], #[]⟩ :=
    hstore_iprj bytes_i c_i hblake_i hdec_i (.inr (.inr (Core.hashed_mono hsub_ld hhash_i)))
  subst c_i
  have hi_toNat : i.toUInt64.toNat = i := Nat.mod_eq_of_lt hi_u64
  simp only [L1.RawCIRep, hi_toNat] at hraw_i
  obtain ⟨_, lcB, cb_ld, ms_ld, ind_ld, _, hget_lcB, _, _, hexact_lcB, _,
    hcb_ld, hms_ld, _, hraw_ind⟩ := hraw_i
  obtain ⟨hhash_lcB, hblake_lcB⟩ := hload_ld.1 blk lcB hget_lcB
  have hcb_eq_ld : cb = cb_ld := loaded_recordAt_eq_of_exact_noCollision
    hexact₀ hload₀ hnoCol hrec_blk hhash_lcB hsub_ld hblake_lcB hexact_lcB
  subst cb_ld
  rw [hcb] at hcb_ld
  injection hcb_ld with hms_ld_eq
  subst ms_ld
  obtain ⟨_, _, _, _, _, _, blkPtr, b_arr, hb_eq, hbp_m, rfl, _⟩ := hraw_ind
  match Obs.«KernelCheck::check_const».obs ev_chk with
  | .Axiom_n1 (hv37 := hv) .. | .Axiom_other_n0 (hv37 := hv) ..
  | .Axiom_other_other (hv37 := hv) ..
  | .Defn (hv269 := hv) .. | .Thm (hv526 := hv) ..
  | .Opaque (hv825 := hv) .. | .Quot (hv1076 := hv) ..
  | .Ctor_n0_n0 (hv1884 := hv) .. | .Ctor_n0_other (hv1884 := hv) ..
  | .Ctor_other_n0 (hv1884 := hv) .. | .Ctor_other_other (hv1884 := hv) ..
  | .Rec_n0 (hv2574 := hv) .. | .Rec_other (hv2574 := hv) .. =>
    injection hv with _ htag _; exact absurd htag (by decide)
  | .Induct_n0 (x_ind_block := xblk) (m1354 := m1354) (m1376 := m1376)
      (m1427 := m1427) (m1440 := m1440) (v1469 := r_mk) (m1470 := m_mk) (cs1480 := cs_mk)
      (ev14 := ev1) (hv1240 := hv_ind) (ev1295 := ev2)
      (hm1362 := hm1354) (hm1384 := hm1376) (ev1343 := ev3)
      (hm1435 := hm1427) (ev1408 := ev4) (ev1452 := ev5)
      (ev1482 := ev_mk) (hc1634 := hc) ..
  | .Induct_other_n0 (x_ind_block := xblk) (m1354 := m1354) (m1376 := m1376)
      (m1427 := m1427) (m1440 := m1440) (v1469 := r_mk) (m1470 := m_mk) (cs1480 := cs_mk)
      (ev14 := ev1) (hv1240 := hv_ind) (ev1295 := ev2)
      (hm1362 := hm1354) (hm1384 := hm1376) (ev1343 := ev3)
      (hm1435 := hm1427) (ev1408 := ev4) (ev1452 := ev5)
      (ev1482 := ev_mk) (hc1869 := hc) ..
  | .Induct_other_other (x_ind_block := xblk) (m1354 := m1354) (m1376 := m1376)
      (m1427 := m1427) (m1440 := m1440) (v1469 := r_mk) (m1470 := m_mk) (cs1480 := cs_mk)
      (ev14 := ev1) (hv1240 := hv_ind) (ev1295 := ev2)
      (hm1362 := hm1354) (hm1384 := hm1376) (ev1343 := ev3)
      (hm1435 := hm1427) (ev1408 := ev4) (ev1452 := ev5)
      (ev1482 := ev_mk) (hc1878 := hc) .. =>
    injection hv_ind with _ _ hargs
    injection hargs with _ hargs; injection hargs with _ hargs
    injection hargs with _ hargs; injection hargs with _ hargs
    injection hargs with _ hargs; injection hargs with _ hargs
    injection hargs with hblk _
    subst hblk
    have e_1376 : Heap.Extends _ m1376 := by rw [hm1376]; exact Heap.Extends.snoc _ _
    have e_1354 : Heap.Extends m1376 m1354 := by rw [hm1354]; exact Heap.Extends.snoc _ _
    have e_1427 : Heap.Extends _ m1427 := by rw [hm1427]; exact Heap.Extends.snoc _ _
    have hext : Heap.Extends m_chk m1440 :=
      ev1.heap_extends.trans (ev2.heap_extends.trans
        (e_1376.trans (e_1354.trans (ev3.heap_extends.trans
          (e_1427.trans (ev4.heap_extends.trans ev5.heap_extends))))))
    exact ⟨blkPtr, r_mk, m1440, m_mk, cs_mk,
      ⟨b_arr, Aiur.Library.Bytes.repAddressRef_heapMono₂ Core.addrTy hext hbp_m, hb_eq⟩,
      ev_mk, fun cl hcl => hsub_chk cl (by rw [hc]; simp [hcl])⟩

/-- Extract `KernelCheck::check_block_member_kinds` on `blk` from a recursor member check
`MutsMemberCheckedAtFull calls bAddr t blk ms i` with `ms[i]? = some (.recr rc)`. -/
private theorem rec_block_checked_member_kinds
    {calls : List (Call F)} {bAddr blk : _root_.Address} {t : Ix.Kernel.RoleTable}
    {E₀ : Ixon.Env} {V : IxVM.Refinement.View} {extra : List ByteArray}
    {cb : Ixon.Constant} {ms : Array Ixon.MutConst} {i : Nat} {rc_m : Ixon.Recursor}
    (hbound : IxVM.Consistency.Bounded calls)
    (hload₀ : IxVM.Consistency.LoadedBy calls E₀)
    (hexact₀ : L1.EnvDecoded E₀)
    (hnoCol : ¬ V.HashedCollision extra calls)
    (hrec_blk : Ix.Cert.recordAt E₀ blk = some cb)
    (hcb : cb.info = .muts ms)
    (hms_i : ms[i]? = some (.recr rc_m))
    (hm_i : Claim.MutsMemberCheckedAtFull calls bAddr t blk ms i) :
    ∃ (x_blk r : SourceValue F) (h h' : Heap F) (cs : List (Call F)),
      Core.S0.addr h x_blk blk ∧
      ObsFn Core.W "KernelCheck::check_block_member_kinds" [x_blk] h r h' cs ∧
      (∀ cl ∈ cs, cl ∈ calls) := by
  obtain ⟨hi_u64, hstore_rprj⟩ := rprj_store_eq_of_mutsMemberChecked hbound hnoCol hm_i hms_i
  have hchk_rprj : Claim.CheckedAtFull calls bAddr t (Core.rprjAddr blk i) := by
    have h0 := mutsMemberCheckedAtFull_to_checkedAtFull hbound hm_i hms_i
    simpa only [Core.Specs.Callees.memberProjInfo, Core.rprjAddr] using h0
  obtain ⟨_, _, m_chk, _, rc, ap, ptr, v, r_chk, cs_ld, cs_chk, bytes_r, E_ld,
    _, _, _, _, hhash_r, hblake_r, hload_ld, hL1_r, hsub_ld, hld_v, ev_chk, _, hsub_chk⟩ :=
    checkedAtFull_loadedL1 hbound hchk_rprj
  obtain ⟨c_r, hdec_r, _, _, v', hld_v', hraw_r⟩ := hL1_r
  have hv_eq : v' = v := Except.ok.inj (hld_v'.symm.trans hld_v)
  subst v'
  have hc_r_eq : c_r = ⟨.rPrj ⟨i.toUInt64, blk⟩, #[], #[], #[], #[]⟩ :=
    hstore_rprj bytes_r c_r hblake_r hdec_r (.inr (.inr (Core.hashed_mono hsub_ld hhash_r)))
  subst c_r
  have hi_toNat : i.toUInt64.toNat = i := Nat.mod_eq_of_lt hi_u64
  simp only [L1.RawCIRep, hi_toNat] at hraw_r
  obtain ⟨_, lcB, cb_ld, ms_ld, _, _, hget_lcB, _, _, hexact_lcB, _,
    hcb_ld, _, _, hraw_rc⟩ := hraw_r
  obtain ⟨hhash_lcB, hblake_lcB⟩ := hload_ld.1 blk lcB hget_lcB
  have hcb_eq_ld : cb = cb_ld := loaded_recordAt_eq_of_exact_noCollision
    hexact₀ hload₀ hnoCol hrec_blk hhash_lcB hsub_ld hblake_lcB hexact_lcB
  subst cb_ld
  rw [hcb] at hcb_ld
  injection hcb_ld with hms_ld_eq
  subst ms_ld
  obtain ⟨_, _, _, _, _, _, _, _, blkPtr, b_arr, hb_eq, hbp_m, rfl, _, _⟩ := hraw_rc
  match Obs.«KernelCheck::check_const».obs ev_chk with
  | .Axiom_n1 (hv37 := hv) .. | .Axiom_other_n0 (hv37 := hv) ..
  | .Axiom_other_other (hv37 := hv) ..
  | .Defn (hv269 := hv) .. | .Thm (hv526 := hv) ..
  | .Opaque (hv825 := hv) .. | .Quot (hv1076 := hv) ..
  | .Induct_n0 (hv1240 := hv) .. | .Induct_other_n0 (hv1240 := hv) ..
  | .Induct_other_other (hv1240 := hv) ..
  | .Ctor_n0_n0 (hv1884 := hv) .. | .Ctor_n0_other (hv1884 := hv) ..
  | .Ctor_other_n0 (hv1884 := hv) .. | .Ctor_other_other (hv1884 := hv) .. =>
    injection hv with _ htag _; exact absurd htag (by decide)
  | .Rec_n0 (x_rec_block := xblk) (m2705 := m2705) (m2718 := m2718)
      (v2747 := r_mk) (m2748 := m_mk) (cs2758 := cs_mk)
      (ev14 := ev1) (hv2574 := hv_rec) (ev2649 := ev2)
      (hm2713 := hm2705) (ev2686 := ev3) (ev2730 := ev4)
      (ev2760 := ev_mk) (hc2875 := hc) ..
  | .Rec_other (x_rec_block := xblk) (m2705 := m2705) (m2718 := m2718)
      (v2747 := r_mk) (m2748 := m_mk) (cs2758 := cs_mk)
      (ev14 := ev1) (hv2574 := hv_rec) (ev2649 := ev2)
      (hm2713 := hm2705) (ev2686 := ev3) (ev2730 := ev4)
      (ev2760 := ev_mk) (hc2964 := hc) .. =>
    injection hv_rec with _ _ hargs
    injection hargs with _ hargs; injection hargs with _ hargs
    injection hargs with _ hargs; injection hargs with _ hargs
    injection hargs with _ hargs; injection hargs with _ hargs
    injection hargs with _ hargs; injection hargs with _ hargs
    injection hargs with _ hargs; injection hargs with hblk _
    subst hblk
    have e_2705 : Heap.Extends _ m2705 := by rw [hm2705]; exact Heap.Extends.snoc _ _
    have hext : Heap.Extends m_chk m2718 :=
      ev1.heap_extends.trans (ev2.heap_extends.trans
        (e_2705.trans (ev3.heap_extends.trans ev4.heap_extends)))
    exact ⟨blkPtr, r_mk, m2718, m_mk, cs_mk,
      ⟨b_arr, Aiur.Library.Bytes.repAddressRef_heapMono₂ Core.addrTy hext hbp_m, hb_eq⟩,
      ev_mk, fun cl hcl => hsub_chk cl (by rw [hc]; simp [hcl])⟩

/-- **Unconditional target resolution & safety for any walked `SafeRefTargetChecked` constant**
across all 8 non-`muts` `ConstantInfo` variants (`defn`, `recr`, `axio`, `quot`, `dPrj`, `iPrj`,
`rPrj`, `cPrj`). -/
theorem safeRefTargetChecked_resolve_and_not_outside
    {calls : List (Call F)} {bAddr : _root_.Address} {t : Ix.Kernel.RoleTable}
    {E₀ : Ixon.Env} {V : IxVM.Refinement.View} {extra : List ByteArray}
    {a : _root_.Address}
    (hbound : IxVM.Consistency.Bounded calls)
    (hload₀ : IxVM.Consistency.LoadedBy calls E₀)
    (hexact₀ : L1.EnvDecoded E₀)
    (hnoCol : ¬ V.HashedCollision extra calls)
    (hchk_ref : SafeRefTargetChecked calls a)
    (hwk_a : WkAll calls bAddr t E₀ a) :
    ¬ IxVM.Consistency.OutsideLogicAt E₀ a ∧
      ∀ c_a, Ix.Cert.recordAt E₀ a = some c_a →
        (Ix.Kernel.Reader.resolveSource (Ix.Cert.recordAt E₀) a c_a).isSome = true := by
  obtain ⟨b_arr, x_caddr, p_ci, v_ci, h₀, h₁, h₂, cs_ci, cs_u,
    hb_eq, ra, ev_ci, hsub_ci, hld_pci, ev_u⟩ := hchk_ref
  obtain ⟨c_a0, hrec_a0, _⟩ := (wkAll_closedSubwalk calls bAddr t E₀).checked a hwk_a
  obtain ⟨_, bytes_ld, E_ld, hhash_ld, hblake_ld, hload_ld,
    c_ld, hexact_ld, _, htv_ld, v_ld, hld_v, hraw_ld⟩ :=
    L1.get_ci_loadedL1_spec (RomBound.bounded_mono hbound hsub_ci) ra ev_ci
  have hv_eq : v_ld = v_ci := Except.ok.inj (hld_v.symm.trans hld_pci)
  subst hv_eq
  rw [hb_eq] at hblake_ld
  rw [hblake_ld] at hraw_ld
  obtain ⟨_, _, _, _, hinlogic⟩ := L1.is_unsafe_ci_raw_spec hraw_ld ev_u
  have hca_eq : c_a0 = c_ld := loaded_recordAt_eq_of_exact_noCollision
    hexact₀ hload₀ hnoCol hrec_a0 hhash_ld hsub_ci hblake_ld hexact_ld
  subst c_ld
  have hno_muts : ∀ ms, c_a0.info ≠ .muts ms := by
    intro ms hms
    simp only [L1.RawCIRep, hms] at hraw_ld
  have hres_and_safe :
      ¬ IxVM.Consistency.OutsideLogicAt E₀ a ∧
      (Ix.Kernel.Reader.resolveSource (Ix.Cert.recordAt E₀) a c_a0).isSome = true := by
    cases hinfo : c_a0.info with
    | muts ms => exact absurd hinfo (hno_muts ms)
    | defn _ | recr _ | axio _ | quot _ =>
      have hown : Ix.Cert.ownerOf a c_a0 = a := by simp [Ix.Cert.ownerOf, hinfo]
      have hinl : IxVM.Consistency.InLogic c_a0 := hinlogic rfl hown
      have hnot_out : ¬ IxVM.Consistency.OutsideLogicAt E₀ a := by
        rintro ⟨c_x, hrec_x, hnot_c | ⟨cb_x, hrec_cb, hnot_cb⟩⟩
        · have hcx : c_x = c_a0 := Option.some.inj (hrec_x.symm.trans hrec_a0)
          rw [hcx] at hnot_c; exact hnot_c hinl
        · have hcx : c_x = c_a0 := Option.some.inj (hrec_x.symm.trans hrec_a0)
          rw [hcx, hown] at hrec_cb
          have hcb : cb_x = c_a0 := Option.some.inj (hrec_cb.symm.trans hrec_a0)
          rw [hcb] at hnot_cb; exact hnot_cb hinl
      exact ⟨hnot_out, by simp [Ix.Kernel.Reader.resolveSource, hinfo]⟩
    | dPrj p =>
      have hemp := emptyTables_of_constantTablesValid_prj htv_ld (.inl ⟨p, hinfo⟩)
      simp only [L1.RawCIRep, hinfo] at hraw_ld
      obtain ⟨_, lcB, cb_ld, ms_ld, d_ld, _, hget_B, _, _, hexact_B, _, hcb_ld, hms_ld, _, hraw_d⟩ := hraw_ld
      obtain ⟨hhash_B, hblake_B⟩ := hload_ld.1 p.block lcB hget_B
      have hp_ne : p.block ≠ a := by
        intro hp_eq
        rw [hp_eq] at hblake_B
        have hcb_eq := loaded_recordAt_eq_of_exact_noCollision
          hexact₀ hload₀ hnoCol hrec_a0 hhash_B hsub_ci hblake_B hexact_B
        exact hno_muts ms_ld ((congrArg Ixon.Constant.info hcb_eq).trans hcb_ld)
      have hedge : Core.S0.WalkEdge E₀ a p.block :=
        ⟨c_a0, hrec_a0, .inl ⟨by simp [Ix.Cert.ownerOf, hinfo], hp_ne⟩⟩
      obtain ⟨hwk_blk, _⟩ := (wkAll_closedSubwalk calls bAddr t E₀).step a p.block hwk_a hedge
      obtain ⟨cb₀, hrec_cb₀, _⟩ := (wkAll_closedSubwalk calls bAddr t E₀).checked p.block hwk_blk
      have hcb_eq : cb₀ = cb_ld := loaded_recordAt_eq_of_exact_noCollision
        hexact₀ hload₀ hnoCol hrec_cb₀ hhash_B hsub_ci hblake_B hexact_B
      subst cb_ld
      obtain ⟨_, _, _, _, rfl, _, _⟩ := hraw_d
      have hsafe_d := safetyDecline_eq_none_of_is_unsafe_ci_zero ev_u
      have hlt_d : mutUnsafeCount (.defn d_ld) < mutConstCount (.defn d_ld) := by
        simp [mutUnsafeCount, mutConstCount, hsafe_d]
      have hmk_dprj : ∃ (x_blk r : SourceValue F) (h h' : Heap F) (cs : List (Call F)),
          Core.S0.addr h x_blk p.block ∧
          ObsFn Core.W "KernelCheck::check_block_member_kinds" [x_blk] h r h' cs ∧
          (∀ cl ∈ cs, cl ∈ calls) := by
        cases Obs.«Ingress::get_ci».obs ev_ci with
        | Defn _ cs12 _ _ _ _ _ _ _ _ _ ev14 _ _ _ _ hc
        | Axio _ cs12 _ _ _ _ _ _ _ _ _ ev14 _ _ _ _ hc
        | Quot _ cs12 _ _ _ _ _ _ _ _ _ ev14 _ _ _ _ _ hc
        | IPrj _ cs12 _ _ _ _ _ _ _ _ _ _ ev14 _ _ hc
        | CPrj _ cs12 _ _ _ _ _ _ _ _ _ _ _ _ _ ev14 _ _ _ hc
        | RPrj _ cs12 _ _ _ _ _ _ _ _ _ _ ev14 _ _ hc
        | Recr _ cs12 _ _ _ _ _ _ _ _ _ _ _ _ _ ev14 _ _ _ _ _ _ hc =>
          obtain ⟨_, _, c_x, _, hh_x, hbl_x, _, hex_x, hrep_x, _⟩ :=
            Claim.load_verified_constant_de ⟨b_arr, ra, hb_eq⟩ ev14
          have hsub12 : ∀ cl ∈ cs12, cl ∈ calls :=
            fun cl hcl => hsub_ci cl (by rw [hc]; simp [hcl])
          have hcx_eq : c_a0 = c_x := loaded_recordAt_eq_of_exact_noCollision
            hexact₀ hload₀ hnoCol hrec_a0 hh_x hsub12 hbl_x hex_x
          subst c_x
          obtain ⟨infoVal, _, _, _, _, hv_c, hinfo_r, _, _, _, _⟩ := hrep_x
          injection hv_c with _ _ hargs
          simp only [List.cons.injEq] at hargs
          rw [← hargs.1, hinfo] at hinfo_r
          obtain ⟨_, hv_bad, _⟩ := hinfo_r
          simp at hv_bad
        | DPrj m2 cs12 _ _ _ _ x_idx x_block_addr cs648 ev14 ev650 hc675 =>
          obtain ⟨_, _, c_x, _, hh_x, hbl_x, _, hex_x, hrep_x, _⟩ :=
            Claim.load_verified_constant_de ⟨b_arr, ra, hb_eq⟩ ev14
          have hsub12 : ∀ cl ∈ cs12, cl ∈ calls :=
            fun cl hcl => hsub_ci cl (by rw [hc675]; simp [hcl])
          have hcx_eq : c_a0 = c_x := loaded_recordAt_eq_of_exact_noCollision
            hexact₀ hload₀ hnoCol hrec_a0 hh_x hsub12 hbl_x hex_x
          subst c_x
          obtain ⟨infoVal, _, _, _, _, hv_c, hinfo_r, _, _, _, _⟩ := hrep_x
          injection hv_c with _ _ hargs
          simp only [List.cons.injEq] at hargs
          rw [← hargs.1, hinfo] at hinfo_r
          obtain ⟨pv, hpv, blkPtr, hdp, hblk_addr⟩ := hinfo_r
          injection hpv with _ _ hpv_args
          simp only [List.cons.injEq, and_true] at hpv_args
          rw [← hpv_args] at hdp
          injection hdp with _ _ hdp_args
          simp only [List.cons.injEq, and_true] at hdp_args
          rcases hdp_args with ⟨_, rfl⟩
          cases Obs.«Ingress::get_ci_dprj».obs ev650 with
          | run v1 m2' cs12' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ev_mk _ _ _ _ _ _ _ _ _ _ hc348 =>
            exact ⟨blkPtr, v1, m2, m2', cs12', hblk_addr, ev_mk,
              fun cl hcl => hsub_ci cl (by rw [hc675, hc348]; simp [hcl])⟩
      obtain ⟨x_blk, r_mk, h_mk, h'_mk, cs_mk, ha_blk, ev_mk, hsub_mk⟩ := hmk_dprj
      have hinl_cb : IxVM.Consistency.InLogic cb₀ :=
        check_block_member_kinds_inLogic hload₀ hexact₀ hnoCol ha_blk ev_mk hsub_mk
          hrec_cb₀ hcb_ld ⟨.defn d_ld, List.mem_of_getElem? hms_ld, hlt_d⟩
      have hnot_out : ¬ IxVM.Consistency.OutsideLogicAt E₀ a := by
        rintro ⟨c_x, hrec_x, hnot_c | ⟨cb_x, hrec_cbx, hnot_cbx⟩⟩
        · have hcx : c_x = c_a0 := Option.some.inj (hrec_x.symm.trans hrec_a0)
          rw [hcx] at hnot_c; exact hnot_c (by simp [IxVM.Consistency.InLogic, hinfo])
        · have hcx : c_x = c_a0 := Option.some.inj (hrec_x.symm.trans hrec_a0)
          rw [hcx] at hrec_cbx; simp only [Ix.Cert.ownerOf, hinfo] at hrec_cbx
          have hcbx : cb_x = cb₀ := Option.some.inj (hrec_cbx.symm.trans hrec_cb₀)
          rw [hcbx] at hnot_cbx; exact hnot_cbx hinl_cb
      have hms_arr : ms_ld[p.idx.toNat]? = some (.defn d_ld) := by simpa using hms_ld
      exact ⟨hnot_out, by simp [Ix.Kernel.Reader.resolveSource, hinfo, hemp, hrec_cb₀, hcb_ld, hms_arr]⟩
    | iPrj p =>
      have hemp := emptyTables_of_constantTablesValid_prj htv_ld (.inr (.inl ⟨p, hinfo⟩))
      simp only [L1.RawCIRep, hinfo] at hraw_ld
      obtain ⟨_, lcB, cb_ld, ms_ld, ind_ld, _, hget_B, _, _, hexact_B, _, hcb_ld, hms_ld, _, hraw_ind⟩ := hraw_ld
      obtain ⟨hhash_B, hblake_B⟩ := hload_ld.1 p.block lcB hget_B
      have hp_ne : p.block ≠ a := by
        intro hp_eq
        rw [hp_eq] at hblake_B
        have hcb_eq := loaded_recordAt_eq_of_exact_noCollision
          hexact₀ hload₀ hnoCol hrec_a0 hhash_B hsub_ci hblake_B hexact_B
        exact hno_muts ms_ld ((congrArg Ixon.Constant.info hcb_eq).trans hcb_ld)
      have hedge : Core.S0.WalkEdge E₀ a p.block :=
        ⟨c_a0, hrec_a0, .inl ⟨by simp [Ix.Cert.ownerOf, hinfo], hp_ne⟩⟩
      obtain ⟨hwk_blk, _⟩ := (wkAll_closedSubwalk calls bAddr t E₀).step a p.block hwk_a hedge
      obtain ⟨cb₀, hrec_cb₀, hchk_or⟩ := (wkAll_closedSubwalk calls bAddr t E₀).checked p.block hwk_blk
      have hcb_eq : cb₀ = cb_ld := loaded_recordAt_eq_of_exact_noCollision
        hexact₀ hload₀ hnoCol hrec_cb₀ hhash_B hsub_ci hblake_B hexact_B
      subst cb_ld
      have hms_arr : ms_ld[p.idx.toNat]? = some (.indc ind_ld) := by simpa using hms_ld
      have hm_i : Claim.MutsMemberCheckedAtFull calls bAddr t p.block ms_ld p.idx.toNat := by
        rcases hchk_or with ⟨ms', hms'_eq, hmem_chk⟩ | hchk_blk
        · rw [hcb_ld] at hms'_eq; injection hms'_eq with hms'_eq'; subst ms'
          exact hmem_chk _ (Array.getElem?_eq_some_iff.mp hms_arr).1
        · obtain ⟨_, _, _, _, _, _, _, _, _, cs_b, _, bytes_b, _,
            _, _, _, _, hhash_b, hblake_b, _, hL1_b, hsub_b, _, _, _, _⟩ :=
            checkedAtFull_loadedL1 hbound hchk_blk
          obtain ⟨c_b, hdec_b, _, _, _, _, hraw_b⟩ := hL1_b
          have hcb_eq_b := loaded_recordAt_eq_of_exact_noCollision
            hexact₀ hload₀ hnoCol hrec_cb₀ hhash_b hsub_b hblake_b hdec_b
          subst c_b; simp only [L1.RawCIRep, hcb_ld] at hraw_b
      obtain ⟨_, _, _, _, _, _, _, _, _, _, rfl, _⟩ := hraw_ind
      have hind_safe : ind_ld.isUnsafe = false := by
        cases Obs.«KernelCheck::is_unsafe_ci».obs ev_u with
        | Induct _ _ _ _ _ _ _ _ _ _ _ _ _ hv he _ _ =>
          simp only [Value.construct.injEq, List.cons.injEq, and_true] at hv
          rcases hv with ⟨_, _, _, _, _, _, _, hu_eq, _, _⟩
          exact bool_false_of_repBoolField_zero (hu_eq.trans he)
        | Axiom _ _ _ hv | Defn_Safe _ _ _ _ _ hv | Defn_other _ _ _ _ _ _ hv
        | Thm _ _ _ _ _ hv | Opaque _ _ _ _ _ _ _ hv | Quot _ _ _ _ _ _ _ hv
        | Ctor _ _ _ _ _ _ _ _ _ _ _ _ _ _ hv | Rec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hv =>
          simp [Core.kciEnum] at hv
      have hlt_ind : mutUnsafeCount (.indc ind_ld) < mutConstCount (.indc ind_ld) := by
        have hle := sum_ctorUnsafeBit_le_length ind_ld.ctors.toList
        simp only [mutUnsafeCount, mutConstCount, hind_safe]; omega
      obtain ⟨x_blk, r_mk, h_mk, h'_mk, cs_mk, ha_blk, ev_mk, hsub_mk⟩ :=
        ind_block_checked_member_kinds hbound hload₀ hexact₀ hnoCol hrec_cb₀ hcb_ld hms_arr hm_i
      have hinl_cb : IxVM.Consistency.InLogic cb₀ :=
        check_block_member_kinds_inLogic hload₀ hexact₀ hnoCol ha_blk ev_mk hsub_mk
          hrec_cb₀ hcb_ld ⟨.indc ind_ld, List.mem_of_getElem? hms_ld, hlt_ind⟩
      have hnot_out : ¬ IxVM.Consistency.OutsideLogicAt E₀ a := by
        rintro ⟨c_x, hrec_x, hnot_c | ⟨cb_x, hrec_cbx, hnot_cbx⟩⟩
        · have hcx : c_x = c_a0 := Option.some.inj (hrec_x.symm.trans hrec_a0)
          rw [hcx] at hnot_c; exact hnot_c (by simp [IxVM.Consistency.InLogic, hinfo])
        · have hcx : c_x = c_a0 := Option.some.inj (hrec_x.symm.trans hrec_a0)
          rw [hcx] at hrec_cbx; simp only [Ix.Cert.ownerOf, hinfo] at hrec_cbx
          have hcbx : cb_x = cb₀ := Option.some.inj (hrec_cbx.symm.trans hrec_cb₀)
          rw [hcbx] at hnot_cbx; exact hnot_cbx hinl_cb
      exact ⟨hnot_out, by simp [Ix.Kernel.Reader.resolveSource, hinfo, hemp, hrec_cb₀, hcb_ld, hms_arr]⟩
    | rPrj p =>
      have hemp := emptyTables_of_constantTablesValid_prj htv_ld (.inr (.inr (.inl ⟨p, hinfo⟩)))
      simp only [L1.RawCIRep, hinfo] at hraw_ld
      obtain ⟨_, lcB, cb_ld, ms_ld, rc_ld, _, hget_B, _, _, hexact_B, _, hcb_ld, hms_ld, _, hraw_rc⟩ := hraw_ld
      obtain ⟨hhash_B, hblake_B⟩ := hload_ld.1 p.block lcB hget_B
      have hp_ne : p.block ≠ a := by
        intro hp_eq
        rw [hp_eq] at hblake_B
        have hcb_eq := loaded_recordAt_eq_of_exact_noCollision
          hexact₀ hload₀ hnoCol hrec_a0 hhash_B hsub_ci hblake_B hexact_B
        exact hno_muts ms_ld ((congrArg Ixon.Constant.info hcb_eq).trans hcb_ld)
      have hedge : Core.S0.WalkEdge E₀ a p.block :=
        ⟨c_a0, hrec_a0, .inl ⟨by simp [Ix.Cert.ownerOf, hinfo], hp_ne⟩⟩
      obtain ⟨hwk_blk, _⟩ := (wkAll_closedSubwalk calls bAddr t E₀).step a p.block hwk_a hedge
      obtain ⟨cb₀, hrec_cb₀, hchk_or⟩ := (wkAll_closedSubwalk calls bAddr t E₀).checked p.block hwk_blk
      have hcb_eq : cb₀ = cb_ld := loaded_recordAt_eq_of_exact_noCollision
        hexact₀ hload₀ hnoCol hrec_cb₀ hhash_B hsub_ci hblake_B hexact_B
      subst cb_ld
      have hms_arr : ms_ld[p.idx.toNat]? = some (.recr rc_ld) := by simpa using hms_ld
      have hm_i : Claim.MutsMemberCheckedAtFull calls bAddr t p.block ms_ld p.idx.toNat := by
        rcases hchk_or with ⟨ms', hms'_eq, hmem_chk⟩ | hchk_blk
        · rw [hcb_ld] at hms'_eq; injection hms'_eq with hms'_eq'; subst ms'
          exact hmem_chk _ (Array.getElem?_eq_some_iff.mp hms_arr).1
        · obtain ⟨_, _, _, _, _, _, _, _, _, cs_b, _, bytes_b, _,
            _, _, _, _, hhash_b, hblake_b, _, hL1_b, hsub_b, _, _, _, _⟩ :=
            checkedAtFull_loadedL1 hbound hchk_blk
          obtain ⟨c_b, hdec_b, _, _, _, _, hraw_b⟩ := hL1_b
          have hcb_eq_b := loaded_recordAt_eq_of_exact_noCollision
            hexact₀ hload₀ hnoCol hrec_cb₀ hhash_b hsub_b hblake_b hdec_b
          subst c_b; simp only [L1.RawCIRep, hcb_ld] at hraw_b
      obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, rfl, _, _⟩ := hraw_rc
      have hrc_safe : rc_ld.isUnsafe = false := by
        cases Obs.«KernelCheck::is_unsafe_ci».obs ev_u with
        | Rec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hv he _ _ =>
          simp only [Value.construct.injEq, List.cons.injEq, and_true] at hv
          rcases hv with ⟨_, _, _, _, _, _, _, _, _, _, hu_eq, _, _⟩
          exact bool_false_of_repBoolField_zero (hu_eq.trans he)
        | Axiom _ _ _ hv | Defn_Safe _ _ _ _ _ hv | Defn_other _ _ _ _ _ _ hv
        | Thm _ _ _ _ _ hv | Opaque _ _ _ _ _ _ _ hv | Quot _ _ _ _ _ _ _ hv
        | Induct _ _ _ _ _ _ _ _ _ _ _ _ _ hv | Ctor _ _ _ _ _ _ _ _ _ _ _ _ _ _ hv =>
          simp [Core.kciEnum] at hv
      have hlt_rc : mutUnsafeCount (.recr rc_ld) < mutConstCount (.recr rc_ld) := by
        simp [mutUnsafeCount, mutConstCount, hrc_safe]
      obtain ⟨x_blk, r_mk, h_mk, h'_mk, cs_mk, ha_blk, ev_mk, hsub_mk⟩ :=
        rec_block_checked_member_kinds hbound hload₀ hexact₀ hnoCol hrec_cb₀ hcb_ld hms_arr hm_i
      have hinl_cb : IxVM.Consistency.InLogic cb₀ :=
        check_block_member_kinds_inLogic hload₀ hexact₀ hnoCol ha_blk ev_mk hsub_mk
          hrec_cb₀ hcb_ld ⟨.recr rc_ld, List.mem_of_getElem? hms_ld, hlt_rc⟩
      have hnot_out : ¬ IxVM.Consistency.OutsideLogicAt E₀ a := by
        rintro ⟨c_x, hrec_x, hnot_c | ⟨cb_x, hrec_cbx, hnot_cbx⟩⟩
        · have hcx : c_x = c_a0 := Option.some.inj (hrec_x.symm.trans hrec_a0)
          rw [hcx] at hnot_c; exact hnot_c (by simp [IxVM.Consistency.InLogic, hinfo])
        · have hcx : c_x = c_a0 := Option.some.inj (hrec_x.symm.trans hrec_a0)
          rw [hcx] at hrec_cbx; simp only [Ix.Cert.ownerOf, hinfo] at hrec_cbx
          have hcbx : cb_x = cb₀ := Option.some.inj (hrec_cbx.symm.trans hrec_cb₀)
          rw [hcbx] at hnot_cbx; exact hnot_cbx hinl_cb
      exact ⟨hnot_out, by simp [Ix.Kernel.Reader.resolveSource, hinfo, hemp, hrec_cb₀, hcb_ld, hms_arr]⟩
    | cPrj p =>
      have hemp := emptyTables_of_constantTablesValid_prj htv_ld (.inr (.inr (.inr ⟨p, hinfo⟩)))
      simp only [L1.RawCIRep, hinfo] at hraw_ld
      obtain ⟨_, _, lcB, cb_ld, ms_ld, ind_ld, ct_ld, _,
        hget_B, _, _, hexact_B, _, hcb_ld, hms_ld, hct_ld, _, hraw_ct⟩ := hraw_ld
      obtain ⟨hhash_B, hblake_B⟩ := hload_ld.1 p.block lcB hget_B
      have hp_ne : p.block ≠ a := by
        intro hp_eq
        rw [hp_eq] at hblake_B
        have hcb_eq := loaded_recordAt_eq_of_exact_noCollision
          hexact₀ hload₀ hnoCol hrec_a0 hhash_B hsub_ci hblake_B hexact_B
        exact hno_muts ms_ld ((congrArg Ixon.Constant.info hcb_eq).trans hcb_ld)
      have hedge : Core.S0.WalkEdge E₀ a p.block :=
        ⟨c_a0, hrec_a0, .inl ⟨by simp [Ix.Cert.ownerOf, hinfo], hp_ne⟩⟩
      obtain ⟨hwk_blk, _⟩ := (wkAll_closedSubwalk calls bAddr t E₀).step a p.block hwk_a hedge
      obtain ⟨cb₀, hrec_cb₀, hchk_or⟩ := (wkAll_closedSubwalk calls bAddr t E₀).checked p.block hwk_blk
      have hcb_eq : cb₀ = cb_ld := loaded_recordAt_eq_of_exact_noCollision
        hexact₀ hload₀ hnoCol hrec_cb₀ hhash_B hsub_ci hblake_B hexact_B
      subst cb_ld
      have hms_arr : ms_ld[p.idx.toNat]? = some (.indc ind_ld) := by simpa using hms_ld
      have hct_arr : ind_ld.ctors[p.cidx.toNat]? = some ct_ld := by simpa using hct_ld
      have hm_i : Claim.MutsMemberCheckedAtFull calls bAddr t p.block ms_ld p.idx.toNat := by
        rcases hchk_or with ⟨ms', hms'_eq, hmem_chk⟩ | hchk_blk
        · rw [hcb_ld] at hms'_eq; injection hms'_eq with hms'_eq'; subst ms'
          exact hmem_chk _ (Array.getElem?_eq_some_iff.mp hms_arr).1
        · obtain ⟨_, _, _, _, _, _, _, _, _, cs_b, _, bytes_b, _,
            _, _, _, _, hhash_b, hblake_b, _, hL1_b, hsub_b, _, _, _, _⟩ :=
            checkedAtFull_loadedL1 hbound hchk_blk
          obtain ⟨c_b, hdec_b, _, _, _, _, hraw_b⟩ := hL1_b
          have hcb_eq_b := loaded_recordAt_eq_of_exact_noCollision
            hexact₀ hload₀ hnoCol hrec_cb₀ hhash_b hsub_b hblake_b hdec_b
          subst c_b; simp only [L1.RawCIRep, hcb_ld] at hraw_b
      obtain ⟨_, _, _, _, _, _, _, _, _, _, rfl, _⟩ := hraw_ct
      have hct_safe : ct_ld.isUnsafe = false := by
        cases Obs.«KernelCheck::is_unsafe_ci».obs ev_u with
        | Ctor _ _ _ _ _ _ _ _ _ _ _ _ _ _ hv he _ _ =>
          simp only [Value.construct.injEq, List.cons.injEq, and_true] at hv
          rcases hv with ⟨_, _, _, _, _, _, _, _, _, hu_eq⟩
          exact bool_false_of_repBoolField_zero (hu_eq.trans he)
        | Axiom _ _ _ hv | Defn_Safe _ _ _ _ _ hv | Defn_other _ _ _ _ _ _ hv
        | Thm _ _ _ _ _ hv | Opaque _ _ _ _ _ _ _ hv | Quot _ _ _ _ _ _ _ hv
        | Induct _ _ _ _ _ _ _ _ _ _ _ _ _ hv | Rec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hv =>
          simp [Core.kciEnum] at hv
      have hlt_ind : mutUnsafeCount (.indc ind_ld) < mutConstCount (.indc ind_ld) := by
        have hlt_ct := sum_ctorUnsafeBit_lt_length_of_mem (List.mem_of_getElem? hct_ld) hct_safe
        simp only [mutUnsafeCount, mutConstCount]
        cases ind_ld.isUnsafe <;> omega
      obtain ⟨x_blk, r_mk, h_mk, h'_mk, cs_mk, ha_blk, ev_mk, hsub_mk⟩ :=
        ind_block_checked_member_kinds hbound hload₀ hexact₀ hnoCol hrec_cb₀ hcb_ld hms_arr hm_i
      have hinl_cb : IxVM.Consistency.InLogic cb₀ :=
        check_block_member_kinds_inLogic hload₀ hexact₀ hnoCol ha_blk ev_mk hsub_mk
          hrec_cb₀ hcb_ld ⟨.indc ind_ld, List.mem_of_getElem? hms_ld, hlt_ind⟩
      have hsafe_blk : ¬ IxVM.Consistency.OutsideLogicAt E₀ p.block := by
        rintro ⟨c_x, hrec_x, hnot_c | ⟨cb_x, hrec_cbx, hnot_cbx⟩⟩
        · have hcx : c_x = cb₀ := Option.some.inj (hrec_x.symm.trans hrec_cb₀)
          rw [hcx] at hnot_c; exact hnot_c hinl_cb
        · have hcx : c_x = cb₀ := Option.some.inj (hrec_x.symm.trans hrec_cb₀)
          rw [hcx] at hrec_cbx; simp only [Ix.Cert.ownerOf, hcb_ld] at hrec_cbx
          have hcbx : cb_x = cb₀ := Option.some.inj (hrec_cbx.symm.trans hrec_cb₀)
          rw [hcbx] at hnot_cbx; exact hnot_cbx hinl_cb
      have hcidx_eq_nat : ct_ld.cidx.toNat = p.cidx.toNat :=
        indBlockCtorIdx_of_exact_noCollision hbound hload₀ hexact₀ hnoCol
          hwk_blk hsafe_blk hrec_cb₀ hcb_ld hms_arr hct_arr
      have hcidx_eq : ct_ld.cidx = p.cidx := UInt64.toNat_inj.mp hcidx_eq_nat
      have hnot_out : ¬ IxVM.Consistency.OutsideLogicAt E₀ a := by
        rintro ⟨c_x, hrec_x, hnot_c | ⟨cb_x, hrec_cbx, hnot_cbx⟩⟩
        · have hcx : c_x = c_a0 := Option.some.inj (hrec_x.symm.trans hrec_a0)
          rw [hcx] at hnot_c; exact hnot_c (by simp [IxVM.Consistency.InLogic, hinfo])
        · have hcx : c_x = c_a0 := Option.some.inj (hrec_x.symm.trans hrec_a0)
          rw [hcx] at hrec_cbx; simp only [Ix.Cert.ownerOf, hinfo] at hrec_cbx
          have hcbx : cb_x = cb₀ := Option.some.inj (hrec_cbx.symm.trans hrec_cb₀)
          rw [hcbx] at hnot_cbx; exact hnot_cbx hinl_cb
      exact ⟨hnot_out,
        by simp [Ix.Kernel.Reader.resolveSource, hinfo, hemp, hrec_cb₀,
          hcb_ld, hms_arr, hct_arr, hcidx_eq, guard, pure]⟩
  refine ⟨hres_and_safe.1, fun c_a hrec_a => ?_⟩
  have heq : c_a = c_a0 := Option.some.inj (hrec_a.symm.trans hrec_a0)
  rwa [heq]

/-- Along any `L1.RawConvExpr` evaluated by `KernelCheck::safe_refs_only`, every `.ref`-only
reachable constant index `i ∈ reachRefOnlyExpr ... e` with `c.refs[i]? = some a` satisfies
`SafeRefTargetChecked calls a` unconditionally when `r = .field 1`. -/
theorem safe_refs_only_raw_checked
    {calls : List (Call F)} {c : Ixon.Constant} {recurAddrs : List _root_.Address}
    {blobs : List (_root_.Address × ByteArray)} {h₀ : Heap F}
    {bound : Nat} {e : Ixon.Expr} {kp : SourceValue F}
    (hbound : IxVM.Consistency.Bounded calls)
    (raw : L1.RawConvExpr c.refs.toList recurAddrs c.univs.toList c.sharing.toList blobs h₀ bound e kp) :
    ∀ (n : Nat) {h h' : Heap F} {r : SourceValue F} {cs : List (Call F)},
      n ≤ c.sharing.toList.length →
      (bound ≤ n ∨ (bound = 4294967295 ∧ n = c.sharing.toList.length)) →
      Heap.Extends h₀ h →
      (∀ cl ∈ cs, cl ∈ calls) →
      ObsFn Core.W "KernelCheck::safe_refs_only" [kp] h r h' cs →
      (r = .field 0 ∨ r = .field 1) ∧
      Heap.Extends h h' ∧
      (r = .field 1 →
        ∀ {i : Nat} {a : _root_.Address},
          i ∈ reachRefOnlyExpr (buildReachRefOnlyTbl (c.sharing.toList.take n)) e →
          c.refs[i]? = some a →
          SafeRefTargetChecked calls a) := by
  induction raw with
  | var _ cell =>
    intro n h h' r cs _ _ hext _ ev
    have cell_h := hext.getElem?_eq cell
    cases Obs.«KernelCheck::safe_refs_only».obs ev with
    | BVar _ ld hr hh' _ =>
      exact ⟨Or.inr hr, by rw [hh'], fun _ _ _ hm => nomatch hm⟩
    | Srt _ ld _ _ _ | Const _ _ _ _ _ _ _ _ ld _ _ _ _ _
    | App _ _ _ _ _ _ _ ld _ _ _ _ | Lam _ _ _ _ _ _ _ _ ld _ _ _ _
    | Forall _ _ _ _ _ _ _ _ ld _ _ _ _ | Let _ _ _ _ _ _ _ _ _ _ _ _ ld _ _ _ _ _ _
    | Lit _ ld _ _ _ | Proj _ _ _ _ ld _ _ =>
      exact (Core.load_cell_ne cell_h ld (by decide)).elim
  | sort _ _ _ cell =>
    intro n h h' r cs _ _ hext _ ev
    have cell_h := hext.getElem?_eq cell
    cases Obs.«KernelCheck::safe_refs_only».obs ev with
    | Srt _ ld hr hh' _ =>
      exact ⟨Or.inr hr, by rw [hh'], fun _ _ _ hm => nomatch hm⟩
    | BVar _ ld _ _ _ | Const _ _ _ _ _ _ _ _ ld _ _ _ _ _
    | App _ _ _ _ _ _ _ ld _ _ _ _ | Lam _ _ _ _ _ _ _ _ ld _ _ _ _
    | Forall _ _ _ _ _ _ _ _ ld _ _ _ _ | Let _ _ _ _ _ _ _ _ _ _ _ _ ld _ _ _ _ _ _
    | Lit _ ld _ _ _ | Proj _ _ _ _ ld _ _ =>
      exact (Core.load_cell_ne cell_h ld (by decide)).elim
  | str _ _ _ _ _ _ _ cell | nat _ _ _ _ _ _ _ cell =>
    intro n h h' r cs _ _ hext _ ev
    have cell_h := hext.getElem?_eq cell
    cases Obs.«KernelCheck::safe_refs_only».obs ev with
    | Lit _ ld hr hh' _ =>
      exact ⟨Or.inr hr, by rw [hh'], fun _ _ _ hm => nomatch hm⟩
    | BVar _ ld _ _ _ | Srt _ ld _ _ _ | Const _ _ _ _ _ _ _ _ ld _ _ _ _ _
    | App _ _ _ _ _ _ _ ld _ _ _ _ | Lam _ _ _ _ _ _ _ _ ld _ _ _ _
    | Forall _ _ _ _ _ _ _ _ ld _ _ _ _ | Let _ _ _ _ _ _ _ _ _ _ _ _ ld _ _ _ _ _ _
    | Proj _ _ _ _ ld _ _ =>
      exact (Core.load_cell_ne cell_h ld (by decide)).elim
  | recur _ _ _ ra _ _ cell =>
    intro n h h' r cs _ _ hext hsub ev
    have cell_h := hext.getElem?_eq cell
    cases Obs.«KernelCheck::safe_refs_only».obs ev with
    | Const x_caddr _ v63 m64 p71 cs77 y89 _ ld ev79 ld73 ev101 op95 hc110 =>
      have hxs := (Core.load_cell cell_h ld).2
      simp only [List.cons.injEq, and_true] at hxs
      rcases hxs with ⟨rfl, _⟩
      have hsub77 : ∀ cl ∈ cs77, cl ∈ calls := fun cl hcl => hsub cl (by rw [hc110]; simp [hcl])
      obtain ⟨ext_ci, _, _, _, _, _, _, _, _, _, v_ld, hld_v, hraw_ld⟩ :=
        L1.get_ci_loadedL1_spec (RomBound.bounded_mono hbound hsub77)
          (Aiur.Library.Bytes.repAddressRef_heapMono₂ Core.addrTy hext ra) ev79
      have hv_eq : v_ld = v63 := Except.ok.inj (hld_v.symm.trans ld73)
      subst hv_eq
      obtain ⟨hh', _, hy89, _, _⟩ := L1.is_unsafe_ci_raw_spec hraw_ld ev101
      subst hh'
      obtain ⟨hr_bool, _⟩ := sub_one_bool_dichot hy89 op95
      exact ⟨hr_bool, ext_ci, fun _ _ _ hm => nomatch hm⟩
    | BVar _ ld _ _ _ | Srt _ ld _ _ _
    | App _ _ _ _ _ _ _ ld _ _ _ _ | Lam _ _ _ _ _ _ _ _ ld _ _ _ _
    | Forall _ _ _ _ _ _ _ _ ld _ _ _ _ | Let _ _ _ _ _ _ _ _ _ _ _ _ ld _ _ _ _ _ _
    | Lit _ ld _ _ _ | Proj _ _ _ _ ld _ _ =>
      exact (Core.load_cell_ne cell_h ld (by decide)).elim
  | @ref bound addr rIdx uIdxs a' d ap lsp ls _ href hd ra _ _ cell =>
    intro n h h' r cs _ _ hext hsub ev
    have cell_h := hext.getElem?_eq cell
    cases Obs.«KernelCheck::safe_refs_only».obs ev with
    | Const x_caddr _ v63 m64 p71 cs77 y89 cs99 ld ev79 ld73 ev101 op95 hc110 =>
      have hxs := (Core.load_cell cell_h ld).2
      simp only [List.cons.injEq, and_true] at hxs
      rcases hxs with ⟨rfl, _⟩
      have hsub77 : ∀ cl ∈ cs77, cl ∈ calls := fun cl hcl => hsub cl (by rw [hc110]; simp [hcl])
      obtain ⟨ext_ci, _, _, _, _, _, _, _, _, _, v_ld, hld_v, hraw_ld⟩ :=
        L1.get_ci_loadedL1_spec (RomBound.bounded_mono hbound hsub77)
          (Aiur.Library.Bytes.repAddressRef_heapMono₂ Core.addrTy hext ra) ev79
      have hv_eq : v_ld = v63 := Except.ok.inj (hld_v.symm.trans ld73)
      subst hv_eq
      obtain ⟨hh', _, hy89, _, _⟩ := L1.is_unsafe_ci_raw_spec hraw_ld ev101
      subst hh'
      obtain ⟨hr_bool, hy0_of_r1⟩ := sub_one_bool_dichot hy89 op95
      refine ⟨hr_bool, ext_ci, fun hr1 {i a} hi hc_ref => ?_⟩
      have hy0 : y89 = .field 0 := hy0_of_r1 hr1
      subst hy0
      simp only [reachRefOnlyExpr, List.mem_singleton] at hi
      subst hi
      have href_arr : c.refs[rIdx.toNat]? = some a' := by simpa using href
      have ha_eq : a' = a := Option.some.inj (href_arr.symm.trans hc_ref)
      exact ⟨d, ap, p71, v63, h, m64, m64, cs77, cs99,
        hd.trans ha_eq, Aiur.Library.Bytes.repAddressRef_heapMono₂ Core.addrTy hext ra,
        ev79, hsub77, ld73, ev101⟩
    | BVar _ ld _ _ _ | Srt _ ld _ _ _
    | App _ _ _ _ _ _ _ ld _ _ _ _ | Lam _ _ _ _ _ _ _ _ ld _ _ _ _
    | Forall _ _ _ _ _ _ _ _ ld _ _ _ _ | Let _ _ _ _ _ _ _ _ _ _ _ _ ld _ _ _ _ _ _
    | Lit _ ld _ _ _ | Proj _ _ _ _ ld _ _ =>
      exact (Core.load_cell_ne cell_h ld (by decide)).elim
  | prj _ _ _ _ _ _ cell ih =>
    intro n h h' r cs hn hbnd hext hsub ev
    have cell_h := hext.getElem?_eq cell
    cases Obs.«KernelCheck::safe_refs_only».obs ev with
    | Proj _ _ x_e1 cs409 ld ev411 hc420 =>
      have hxs := (Core.load_cell cell_h ld).2
      simp only [List.cons.injEq, and_true] at hxs
      rcases hxs with ⟨_, _, rfl⟩
      have hsub409 : ∀ cl ∈ cs409, cl ∈ calls := fun cl hcl => hsub cl (by rw [hc420]; simp [hcl])
      exact ih n hn hbnd hext hsub409 ev411
    | BVar _ ld _ _ _ | Srt _ ld _ _ _ | Const _ _ _ _ _ _ _ _ ld _ _ _ _ _
    | App _ _ _ _ _ _ _ ld _ _ _ _ | Lam _ _ _ _ _ _ _ _ ld _ _ _ _
    | Forall _ _ _ _ _ _ _ _ ld _ _ _ _ | Let _ _ _ _ _ _ _ _ _ _ _ _ ld _ _ _ _ _ _
    | Lit _ ld _ _ _ =>
      exact (Core.load_cell_ne cell_h ld (by decide)).elim
  | app _ _ _ _ cell ih1 ih2 =>
    intro n h h' r cs hn hbnd hext hsub ev
    have cell_h := hext.getElem?_eq cell
    cases Obs.«KernelCheck::safe_refs_only».obs ev with
    | App x_e1 x_e2 v137 m138 cs148 y156 cs167 ld ev150 ev169 op162 hc182 =>
      have hxs := (Core.load_cell cell_h ld).2
      simp only [List.cons.injEq, and_true] at hxs
      rcases hxs with ⟨rfl, rfl⟩
      have hsub148 : ∀ cl ∈ cs148, cl ∈ calls := fun cl hcl => hsub cl (by rw [hc182]; simp [hcl])
      have hsub167 : ∀ cl ∈ cs167, cl ∈ calls := fun cl hcl => hsub cl (by rw [hc182]; simp [hcl])
      obtain ⟨hb1, ext1, hres1⟩ := ih1 n hn hbnd hext hsub148 ev150
      obtain ⟨hb2, ext2, hres2⟩ := ih2 n hn hbnd (hext.trans ext1) hsub167 ev169
      obtain ⟨hr_bool, hand⟩ := mul_bool_dichot hb1 hb2 op162
      refine ⟨hr_bool, ext1.trans ext2, fun hr1 {i a} hi hc_ref => ?_⟩
      obtain ⟨hv1, hv2⟩ := hand hr1
      simp only [reachRefOnlyExpr, List.mem_append] at hi
      rcases hi with hi1 | hi2
      · exact hres1 hv1 hi1 hc_ref
      · exact hres2 hv2 hi2 hc_ref
    | BVar _ ld _ _ _ | Srt _ ld _ _ _ | Const _ _ _ _ _ _ _ _ ld _ _ _ _ _
    | Lam _ _ _ _ _ _ _ _ ld _ _ _ _ | Forall _ _ _ _ _ _ _ _ ld _ _ _ _
    | Let _ _ _ _ _ _ _ _ _ _ _ _ ld _ _ _ _ _ _ | Lit _ ld _ _ _ | Proj _ _ _ _ ld _ _ =>
      exact (Core.load_cell_ne cell_h ld (by decide)).elim
  | lam _ _ _ _ _ cell ih1 ih2 =>
    intro n h h' r cs hn hbnd hext hsub ev
    have cell_h := hext.getElem?_eq cell
    cases Obs.«KernelCheck::safe_refs_only».obs ev with
    | Lam _ x_e1 x_e2 v204 m205 cs215 y223 cs234 ld ev217 ev236 op229 hc250 =>
      have hxs := (Core.load_cell cell_h ld).2
      simp only [List.cons.injEq, and_true] at hxs
      rcases hxs with ⟨_, rfl, rfl⟩
      have hsub215 : ∀ cl ∈ cs215, cl ∈ calls := fun cl hcl => hsub cl (by rw [hc250]; simp [hcl])
      have hsub234 : ∀ cl ∈ cs234, cl ∈ calls := fun cl hcl => hsub cl (by rw [hc250]; simp [hcl])
      obtain ⟨hb1, ext1, hres1⟩ := ih1 n hn hbnd hext hsub215 ev217
      obtain ⟨hb2, ext2, hres2⟩ := ih2 n hn hbnd (hext.trans ext1) hsub234 ev236
      obtain ⟨hr_bool, hand⟩ := mul_bool_dichot hb1 hb2 op229
      refine ⟨hr_bool, ext1.trans ext2, fun hr1 {i a} hi hc_ref => ?_⟩
      obtain ⟨hv1, hv2⟩ := hand hr1
      simp only [reachRefOnlyExpr, List.mem_append] at hi
      rcases hi with hi1 | hi2
      · exact hres1 hv1 hi1 hc_ref
      · exact hres2 hv2 hi2 hc_ref
    | BVar _ ld _ _ _ | Srt _ ld _ _ _ | Const _ _ _ _ _ _ _ _ ld _ _ _ _ _
    | App _ _ _ _ _ _ _ ld _ _ _ _ | Forall _ _ _ _ _ _ _ _ ld _ _ _ _
    | Let _ _ _ _ _ _ _ _ _ _ _ _ ld _ _ _ _ _ _ | Lit _ ld _ _ _ | Proj _ _ _ _ ld _ _ =>
      exact (Core.load_cell_ne cell_h ld (by decide)).elim
  | all _ _ _ _ _ cell ih1 ih2 =>
    intro n h h' r cs hn hbnd hext hsub ev
    have cell_h := hext.getElem?_eq cell
    cases Obs.«KernelCheck::safe_refs_only».obs ev with
    | Forall _ x_e1 x_e2 v272 m273 cs283 y291 cs302 ld ev285 ev304 op297 hc318 =>
      have hxs := (Core.load_cell cell_h ld).2
      simp only [List.cons.injEq, and_true] at hxs
      rcases hxs with ⟨_, rfl, rfl⟩
      have hsub283 : ∀ cl ∈ cs283, cl ∈ calls := fun cl hcl => hsub cl (by rw [hc318]; simp [hcl])
      have hsub302 : ∀ cl ∈ cs302, cl ∈ calls := fun cl hcl => hsub cl (by rw [hc318]; simp [hcl])
      obtain ⟨hb1, ext1, hres1⟩ := ih1 n hn hbnd hext hsub283 ev285
      obtain ⟨hb2, ext2, hres2⟩ := ih2 n hn hbnd (hext.trans ext1) hsub302 ev304
      obtain ⟨hr_bool, hand⟩ := mul_bool_dichot hb1 hb2 op297
      refine ⟨hr_bool, ext1.trans ext2, fun hr1 {i a} hi hc_ref => ?_⟩
      obtain ⟨hv1, hv2⟩ := hand hr1
      simp only [reachRefOnlyExpr, List.mem_append] at hi
      rcases hi with hi1 | hi2
      · exact hres1 hv1 hi1 hc_ref
      · exact hres2 hv2 hi2 hc_ref
    | BVar _ ld _ _ _ | Srt _ ld _ _ _ | Const _ _ _ _ _ _ _ _ ld _ _ _ _ _
    | App _ _ _ _ _ _ _ ld _ _ _ _ | Lam _ _ _ _ _ _ _ _ ld _ _ _ _
    | Let _ _ _ _ _ _ _ _ _ _ _ _ ld _ _ _ _ _ _ | Lit _ ld _ _ _ | Proj _ _ _ _ ld _ _ =>
      exact (Core.load_cell_ne cell_h ld (by decide)).elim
  | letE _ _ _ _ _ _ _ cell ih1 ih2 ih3 =>
    intro n h h' r cs hn hbnd hext hsub ev
    have cell_h := hext.getElem?_eq cell
    cases Obs.«KernelCheck::safe_refs_only».obs ev with
    | Let x_e1 x_e2 x_e3 m343 cs353 x363 v364 m365 y371 cs382 y390 cs401
        ld ev355 ev384 op377 ev403 op396 hc418 =>
      have hxs := (Core.load_cell cell_h ld).2
      simp only [List.cons.injEq, and_true] at hxs
      rcases hxs with ⟨rfl, rfl, rfl⟩
      have hsub353 : ∀ cl ∈ cs353, cl ∈ calls := fun cl hcl => hsub cl (by rw [hc418]; simp [hcl])
      have hsub382 : ∀ cl ∈ cs382, cl ∈ calls := fun cl hcl => hsub cl (by rw [hc418]; simp [hcl])
      have hsub401 : ∀ cl ∈ cs401, cl ∈ calls := fun cl hcl => hsub cl (by rw [hc418]; simp [hcl])
      obtain ⟨hb1, ext1, hres1⟩ := ih1 n hn hbnd hext hsub353 ev355
      obtain ⟨hb2, ext2, hres2⟩ := ih2 n hn hbnd (hext.trans ext1) hsub382 ev384
      obtain ⟨hb12, hand12⟩ := mul_bool_dichot hb1 hb2 op377
      obtain ⟨hb3, ext3, hres3⟩ := ih3 n hn hbnd ((hext.trans ext1).trans ext2) hsub401 ev403
      obtain ⟨hr_bool, hand⟩ := mul_bool_dichot hb12 hb3 op396
      refine ⟨hr_bool, (ext1.trans ext2).trans ext3, fun hr1 {i a} hi hc_ref => ?_⟩
      obtain ⟨hv12, hv3⟩ := hand hr1
      obtain ⟨hv1, hv2⟩ := hand12 hv12
      simp only [reachRefOnlyExpr, List.mem_append] at hi
      rcases hi with (hi1 | hi2) | hi3
      · exact hres1 hv1 hi1 hc_ref
      · exact hres2 hv2 hi2 hc_ref
      · exact hres3 hv3 hi3 hc_ref
    | BVar _ ld _ _ _ | Srt _ ld _ _ _ | Const _ _ _ _ _ _ _ _ ld _ _ _ _ _
    | App _ _ _ _ _ _ _ ld _ _ _ _ | Lam _ _ _ _ _ _ _ _ ld _ _ _ _
    | Forall _ _ _ _ _ _ _ _ ld _ _ _ _ | Lit _ ld _ _ _ | Proj _ _ _ _ ld _ _ =>
      exact (Core.load_cell_ne cell_h ld (by decide)).elim
  | @share bound idx s kp hidx hsh _ ihs =>
    intro n h h' r cs _ hbnd hext hsub ev
    have hidx_len : idx.toNat < c.sharing.toList.length :=
      (List.getElem?_eq_some_iff.mp hsh).1
    have hidx_n : idx.toNat < n := by
      rcases hbnd with hle | ⟨_, hn_eq⟩ <;> omega
    have hget := buildReachRefOnlyTbl_take_getElem? c.sharing.toList hidx_n hsh
    obtain ⟨hb, ext, hres⟩ :=
      ihs idx.toNat (Nat.le_of_lt hidx_len) (.inl (Nat.le_refl _)) hext hsub ev
    refine ⟨hb, ext, fun hr1 {i a} hi hc_ref => ?_⟩
    simp only [reachRefOnlyExpr, hget, Option.getD_some] at hi
    exact hres hr1 hi hc_ref

/-- Unconditional `.ref`-only target safety: every `i ∈ reachRefOnlyExpr ... e` on an expression
accepted by `KernelCheck::safe_refs_only` satisfies `SafeRefTargetChecked calls a`. -/
theorem safe_refs_only_refOnly_checked
    {calls : List (Call F)} {c : Ixon.Constant} {recurAddrs : List _root_.Address}
    {blobs : List (_root_.Address × ByteArray)} {h h' : Heap F} {cs : List (Call F)}
    {bound : Nat} {e : Ixon.Expr} {kp : SourceValue F}
    (hbound : IxVM.Consistency.Bounded calls)
    (hbnd : bound ≤ c.sharing.toList.length ∨ bound = 4294967295)
    (ev : ObsFn Core.W "KernelCheck::safe_refs_only" [kp] h (.field 1) h' cs)
    (hsub : ∀ cl ∈ cs, cl ∈ calls)
    (raw : L1.RawConvExpr c.refs.toList recurAddrs c.univs.toList c.sharing.toList blobs h bound e kp) :
    ∀ {i : Nat} {a : _root_.Address},
      i ∈ reachRefOnlyExpr (buildReachRefOnlyTbl c.sharing.toList) e →
      c.refs[i]? = some a →
      SafeRefTargetChecked calls a := by
  have hbnd' : bound ≤ c.sharing.toList.length ∨
      (bound = 4294967295 ∧ c.sharing.toList.length = c.sharing.toList.length) := by
    rcases hbnd with hle | heq
    · exact .inl hle
    · exact .inr ⟨heq, rfl⟩
  intro i a hi hc_ref
  rw [← List.take_length (l := c.sharing.toList)] at hi
  exact (safe_refs_only_raw_checked hbound raw
    c.sharing.toList.length (Nat.le_refl _) hbnd' (Heap.Extends.refl h) hsub ev).2.2
    rfl hi hc_ref

/-- Exact circuit expression-safety premise corresponding to `KExprNode::Proj(taddr, _, e1)`
checking `taddr` in `KernelCheck::safe_refs_only` (`.ref` nodes already satisfy
`SafeRefTargetChecked` unconditionally by `safe_refs_only_refOnly_checked`), together with
recursor `rules` / modeled `check_recs` safety. -/
structure CircuitExprSafeRefs : Prop where
  expr_refs_checked :
    ∀ {calls : List (Call F)} {c : Ixon.Constant} {recurAddrs : List _root_.Address}
      {blobs : List (_root_.Address × ByteArray)} {h h' : Heap F} {cs : List (Call F)}
      {bound : Nat} {e : Ixon.Expr} {kp : SourceValue F},
      IxVM.Consistency.Bounded calls →
      (bound ≤ c.sharing.toList.length ∨ bound = 4294967295) →
      ObsFn Core.W "KernelCheck::safe_refs_only" [kp] h (.field 1) h' cs →
      (∀ cl ∈ cs, cl ∈ calls) →
      L1.RawConvExpr c.refs.toList recurAddrs c.univs.toList c.sharing.toList blobs h bound e kp →
      ∀ {i : Nat} {a : _root_.Address},
        i ∈ reachRefsExpr (buildReachRefsTbl c.sharing.toList) e →
        c.refs[i]? = some a →
        SafeRefTargetChecked calls a

/-- Full `SafeRefsInputs.safe_expr_refs_resolve` derived from `CircuitExprSafeRefs` and our
unconditional `safeRefTargetChecked_resolve_and_not_outside` theorem. -/
theorem safe_expr_refs_resolve_of_circuitExprSafeRefs
    (hCircuit : CircuitExprSafeRefs) :
    ∀ {calls : List (Call F)} {bAddr : _root_.Address} {t : Ix.Kernel.RoleTable}
      {E₀ : Ixon.Env} {V : IxVM.Refinement.View} {extra : List ByteArray}
      {c : Ixon.Constant} {recurAddrs : List _root_.Address}
      {blobs : List (_root_.Address × ByteArray)} {h h' : Heap F} {cs : List (Call F)}
      {bound : Nat} {e : Ixon.Expr} {kp : SourceValue F},
      IxVM.Consistency.Bounded calls →
      IxVM.Consistency.LoadedBy calls E₀ →
      L1.EnvDecoded E₀ →
      ¬ V.HashedCollision extra calls →
      (bound ≤ c.sharing.toList.length ∨ bound = 4294967295) →
      ObsFn Core.W "KernelCheck::safe_refs_only" [kp] h (.field 1) h' cs →
      (∀ cl ∈ cs, cl ∈ calls) →
      L1.RawConvExpr c.refs.toList recurAddrs c.univs.toList c.sharing.toList blobs h bound e kp →
      ∀ {i : Nat} {a : _root_.Address},
        i ∈ reachRefsExpr (buildReachRefsTbl c.sharing.toList) e →
        c.refs[i]? = some a →
        WkAll calls bAddr t E₀ a →
        ¬ IxVM.Consistency.OutsideLogicAt E₀ a ∧
          ∀ c_a, Ix.Cert.recordAt E₀ a = some c_a →
            (Ix.Kernel.Reader.resolveSource (Ix.Cert.recordAt E₀) a c_a).isSome = true := by
  intro calls bAddr t E₀ V extra c recurAddrs blobs h h' cs bound e kp
    hbound hload₀ hexact₀ hnoCol hbnd ev hsub raw i a hi hc_ref hwk_a
  exact safeRefTargetChecked_resolve_and_not_outside hbound hload₀ hexact₀ hnoCol
    (hCircuit.expr_refs_checked hbound hbnd ev hsub raw hi hc_ref) hwk_a

/-! ## Section 3: Role-Prefix Order, Reachability & `preparePrelude` Splitting -/

private theorem idxOf_append_left [BEq α] [LawfulBEq α] :
    ∀ {xs ys : List α} {a : α}, a ∈ xs → (xs ++ ys).idxOf a = xs.idxOf a
  | [], _, _, ha => nomatch ha
  | x :: xs, ys, a, ha => by
    simp only [List.cons_append, List.idxOf_cons]
    cases hxa : x == a with
    | true => rfl
    | false =>
      rcases List.mem_cons.mp ha with h_ax | ha'
      · rw [h_ax] at hxa
        exact absurd (beq_self_eq_true x) (by rw [hxa]; decide)
      · exact congrArg Nat.succ (idxOf_append_left ha')

private theorem idxOf_lt_length [BEq α] [LawfulBEq α] :
    ∀ {xs : List α} {a : α}, a ∈ xs → xs.idxOf a < xs.length
  | [], _, ha => nomatch ha
  | x :: xs, a, ha => by
    simp only [List.idxOf_cons, List.length_cons]
    cases hxa : x == a with
    | true => exact Nat.zero_lt_succ _
    | false =>
      rcases List.mem_cons.mp ha with h_ax | ha'
      · rw [h_ax] at hxa
        exact absurd (beq_self_eq_true x) (by rw [hxa]; decide)
      · exact Nat.succ_lt_succ (idxOf_lt_length ha')

private theorem getElem?_idxOf [BEq α] [LawfulBEq α] :
    ∀ {xs : List α} {a : α}, a ∈ xs → xs[xs.idxOf a]? = some a
  | [], _, ha => nomatch ha
  | x :: xs, a, ha => by
    simp only [List.idxOf_cons]
    cases hxa : x == a with
    | true => exact congrArg some (beq_iff_eq.mp hxa)
    | false =>
      rcases List.mem_cons.mp ha with h_ax | ha'
      · rw [h_ax] at hxa
        exact absurd (beq_self_eq_true x) (by rw [hxa]; decide)
      · exact getElem?_idxOf ha'

private theorem getElem_idxOf [BEq α] [LawfulBEq α] {xs : List α} {a : α}
    (ha : a ∈ xs) : xs[xs.idxOf a]'(idxOf_lt_length ha) = a := by
  have h := getElem?_idxOf ha
  rw [List.getElem?_eq_getElem (idxOf_lt_length ha)] at h
  exact Option.some.inj h

private theorem idxOf_getElem_of_nodup [BEq α] [LawfulBEq α] :
    ∀ {xs : List α}, xs.Nodup → ∀ (i : Nat) (hi : i < xs.length), xs.idxOf xs[i] = i
  | [], _, _, hi => nomatch hi
  | _ :: _, _, 0, _ => by simp
  | x :: xs, hnd, i + 1, hi => by
    rw [List.nodup_cons] at hnd
    have hi' : i < xs.length := Nat.lt_of_succ_lt_succ hi
    simp only [List.getElem_cons_succ, List.idxOf_cons]
    have hne : (x == xs[i]'hi') = false :=
      beq_false_of_ne (fun h => hnd.1 (by rw [h]; exact List.getElem_mem hi'))
    rw [hne]
    exact congrArg Nat.succ (idxOf_getElem_of_nodup hnd.2 i hi')

/-- **Unconditional role-prefix filter identity**: whenever `order` and `order_role` are `Nodup`,
every element of `order_role` appears in `order`, `order` splits into
`order.filter (· ∈ order_role) ++ order.filter (· ∉ order_role)`, and relative indices on
`order.filter (· ∈ order_role)` are preserved in `order_role`, we have
`order.filter (· ∈ order_role) = order_role`. -/
theorem order_filter_role_eq_of_subset
    {order order_role : List _root_.Address}
    (hnd : order.Nodup)
    (hnd_r : order_role.Nodup)
    (hsub : ∀ a ∈ order_role, a ∈ order)
    (hsplit : order = order.filter (· ∈ order_role) ++ order.filter (· ∉ order_role))
    (hmono : ∀ a b', a ∈ order.filter (· ∈ order_role) → b' ∈ order.filter (· ∈ order_role) →
      order.idxOf a < order.idxOf b' → order_role.idxOf a < order_role.idxOf b') :
    order.filter (· ∈ order_role) = order_role := by
  let xs := order.filter (· ∈ order_role)
  have hsplit_xs : order = xs ++ order.filter (· ∉ order_role) := hsplit
  have hnd_xs : xs.Nodup := hnd.filter _
  have hmem : ∀ a, a ∈ xs ↔ a ∈ order_role := fun a =>
    ⟨fun h => of_decide_eq_true (List.mem_filter.mp h).2,
     fun h => List.mem_filter.mpr ⟨hsub a h, decide_eq_true h⟩⟩
  let f : Nat → Nat := fun i => match xs[i]? with | some x => order_role.idxOf x | none => 0
  have hf_eq : ∀ i (hi : i < xs.length), f i = order_role.idxOf (xs[i]'hi) := by
    intro i hi
    simp only [f, List.getElem?_eq_getElem hi]
  have hf_lt : ∀ i (hi : i < xs.length), f i < order_role.length := by
    intro i hi
    rw [hf_eq i hi]
    exact idxOf_lt_length ((hmem xs[i]).mp (List.getElem_mem hi))
  have hf_mono : ∀ i₁ i₂, i₁ < i₂ → (hi₂ : i₂ < xs.length) → f i₁ < f i₂ := by
    intro i₁ i₂ hlt hi₂
    have hi₁ : i₁ < xs.length := Nat.lt_trans hlt hi₂
    rw [hf_eq i₁ hi₁, hf_eq i₂ hi₂]
    have hm₁ : xs[i₁] ∈ xs := List.getElem_mem hi₁
    have hm₂ : xs[i₂] ∈ xs := List.getElem_mem hi₂
    have hidx₁ : order.idxOf xs[i₁] = i₁ := by
      rw [hsplit_xs, idxOf_append_left hm₁, idxOf_getElem_of_nodup hnd_xs i₁ hi₁]
    have hidx₂ : order.idxOf xs[i₂] = i₂ := by
      rw [hsplit_xs, idxOf_append_left hm₂, idxOf_getElem_of_nodup hnd_xs i₂ hi₂]
    apply hmono xs[i₁] xs[i₂] hm₁ hm₂
    rw [hidx₁, hidx₂]
    exact hlt
  have hsurj : ∀ j (hj : j < order_role.length), ∃ i, i < xs.length ∧ f i = j := by
    intro j hj
    have hy_mem : order_role[j] ∈ xs := (hmem order_role[j]).mpr (List.getElem_mem hj)
    have hi : xs.idxOf order_role[j] < xs.length := idxOf_lt_length hy_mem
    have hget : xs[xs.idxOf order_role[j]]'hi = order_role[j] := getElem_idxOf hy_mem
    refine ⟨xs.idxOf order_role[j], hi, ?_⟩
    rw [hf_eq _ hi, hget]
    exact idxOf_getElem_of_nodup hnd_r j hj
  have hstep : ∀ j, j < order_role.length → j < xs.length ∧ f j = j := by
    intro j
    induction j with
    | zero =>
      intro hj
      obtain ⟨i, hi, hfi⟩ := hsurj 0 hj
      by_cases hi0 : i = 0
      · subst hi0; exact ⟨hi, hfi⟩
      · have h0i : 0 < i := Nat.pos_of_ne_zero hi0
        have := hf_mono 0 i h0i hi
        omega
    | succ j ih =>
      intro hj
      obtain ⟨hj_xs, hfj⟩ := ih (Nat.lt_of_succ_lt hj)
      obtain ⟨i, hi, hfi⟩ := hsurj (j + 1) hj
      by_cases hij : i < j
      · have := hf_mono i j hij hj_xs
        omega
      · by_cases heq_j : i = j
        · subst heq_j; omega
        · by_cases hgt : j + 1 < i
          · have h1 := hf_mono j (j + 1) (Nat.lt_succ_self j) (Nat.lt_trans hgt hi)
            have h2 := hf_mono (j + 1) i hgt hi
            omega
          · have hi_eq : i = j + 1 := by omega
            subst hi_eq
            exact ⟨hi, hfi⟩
  have hlen_eq : xs.length = order_role.length := by
    by_cases hlt : order_role.length < xs.length
    · cases hlen_r : order_role.length with
      | zero =>
        rw [hlen_r] at hlt
        have := hf_lt 0 hlt
        omega
      | succ m =>
        have hm_r : m < order_role.length := by omega
        obtain ⟨_, hfm⟩ := hstep m hm_r
        have hm1_xs : m + 1 < xs.length := by omega
        have h1 := hf_mono m (m + 1) (Nat.lt_succ_self m) hm1_xs
        have h2 := hf_lt (m + 1) hm1_xs
        omega
    · by_cases hgt : xs.length < order_role.length
      · have := (hstep xs.length hgt).1
        omega
      · omega
  apply List.ext_getElem hlen_eq
  intro j hj₁ hj₂
  obtain ⟨_, hfj⟩ := hstep j hj₂
  rw [hf_eq j hj₁] at hfj
  have hmem_j : xs[j] ∈ order_role := (hmem xs[j]).mp (List.getElem_mem hj₁)
  have hlt_idx : order_role.idxOf xs[j] < order_role.length := idxOf_lt_length hmem_j
  have hget : order_role[order_role.idxOf xs[j]]'hlt_idx = xs[j] := getElem_idxOf hmem_j
  have heq_elem : order_role[order_role.idxOf xs[j]]'hlt_idx = order_role[j]'hj₂ := by
    congr 1
  exact (heq_elem.symm.trans hget).symm

private theorem idxOf_filter_lt_of_idxOf_lt [BEq α] [LawfulBEq α] :
    ∀ {xs : List α} {p : α → Bool} {a b : α},
      xs.Nodup → a ∈ xs.filter p → b ∈ xs.filter p →
      xs.idxOf a < xs.idxOf b →
      (xs.filter p).idxOf a < (xs.filter p).idxOf b
  | [], _, _, _, _, ha, _, _ => nomatch ha
  | x :: xs, p, a, b, hnd, ha, hb, hlt => by
    rw [List.nodup_cons] at hnd
    simp only [List.filter_cons] at ha hb ⊢
    cases hpx : p x with
    | true =>
      simp only [hpx, ↓reduceIte, List.idxOf_cons] at ha hb ⊢
      simp only [List.idxOf_cons] at hlt
      cases hxa : x == a with
      | true =>
        simp only [hxa, ↓reduceIte] at hlt ⊢
        cases hxb : x == b with
        | true => simp only [hxb, ↓reduceIte] at hlt; omega
        | false => simp only [Bool.false_eq_true, ↓reduceIte]; exact Nat.zero_lt_succ _
      | false =>
        simp only [hxa, Bool.false_eq_true, ↓reduceIte] at hlt ⊢
        have ha' : a ∈ xs.filter p := by
          rcases List.mem_cons.mp ha with h_ax | ha'
          · rw [h_ax] at hxa; exact absurd (beq_self_eq_true x) (by rw [hxa]; decide)
          · exact ha'
        cases hxb : x == b with
        | true => simp only [hxb, ↓reduceIte] at hlt; omega
        | false =>
          simp only [hxb, Bool.false_eq_true, ↓reduceIte] at hlt ⊢
          have hb' : b ∈ xs.filter p := by
            rcases List.mem_cons.mp hb with h_bx | hb'
            · rw [h_bx] at hxb; exact absurd (beq_self_eq_true x) (by rw [hxb]; decide)
            · exact hb'
          exact Nat.succ_lt_succ (idxOf_filter_lt_of_idxOf_lt hnd.2 ha' hb' (Nat.lt_of_succ_lt_succ hlt))
    | false =>
      simp only [hpx, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      have hxa : (x == a) = false :=
        beq_false_of_ne (fun h => hnd.1 (by rw [h]; exact (List.mem_filter.mp ha).1))
      have hxb : (x == b) = false :=
        beq_false_of_ne (fun h => hnd.1 (by rw [h]; exact (List.mem_filter.mp hb).1))
      simp only [List.idxOf_cons, hxa, hxb, Bool.false_eq_true, ↓reduceIte] at hlt
      exact idxOf_filter_lt_of_idxOf_lt hnd.2 ha hb (Nat.lt_of_succ_lt_succ hlt)

/-- **Unconditional pruned role-prefix identity**: even without `order_role ⊆ order` (e.g. when
`order` is `UsedClosureOrderAt` for `ReadIn`'s `seeds ∨ evidence` rather than `seeds ∨ BindingSeeds`),
the role slice `order.filter (· ∈ order_role)` equals the downward-closed pruned role prefix
`order_role.filter (· ∈ order)`. -/
theorem order_filter_eq_pruned_role_prefix
    {order order_role : List _root_.Address}
    (hnd : order.Nodup)
    (hnd_r : order_role.Nodup)
    (hsplit : order = order.filter (· ∈ order_role) ++ order.filter (· ∉ order_role))
    (hmono : ∀ a b, a ∈ order.filter (· ∈ order_role) → b ∈ order.filter (· ∈ order_role) →
      order.idxOf a < order.idxOf b → order_role.idxOf a < order_role.idxOf b) :
    order.filter (· ∈ order_role) = order_role.filter (· ∈ order) := by
  let order_role' := order_role.filter (· ∈ order)
  have hfilt_eq : order.filter (· ∈ order_role) = order.filter (· ∈ order_role') := by
    apply List.filter_congr
    intro x hx
    by_cases hxr : x ∈ order_role
    · have hxr' : x ∈ order_role' := List.mem_filter.mpr ⟨hxr, decide_eq_true hx⟩
      simp [hxr, hxr']
    · have hxr' : x ∉ order_role' := fun h => hxr (List.mem_filter.mp h).1
      simp [hxr, hxr']
  have hnot_eq : order.filter (· ∉ order_role) = order.filter (· ∉ order_role') := by
    apply List.filter_congr
    intro x hx
    by_cases hxr : x ∈ order_role
    · have hxr' : x ∈ order_role' := List.mem_filter.mpr ⟨hxr, decide_eq_true hx⟩
      simp [hxr, hxr']
    · have hxr' : x ∉ order_role' := fun h => hxr (List.mem_filter.mp h).1
      simp [hxr, hxr']
  rw [hfilt_eq]
  apply order_filter_role_eq_of_subset hnd (hnd_r.filter _)
  · intro a ha
    exact of_decide_eq_true (List.mem_filter.mp ha).2
  · rw [← hfilt_eq, ← hnot_eq]
    exact hsplit
  · intro a b ha hb hlt
    rw [← hfilt_eq] at ha hb
    have ha_r' : a ∈ order_role' := List.mem_filter.mpr
      ⟨of_decide_eq_true (List.mem_filter.mp ha).2, decide_eq_true (List.mem_filter.mp ha).1⟩
    have hb_r' : b ∈ order_role' := List.mem_filter.mpr
      ⟨of_decide_eq_true (List.mem_filter.mp hb).2, decide_eq_true (List.mem_filter.mp hb).1⟩
    exact idxOf_filter_lt_of_idxOf_lt hnd_r ha_r' hb_r' (hmono a b ha hb hlt)

private theorem compilerTrust_false_of_groundRoles_mem {r s : Ix.Kernel.Role}
    (hs : s ∈ Ix.Cert.groundRoles r) : IxVM.Refinement.compilerTrust r = false := by
  unfold IxVM.Refinement.compilerTrust
  split
  · have h : Ix.Cert.groundRoles .trustCompiler = [] := by decide
    rw [h] at hs; nomatch hs
  · have h : Ix.Cert.groundRoles .reduceBool = [] := by decide
    rw [h] at hs; nomatch hs
  · have h : Ix.Cert.groundRoles .reduceNat = [] := by decide
    rw [h] at hs; nomatch hs
  · have h : Ix.Cert.groundRoles .ofReduceBool = [] := by decide
    rw [h] at hs; nomatch hs
  · have h : Ix.Cert.groundRoles .ofReduceNat = [] := by decide
    rw [h] at hs; nomatch hs
  · rfl

private theorem contains_of_recordAt_some {E : Ixon.Env} {x : _root_.Address} {c : Ixon.Constant}
    (hrec : Ix.Cert.recordAt E x = some c) : E.consts.contains x = true := by
  unfold Ix.Cert.recordAt at hrec
  rw [Std.HashMap.contains_eq_isSome_getElem?, ← Std.HashMap.get?_eq_getElem?]
  cases hg : E.consts.get? x with
  | none => rw [hg] at hrec; cases hrec
  | some _ => rfl

/-- **Unconditional role reachability embedding**: when `E` agrees with `E_role` on `order_role`,
every `UsedCompiledReachAt t E_role (BindingSeeds t)` node belongs to
`UsedCompiledReachAt t E (fun a => a ∈ seeds ∨ BindingSeeds t a)` provided `RecursorEdge` is
preserved along `order_role`. -/
theorem usedCompiledReach_role_subset
    {t : Ix.Kernel.RoleTable} {E E_role : Ixon.Env}
    {order_role seeds : List _root_.Address}
    (hcomp_r : ∀ a, a ∈ order_role ↔
      IxVM.Consistency.UsedCompiledReachAt t E_role (IxVM.Refinement.BindingSeeds t) a)
    (hagree : ∀ a ∈ order_role,
      Ix.Cert.recordAt E a = Ix.Cert.recordAt E_role a ∧ E.consts.contains a = true)
    (hrec_edge : ∀ a b, a ∈ order_role → b ∈ order_role →
      Ix.Cert.RecursorEdge E_role a b → Ix.Cert.RecursorEdge E a b) :
    ∀ {a : _root_.Address},
      IxVM.Consistency.UsedCompiledReachAt t E_role (IxVM.Refinement.BindingSeeds t) a →
      IxVM.Consistency.UsedCompiledReachAt t E
        (fun x => x ∈ seeds ∨ IxVM.Refinement.BindingSeeds t x) a := by
  intro a hr
  induction hr with
  | @seed x hx hcont =>
    have hx_mem : x ∈ order_role := (hcomp_r x).mpr (.seed hx hcont)
    exact .seed (.inr hx) (hagree x hx_mem).2
  | @step x y hrx hedge ih =>
    have hx_mem : x ∈ order_role := (hcomp_r x).mpr hrx
    have hy_mem : y ∈ order_role := (hcomp_r y).mpr (.step hrx hedge)
    obtain ⟨c, hrec_x, hstep⟩ := hedge
    refine .step ih ⟨c, (hagree x hx_mem).1.trans hrec_x, ?_⟩
    rcases hstep with hown | ⟨href, _⟩
    · exact .inl hown
    · exact .inr ⟨href, (hagree y hy_mem).2⟩
  | @ground x y hrx hgrd ih =>
    have hx_mem : x ∈ order_role := (hcomp_r x).mpr hrx
    have hy_mem : y ∈ order_role := (hcomp_r y).mpr (.ground hrx hgrd)
    obtain ⟨_, s, hs_addr, htrig⟩ := hgrd
    refine .ground ih ⟨(hagree y hy_mem).2, s, hs_addr, ?_⟩
    rcases htrig with ⟨r, p, hr_addr, hs_gr, hp_own⟩ | ⟨c, hrec_x, hs_lit⟩
    · refine .inl ⟨r, p, hr_addr, hs_gr, ?_⟩
      rcases hp_own with hp_eq | ⟨c, hrec_p, hown_p⟩
      · exact .inl hp_eq
      · have hct := compilerTrust_false_of_groundRoles_mem hs_gr
        have hp_mem : p ∈ order_role := (hcomp_r p).mpr
          (.seed (.inl ⟨r, hct, hr_addr⟩) (contains_of_recordAt_some hrec_p))
        exact .inr ⟨c, (hagree p hp_mem).1.trans hrec_p, hown_p⟩
    · exact .inr ⟨c, (hagree x hx_mem).1.trans hrec_x, hs_lit⟩
  | @recursor x y hrx hrec ih =>
    have hx_mem : x ∈ order_role := (hcomp_r x).mpr hrx
    have hy_mem : y ∈ order_role := (hcomp_r y).mpr (.recursor hrx hrec)
    exact .recursor ih (hrec_edge x y hx_mem hy_mem hrec)

private theorem preludeShape_compilerTrust_false :
    ∀ s ∈ Ix.Kernel.preludeShape.flatten, IxVM.Refinement.compilerTrust s = false := by
  decide

private theorem pickSpec_append_of_not_declares {md : Ix.Kernel.Mode}
    (n : Option (Ix.Kernel.Key md)) :
    ∀ (xs ys : List (Ix.Kernel.Declaration md)),
      (∀ d ∈ ys, Ix.Kernel.Frontend.declares n d = false) →
      Ix.Kernel.Frontend.pickSpec n (xs ++ ys) =
        ((Ix.Kernel.Frontend.pickSpec n xs).1, (Ix.Kernel.Frontend.pickSpec n xs).2 ++ ys)
  | [], [], _ => rfl
  | [], y :: ys, hys => by
    have hy : Ix.Kernel.Frontend.declares n y = false := hys y List.mem_cons_self
    have hrest := pickSpec_append_of_not_declares n [] ys
      (fun d hd => hys d (List.mem_cons_of_mem y hd))
    simp only [List.nil_append, Ix.Kernel.Frontend.pickSpec] at hrest
    simp only [List.nil_append, Ix.Kernel.Frontend.pickSpec, hy, Bool.false_eq_true, ↓reduceIte,
      hrest]
  | x :: xs, ys, hys => by
    simp only [List.cons_append, Ix.Kernel.Frontend.pickSpec]
    by_cases hx : Ix.Kernel.Frontend.declares n x = true
    · simp [hx]
    · have hxf : Ix.Kernel.Frontend.declares n x = false := Bool.eq_false_iff.mpr hx
      simp only [hxf, Bool.false_eq_true, ↓reduceIte]
      rw [pickSpec_append_of_not_declares n xs ys hys]
      rfl

private theorem frontSpec_append_of_not_declares {md : Ix.Kernel.Mode} :
    ∀ (ps xs ys : List (Ix.Kernel.Declaration md)),
      (∀ p ∈ ps, ∀ d ∈ ys,
        Ix.Kernel.Frontend.declares (Ix.Kernel.Frontend.preludeKey p) d = false) →
      Ix.Kernel.Frontend.frontSpec ps (xs ++ ys) =
        ((Ix.Kernel.Frontend.frontSpec ps xs).1,
         (Ix.Kernel.Frontend.frontSpec ps xs).2 ++ ys)
  | [], _, _, _ => rfl
  | p :: ps, xs, ys, hnot => by
    have hp := pickSpec_append_of_not_declares (Ix.Kernel.Frontend.preludeKey p) xs ys
      (hnot p List.mem_cons_self)
    have hps := frontSpec_append_of_not_declares ps
      (Ix.Kernel.Frontend.pickSpec (Ix.Kernel.Frontend.preludeKey p) xs).2 ys
      (fun p' hp' d hd => hnot p' (List.mem_cons_of_mem p hp') d hd)
    simp only [Ix.Kernel.Frontend.frontSpec, hp, hps]

/-- **Unconditional `frontOf` splitting for non-role walked declarations**: no declaration `d` whose
names are `Core.keyOf t x` with `x ∉ order_role` matches any prelude key, so `frontOf` leaves
`decls_w` untouched at the tail of `.2` and produces the identical front `.1`. -/
theorem frontOf_append_nonPrelude
    {V : IxVM.Refinement.View} {b : Ix.Kernel.Admission.Binding}
    {t : Ix.Kernel.RoleTable} {E_role : Ixon.Env} {limits : Ix.Kernel.Admission.Limits}
    {order_role : List _root_.Address} {envA : Ix.Kernel.Env .anon}
    {pre : Ix.Kernel.Reader.Prelude .anon} {st_role : Ix.Kernel.Reader.State .anon}
    {decls_role decls_w : Array (Ix.Kernel.Declaration .anon)}
    (hadm : TableAdmittedAt V b t E_role limits order_role envA pre st_role decls_role)
    (hdecls_w : ∀ d ∈ decls_w.toList, ∀ n ∈ d.names, ∃ x, n = Core.keyOf t x ∧ x ∉ order_role) :
    (Ix.Kernel.Frontend.frontOf #[] pre.ix.decls.toList (decls_role ++ decls_w)).1.toList =
      (Ix.Kernel.Frontend.frontOf #[] pre.ix.decls.toList decls_role).1.toList ∧
    (Ix.Kernel.Frontend.frontOf #[] pre.ix.decls.toList (decls_role ++ decls_w)).2.toList =
      (Ix.Kernel.Frontend.frontOf #[] pre.ix.decls.toList decls_role).2.toList ++ decls_w.toList := by
  have hroles := (preludeFor_decls_roles hadm.preludeFor).2
  have hba := (Ix.Kernel.Admission.admitBinding_ok_iff _ _ _).mp hadm.admitBinding
  have hnot : ∀ p ∈ pre.ix.decls.toList, ∀ d ∈ decls_w.toList,
      Ix.Kernel.Frontend.declares (Ix.Kernel.Frontend.preludeKey p) d = false := by
    intro p hp d hd
    cases hpk : Ix.Kernel.Frontend.preludeKey p with
    | none => rfl
    | some k =>
      have hk_mem : k ∈ p.names := by
        unfold Ix.Kernel.Frontend.preludeKey at hpk
        cases hpn : p.names with
        | nil => simp [hpn] at hpk
        | cons n₀ ns =>
          simp only [hpn, List.head?_cons, Option.some.injEq] at hpk
          rw [← hpk]
          exact List.mem_cons_self
      obtain ⟨s, hs, rfl⟩ := hroles p hp k hk_mem
      have hct := preludeShape_compilerTrust_false s hs
      simp only [Ix.Kernel.Frontend.declares, Option.any_some]
      cases hc : d.names.contains (.role s) with
      | false => rfl
      | true =>
        have hmem_d : (.role s : Ix.Kernel.Key .anon) ∈ d.names := List.mem_of_elem_eq_true hc
        obtain ⟨x, hx_eq, hx_not⟩ := hdecls_w d hd (.role s) hmem_d
        exact absurd hx_eq.symm (keyOf_nonRole_ne_role hadm hba hx_not hct)
  obtain ⟨h1_aw, h2_aw⟩ := Ix.Kernel.Frontend.frontOf_toList
    pre.ix.decls.toList #[] (decls_role ++ decls_w)
  obtain ⟨h1_a, h2_a⟩ := Ix.Kernel.Frontend.frontOf_toList
    pre.ix.decls.toList #[] decls_role
  have hfs := frontSpec_append_of_not_declares pre.ix.decls.toList decls_role.toList decls_w.toList hnot
  rw [h1_aw, h2_aw, h1_a, h2_a, Array.toList_append, hfs]
  simp

/-- When `hoistNatOpGround` leaves both rest arrays in place (e.g., when no pinned `Nat` operation
precedes its ground), `preparePrelude` appends `decls_w` directly after
`preparePrelude pre.ix decls_role`. -/
theorem preparePrelude_append_of_hoist_id
    {V : IxVM.Refinement.View} {b : Ix.Kernel.Admission.Binding}
    {t : Ix.Kernel.RoleTable} {E_role : Ixon.Env} {limits : Ix.Kernel.Admission.Limits}
    {order_role : List _root_.Address} {envA : Ix.Kernel.Env .anon}
    {pre : Ix.Kernel.Reader.Prelude .anon} {st_role : Ix.Kernel.Reader.State .anon}
    {decls_role decls_w : Array (Ix.Kernel.Declaration .anon)}
    (hadm : TableAdmittedAt V b t E_role limits order_role envA pre st_role decls_role)
    (hdecls_w : ∀ d ∈ decls_w.toList, ∀ n ∈ d.names, ∃ x, n = Core.keyOf t x ∧ x ∉ order_role)
    (hhoist_r : (Ix.Kernel.Frontend.hoistNatOpGround
        (Ix.Kernel.Frontend.frontOf #[] pre.ix.decls.toList decls_role).2).1 =
      (Ix.Kernel.Frontend.frontOf #[] pre.ix.decls.toList decls_role).2)
    (hhoist_rw : (Ix.Kernel.Frontend.hoistNatOpGround
        (Ix.Kernel.Frontend.frontOf #[] pre.ix.decls.toList (decls_role ++ decls_w)).2).1 =
      (Ix.Kernel.Frontend.frontOf #[] pre.ix.decls.toList (decls_role ++ decls_w)).2) :
    (Ix.Kernel.Frontend.preparePrelude pre.ix (decls_role ++ decls_w)).toList =
      (Ix.Kernel.Frontend.preparePrelude pre.ix decls_role).toList ++ decls_w.toList := by
  obtain ⟨hf1, hf2⟩ := frontOf_append_nonPrelude hadm hdecls_w
  rw [Ix.Kernel.Frontend.preparePrelude_front, Ix.Kernel.Frontend.preparePrelude_front,
    Array.toList_append, Array.toList_append, hhoist_r, hhoist_rw, hf1, hf2, List.append_assoc]

/-! ## Section 4: Minimal Residual Isolation (`SafeExprRefsGap`, `safeRefsInputs`) -/

/-- Minimal residual obligations on `SafeRefsInputs` beyond `CircuitExprSafeRefs` and the
unconditional theorems in Sections 1–3:
separating `decls_role_full` (`StreamRead` / `prepareWith`) from `decls_role_bare`
(`StreamReadBare` / `prepareBare` on the pruned role prefix), together with bare `.recr` /
inductive `.muts` `L1.RecordReadsAs` lowering. -/
structure SafeExprRefsGap : Prop where
  rolePrefixStreamReadBare_rest :
    ∀ {V : IxVM.Refinement.View} {extra : List ByteArray} {calls : List (Call F)}
      {b : Ix.Kernel.Admission.Binding} {t : Ix.Kernel.RoleTable}
      {E₀ E E_role E_core : Ixon.Env} {limits : Ix.Kernel.Admission.Limits}
      {order order_role : List _root_.Address} {envA : Ix.Kernel.Env .anon}
      {pre : Ix.Kernel.Reader.Prelude .anon} {st_role : Ix.Kernel.Reader.State .anon}
      {decls_role : Array (Ix.Kernel.Reader.CDecl .anon)}
      {seeds : List _root_.Address},
      TableAdmittedAt V b t E_role limits order_role envA pre st_role decls_role →
      IxVM.Consistency.Bounded calls →
      IxVM.Consistency.LoadedBy calls E₀ →
      ¬ V.HashedCollision extra calls →
      L1.EnvDecoded E_core →
      ¬ L1.EnvInternalCollision E_core →
      (∀ x c_x, Ix.Cert.recordAt E x = some c_x → Ix.Cert.recordAt E_core x = some c_x) →
      (∀ x bs, E.blobs.get? x = some bs → E_core.blobs.get? x = some bs) →
      (∀ a ∈ order_role, Ix.Cert.recordAt E a = Ix.Cert.recordAt E_role a ∧
        E.consts.contains a = true) →
      (∀ a bytes, (a, bytes) ∈ Ix.Cert.blobsOf E_role order_role →
        E.blobs.get? a = some bytes) →
      IxVM.Consistency.UsedClosureOrderAt t E
        (fun a => a ∈ seeds ∨ IxVM.Refinement.BindingSeeds t a) order →
      order = order.filter (· ∈ order_role) ++ order.filter (· ∉ order_role) →
      (∀ a b', a ∈ order.filter (· ∈ order_role) → b' ∈ order.filter (· ∈ order_role) →
        order.idxOf a < order.idxOf b' → order_role.idxOf a < order_role.idxOf b') →
      AuthenticExactStore
        (Ix.Kernel.Admission.streamContext _root_.Address.admissionHash t pre
          (Ix.Cert.Stream.decodedOf E order) (Ix.Cert.blobsOf E order) (Ix.Cert.hintsOf E)).store →
      (∀ a ∈ order_role, a ∈ order) ∧
        (∀ (decls_w : Array (Ix.Kernel.Declaration .anon)),
          (∀ d ∈ decls_w.toList, ∀ n ∈ d.names, ∃ x, n = Core.keyOf t x ∧ x ∉ order_role) →
          (Ix.Kernel.Frontend.preparePrelude pre.ix (decls_role ++ decls_w)).toList =
            (Ix.Kernel.Frontend.preparePrelude pre.ix decls_role).toList ++ decls_w.toList) ∧
        ((Ix.Kernel.Frontend.preparePrelude pre.ix decls_role).toList.flatMap
          (fun d => (IxVM.Consistency.installs d).map (·.name))).Nodup ∧
        (∀ d ∈ (Ix.Kernel.Frontend.preparePrelude pre.ix decls_role).toList,
          ∀ ci₀ ∈ IxVM.Consistency.installs d,
          ∀ x, ci₀.name = Core.keyOf t x →
            x ∈ order_role ∨
            ∀ c_x,
              (Ix.Cert.recordAt E₀ x = some c_x ∨
                (∃ owner ms i d_m,
                  x = Core.dprjAddr owner i ∧ i < UInt64.size ∧
                  c_x = ⟨.dPrj ⟨i.toUInt64, owner⟩, #[], #[], #[], #[]⟩ ∧
                  Claim.MutsMemberCheckedAtFull calls b.address t owner ms i ∧
                  ms[i]? = some (.defn d_m))) →
              Ix.Cert.ownerOf x c_x ∈ order_role) ∧
        ∃ st_r,
          StreamReadBare
            (Ix.Kernel.Admission.streamContext _root_.Address.admissionHash t pre
              (Ix.Cert.Stream.decodedOf E order) (Ix.Cert.blobsOf E order) (Ix.Cert.hintsOf E))
            pre.state (Ix.Cert.Stream.decodedOf E order_role) st_r decls_role ∧
          (∀ k ∈ pre.state.keys, st_r.SameAt pre.state k) ∧
          (∀ x c_x,
            ((x ∈ order_role ∧ Ix.Cert.recordAt E x = some c_x ∧
                ((∃ d_x, c_x.info = .defn d_x) ∨ (∃ ax, c_x.info = .axio ax) ∨
                  (∃ qt, c_x.info = .quot qt) ∨ (∃ rc, c_x.info = .recr rc) ∨
                  Ix.Cert.ownerOf x c_x ≠ x)) ∨
              (∃ blk ∈ order_role, OwnedOrProjOf E blk x c_x)) →
            ∃ ci₀,
              ci₀.name = Core.keyOf t x ∧
              L1.RecordReadsAs t E_core x c_x ci₀ ∧
              (IxVM.Consistency.inertKey (Core.keyOf t x) = false →
                ∃ d,
                  d ∈ (Ix.Kernel.Frontend.preparePrelude pre.ix decls_role).toList ∧
                  ci₀ ∈ IxVM.Consistency.installs d))
  indRecRecordReadBare :
    ∀ {V : IxVM.Refinement.View} {extra : List ByteArray} {calls : List (Call F)}
      {b : Ix.Kernel.Admission.Binding} {t : Ix.Kernel.RoleTable}
      {E₀ E E_role E_core : Ixon.Env} {limits : Ix.Kernel.Admission.Limits}
      {order order_role : List _root_.Address} {envA : Ix.Kernel.Env .anon}
      {pre : Ix.Kernel.Reader.Prelude .anon} {st_role st : Ix.Kernel.Reader.State .anon}
      {decls_role prev_cDecls : Array (Ix.Kernel.Reader.CDecl .anon)}
      {prev_recs suf_recs : List (_root_.Address × Ixon.Constant)}
      {seeds : List _root_.Address}
      {a : _root_.Address} {c : Ixon.Constant},
      TableAdmittedAt V b t E_role limits order_role envA pre st_role decls_role →
      IxVM.Consistency.Bounded calls →
      IxVM.Consistency.LoadedBy calls E₀ →
      ¬ V.HashedCollision extra calls →
      L1.EnvDecoded E_core →
      ¬ L1.EnvInternalCollision E_core →
      (∀ x c_x, Ix.Cert.recordAt E x = some c_x → Ix.Cert.recordAt E_core x = some c_x) →
      (∀ x bs, E.blobs.get? x = some bs → E_core.blobs.get? x = some bs) →
      AuthenticExactStore
        (Ix.Kernel.Admission.streamContext _root_.Address.admissionHash t pre
          (Ix.Cert.Stream.decodedOf E order) (Ix.Cert.blobsOf E order) (Ix.Cert.hintsOf E)).store →
      IxVM.Consistency.UsedClosureOrderAt t E
        (fun x => x ∈ seeds ∨ IxVM.Refinement.BindingSeeds t x) order →
      Ix.Cert.Stream.decodedOf E order = prev_recs ++ (a, c) :: suf_recs →
      StreamReadBare
        (Ix.Kernel.Admission.streamContext _root_.Address.admissionHash t pre
          (Ix.Cert.Stream.decodedOf E order) (Ix.Cert.blobsOf E order) (Ix.Cert.hintsOf E))
        pre.state prev_recs st prev_cDecls →
      a ∉ order_role →
      Ix.Cert.recordAt E₀ a = some c →
      WkAll calls b.address t E₀ a →
      ¬ IxVM.Consistency.OutsideLogicAt E₀ a →
      (∀ a' c', (a', c') ∈ Ix.Cert.Stream.decodedOf E order → a' ∉ order_role →
        Ix.Cert.recordAt E₀ a' = some c' ∧
        WkAll calls b.address t E₀ a' ∧
        ¬ IxVM.Consistency.OutsideLogicAt E₀ a') →
      (∀ k ∈ pre.state.keys, st.SameAt pre.state k) →
      ((∃ rc, c.info = .recr rc) ∨
        (∃ ms, c.info = .muts ms ∧ ¬ ms.all (fun | .defn _ => true | _ => false))) →
      ∃ r,
        Ix.Kernel.Reader.readRecordBare
          (Ix.Kernel.Admission.streamContext _root_.Address.admissionHash t pre
            (Ix.Cert.Stream.decodedOf E order) (Ix.Cert.blobsOf E order) (Ix.Cert.hintsOf E))
          st a c = .ok r ∧
        (∀ k ∈ pre.state.keys, (st.commit r).SameAt pre.state k) ∧
        (∀ d ∈ r.decls.toList,
          (∃ block nP, d = .indDecl block nP) ∧
          ∀ n ∈ d.names, ∃ x,
            n = Core.keyOf t x ∧
            x ∉ order_role ∧
            (∀ c', Ix.Cert.recordAt E₀ x = some c' →
              (∃ rc, c'.info = .recr rc) ∨ (∃ p, c'.info = .iPrj p) ∨
              (∃ p, c'.info = .cPrj p) ∨ (∃ p, c'.info = .rPrj p)) ∧
            (∀ owner ms (i : Nat) d_m,
              Claim.MutsMemberCheckedAtFull calls b.address t owner ms i →
              ms[i]? = some (.defn d_m) →
              x ≠ Core.dprjAddr owner i)) ∧
        ((r.decls.toList.flatMap (fun d => (IxVM.Consistency.installs d).map (·.name))).Nodup) ∧
        (∀ d ∈ r.decls.toList, ∀ ci₀ ∈ IxVM.Consistency.installs d,
          ∀ d₀ ∈ (Ix.Kernel.Frontend.preparePrelude pre.ix prev_cDecls).toList,
          ∀ ci₁ ∈ IxVM.Consistency.installs d₀, ci₁.name ≠ ci₀.name) ∧
        (∀ x c_x,
          ((x = a ∧ c_x = c ∧ ∃ rc, c.info = .recr rc) ∨
            OwnedOrProjOf E a x c_x) →
          ∃ d ci₀,
            d ∈ (Ix.Kernel.Frontend.preparePrelude pre.ix prev_cDecls).toList ++ r.decls.toList ∧
            ci₀ ∈ IxVM.Consistency.installs d ∧
            ci₀.name = Core.keyOf t x ∧
            L1.RecordReadsAs t E_core x c_x ci₀)
/-- Assemble `SafeRefsInputs` from `CircuitExprSafeRefs`, the unconditional theorems in
Sections 1–3, and `SafeExprRefsGap`. -/
theorem safeRefsInputs (hCircuit : CircuitExprSafeRefs) (hGap : SafeExprRefsGap) : SafeRefsInputs where
  safe_expr_refs_resolve := safe_expr_refs_resolve_of_circuitExprSafeRefs hCircuit
  rolePrefixStreamReadBare := by
    intro V extra calls b t E₀ E E_role E_core limits order order_role envA pre st_role decls_role
      seeds hadm hbound hload₀ hnoCol hexact_c hnoInt_c hrec_sub hblob_sub hagree hblob_r
      huord hsplit hmono hauth
    obtain ⟨hsub_r, hrest⟩ := hGap.rolePrefixStreamReadBare_rest
      hadm hbound hload₀ hnoCol hexact_c hnoInt_c hrec_sub hblob_sub hagree hblob_r
      huord hsplit hmono hauth
    exact ⟨order_filter_role_eq_of_subset huord.nodup hadm.usedClosureOrder.nodup hsub_r hsplit hmono,
      hrest⟩
  indRecRecordReadBare := hGap.indRecRecordReadBare
  indBlockCtorIdx := indBlockCtorIdx_of_exact_noCollision

end IxVM.Refinement.Assembly

