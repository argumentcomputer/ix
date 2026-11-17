import IxVMRefinement.Assembly.PointFormer
import IxVMRefinement.Assembly.NativeBlockReads
import IxVMRefinement.Assembly.NativeBlockNewFacts

/-! # The readings of a block's members and constructors on the constructors-only route

The walked check of member `i` of a block (any number of inductive members) loads the member's
projection record and, in the `Induct` arm, loads every constructor of the member in order
(`check_inductive_shape_ctors` on the native branch, `check_modeled_ctors` on the modeled one),
validating each constructor type's scope (`validate_expr_well_scoped`) right after its load. From
these loads, over the run's store `E₀`:

* `member_reads_at`: the reading of member `i`'s type, closed with its level parameters defined
  and no free variable (the `Induct` prelude validated it), the member's counts below `2 ^ 56`,
  and `Reads` at its projection address;
* `ctorSlots_at`, `ctorSlot_reads_at`: every constructor slot has its load and scope check, and
  the reading of the constructor, closed likewise, with its stored index, level and parameter
  counts pinned, its counts below `2 ^ 56`, and `Reads` at its projection address;
* `point_member_reads`, `point_ctor_reads`: the same at every member of the walked block, the
  reading over the step's store `E` being the one over `E₀` (`StepStore.runBlob`);
* `point_keys_distinct`: the members' keys and the constructor slots' keys are pairwise distinct
  (the records the run's store holds at those addresses differ). A projection address reads its
  indices as 64-bit numbers, so a slot index is asked below `2 ^ 64`; member indices are, the
  block having fewer than `2 ^ 39` members (`mutsMemberAt_size_lt`).
-/

namespace IxVM.Refinement.Typing

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library
open IxVM (F)
open IxVM.Consistency
open Ix.Kernel (ConstantInfo ConstantVal)

set_option maxHeartbeats 1600000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-! ## The constructor loads of the two loops, with their scope checks -/

/-- **A constructor slot the circuit loaded and scope-checked**: a `get_ci_cprj` run in `calls`
on the block `b` at member `i` and slot `j`, whose `Ctor` value carries the slot, the level
count and the parameter count the loop pinned, followed (on an extension of the load's heap) by
the observed `validate_expr_well_scoped` of the loaded type at depth `0` and the level count. -/
def CtorSlotScoped (calls : List (Call F)) (b : Bytes.Address) (i : F) (j levels params : Nat) :
    Prop :=
  ∃ (bp ptr : SourceValue F) (h h' m₁ m₂ : Heap F) (cs cs₂ : List (Call F))
    (nl ty pb mi sl np nf us v₂ : SourceValue F),
    ObsFn Core.W "Ingress::get_ci_cprj" [bp, .field i, .field (j : F)] h ptr h' cs ∧
    (∀ cl ∈ cs, cl ∈ calls) ∧ Bytes.RepAddressRef Core.addrTy h b bp ∧
    loadValue h' ptr = .ok (.construct Core.kciEnum "Ctor" [nl, ty, pb, mi, sl, np, nf, us]) ∧
    sl = .field (j : F) ∧ nl = .field (levels : F) ∧ np = .field (params : F) ∧
    Heap.Extends h' m₁ ∧
    ObsFn Core.W "KernelCheck::validate_expr_well_scoped" [ty, .field 0, .field (levels : F)]
      m₁ v₂ m₂ cs₂ ∧
    (⟨"KernelCheck::validate_expr_well_scoped", [ty, .field 0, .field (levels : F)], m₁⟩ :
      Call F) ∈ calls

/-- **The native constructor loop loads and scope-checks every slot from its start.** -/
theorem native_ctor_slots_scoped {b : Bytes.Address} {n levels params : Nat} {i : F}
    (hn : n < 72057594037927936) {calls : List (Call F)} :
    ∀ (m k : Nat) {rc former np ni nl blockArg sortLevel safety r : SourceValue F}
      {h h' : Heap F} {cs : List (Call F)}, m + k = n →
      np = .field (params : F) → nl = .field (levels : F) →
      (∀ cl ∈ cs, cl ∈ calls) →
      Bytes.RepAddressRef Core.addrTy h b blockArg →
      ObsFn Core.W "KernelCheck::check_inductive_shape_ctors"
        [rc, former, np, ni, .field (n : F), nl, blockArg, .field i, sortLevel, safety,
          .field (k : F)] h r h' cs →
      ∀ j, k ≤ j → j < n → CtorSlotScoped calls b i j levels params := by
  intro m
  induction m with
  | zero =>
    intro k rc former np ni nl blockArg sortLevel safety r h h' cs hmk _ _ _ _ _ j hkj hjn
    omega
  | succ m ih =>
    intro k rc former np ni nl blockArg sortLevel safety r h h' cs hmk hnp hnl hsub hbp ev
      j hkj hjn
    subst hnl
    match Obs.«KernelCheck::check_inductive_shape_ctors».obs ev with
    | .n0 (op17 := op) .. =>
      have hzero : (.field ((0 : Nat) : F) : SourceValue F) =
          .field (((n - k : Nat) : F)) := by
        simpa using Decl.evalBinOp_sub_nat (by omega : k ≤ n) op
      have := Decl.nat_eq_of_field_eq_bounded (by decide) (by omega) hzero
      omega
    | .other (m34 := after) (p41 := ptr) (cs47 := loadCalls)
        (x_c_nlvls := cnl) (x_cty := cty) (x_c_block := cblk)
        (x_c_ind_idx := cmi) (x_c_cidx := csl) (x_c_np := cnp) (x_c_nf := cnf)
        (x_c_unsafe := cus) (m144 := scopeHeap) (ev154 := addrEq) (ev331 := scopeRun)
        (m655 := nextHeap) (cs695 := nextCalls) (v708 := nextIndex)
        (ev49 := loaded) (ld43 := tag) (heq233 := slotChecked) (heq261 := levelsChecked)
        (heq289 := paramsChecked) (op792 := addition) (ev697 := nextRun)
        (hc794 := allCalls) .. =>
      by_cases hjk : j = k
      · subst hjk
        exact ⟨blockArg, ptr, h, after, scopeHeap, _, loadCalls, _, cnl, cty, cblk, cmi, csl,
          cnp, cnf, cus, _, loaded, fun cl hcl => hsub cl (by rw [allCalls]; simp [hcl]), hbp,
          tag, slotChecked, levelsChecked, paramsChecked.trans hnp, addrEq.heap_extends, scopeRun,
          hsub _ (by rw [allCalls]; simp)⟩
      · have added := Decl.evalBinOp_add_nat k 1 addition
        subst nextIndex
        have nextMember : (⟨"KernelCheck::check_inductive_shape_ctors",
            [rc, former, np, ni, .field (n : F), .field (levels : F), blockArg, .field i,
              sortLevel, safety, .field ((k + 1 : Nat) : F)], nextHeap⟩ : Call F) ∈ cs := by
          rw [allCalls]
          simp
        have nextBlock := Bytes.repAddressRef_heapMono₂ Core.addrTy
          (ev.call_heap_bounds nextMember).1 hbp
        exact ih (k + 1) (by omega) hnp rfl
          (fun cl hcl => hsub cl (by rw [allCalls]; simp [hcl])) nextBlock nextRun j
          (by omega) hjn

/-- **The modeled constructor loop loads and scope-checks every slot from its start.** -/
theorem modeled_ctor_slots_scoped {b : Bytes.Address} {n levels params : Nat} {i : F}
    (hn : n < 72057594037927936) {calls : List (Call F)} :
    ∀ (m k : Nat) {rc np ni nl blockArg safety r : SourceValue F}
      {h h' : Heap F} {cs : List (Call F)}, m + k = n →
      np = .field (params : F) → nl = .field (levels : F) →
      (∀ cl ∈ cs, cl ∈ calls) →
      Bytes.RepAddressRef Core.addrTy h b blockArg →
      ObsFn Core.W "KernelCheck::check_modeled_ctors"
        [rc, np, ni, .field (n : F), nl, blockArg, .field i, safety, .field (k : F)] h r h' cs →
      ∀ j, k ≤ j → j < n → CtorSlotScoped calls b i j levels params := by
  intro m
  induction m with
  | zero =>
    intro k rc np ni nl blockArg safety r h h' cs hmk _ _ _ _ _ j hkj hjn
    omega
  | succ m ih =>
    intro k rc np ni nl blockArg safety r h h' cs hmk hnp hnl hsub hbp ev j hkj hjn
    subst hnl
    match Obs.«KernelCheck::check_modeled_ctors».obs ev with
    | .n0 (op17 := op) .. =>
      have hzero : (.field ((0 : Nat) : F) : SourceValue F) =
          .field (((n - k : Nat) : F)) := by
        simpa using Decl.evalBinOp_sub_nat (by omega : k ≤ n) op
      have := Decl.nat_eq_of_field_eq_bounded (by decide) (by omega) hzero
      omega
    | .other (m34 := after) (p41 := ptr) (cs47 := loadCalls)
        (x_c_nlvls := cnl) (x_cty := cty) (x_c_block := cblk)
        (x_c_ind_idx := cmi) (x_c_cidx := csl) (x_c_np := cnp) (x_c_nf := cnf)
        (x_c_unsafe := cus) (m144 := scopeHeap) (ev154 := addrEq) (ev331 := scopeRun)
        (m500 := nextHeap) (cs540 := nextCalls) (v551 := nextIndex)
        (ev49 := loaded) (ld43 := tag) (heq233 := slotChecked) (heq261 := levelsChecked)
        (heq289 := paramsChecked) (op621 := addition) (ev542 := nextRun)
        (hc623 := allCalls) .. =>
      by_cases hjk : j = k
      · subst hjk
        exact ⟨blockArg, ptr, h, after, scopeHeap, _, loadCalls, _, cnl, cty, cblk, cmi, csl,
          cnp, cnf, cus, _, loaded, fun cl hcl => hsub cl (by rw [allCalls]; simp [hcl]), hbp,
          tag, slotChecked, levelsChecked, paramsChecked.trans hnp, addrEq.heap_extends, scopeRun,
          hsub _ (by rw [allCalls]; simp)⟩
      · have added := Decl.evalBinOp_add_nat k 1 addition
        subst nextIndex
        have nextMember : (⟨"KernelCheck::check_modeled_ctors",
            [rc, np, ni, .field (n : F), .field (levels : F), blockArg, .field i, safety,
              .field ((k + 1 : Nat) : F)], nextHeap⟩ : Call F) ∈ cs := by
          rw [allCalls]
          simp
        have nextBlock := Bytes.repAddressRef_heapMono₂ Core.addrTy
          (ev.call_heap_bounds nextMember).1 hbp
        exact ih (k + 1) (by omega) hnp rfl
          (fun cl hcl => hsub cl (by rw [allCalls]; simp [hcl])) nextBlock nextRun j
          (by omega) hjn

/-! ## The member's reading and its constructor slots -/

section Member

variable {t : Ix.Kernel.RoleTable} {calls : List (Call F)} {E₀ : Ixon.Env}
  {bAddr B : _root_.Address} {cb : Ixon.Constant} {ms : Array Ixon.MutConst} {n : Nat}

/-- A member index of a walked block is below `2 ^ 39`. -/
theorem member_idx_lt (hbound : Bounded calls) {i : Nat} {m : Ixon.MutConst}
    (hmem : ms[i]? = some m) (hchk : MutsMemberCheckedAtFullAt calls bAddr t B ms i n) :
    i < 549755813888 := by
  have hsize := mutsMemberAt_size_lt hbound hchk
  have hi := (Array.getElem?_eq_some_iff.mp hmem).1
  omega

/-- **The reading of member `i`'s type**, over the run's store: closed, with its level parameters
defined and no free variable (the `Induct` prelude validated its scope), the member's counts
below `2 ^ 56`, and `Reads` at the member's projection address under every capability record. -/
theorem member_reads_at (ht : t.check = .ok ()) (hbound : Bounded calls)
    (hS : LoadedReads.RunStore calls E₀) (hrec : ModeledBlockRecord E₀ B cb ms)
    {i : Nat} {ind : Ixon.Inductive} (hmem : ms[i]? = some (.indc ind))
    (hchk : MutsMemberCheckedAtFullAt calls bAddr t B ms i n) :
    ∃ ty₀ : Ix.Kernel.Expr .anon,
      (exprReader t (fun x => E₀.blobs.get? x) cb id (blockSelf t B ms)).read ind.typ =
        .ok ty₀ ∧
      ty₀.looseBVarsBounded 0 = true ∧
      ty₀.allLevelParamsDefined (List.range ind.lvls.toNat) = true ∧ ty₀.hasFvar = false ∧
      ind.lvls.toNat < 4294967296 ∧ ind.params.toNat < 72057594037927936 ∧
      ind.indices.toNat < 72057594037927936 ∧ ind.ctors.size < 72057594037927936 ∧
      ∀ caps : Ix.Kernel.IndCaps .anon, Reads t E₀ (Core.iprjAddr B i)
        (.indInfo ⟨Core.keyOf t (Core.iprjAddr B i), List.range ind.lvls.toNat, ty₀⟩ caps) := by
  have hi39 := member_idx_lt hbound hmem hchk
  have hi64 : i < UInt64.size := by
    have e : UInt64.size = 18446744073709551616 := rfl
    omega
  have hidx : (⟨i.toUInt64, B⟩ : Ixon.InductiveProj).idx.toNat = i := toNat_toUInt64_of_lt hi64
  have hchkA := mutsMemberAt_checkedAt hbound hchk hmem
  obtain ⟨_, _, m_chk, _, rc, ap, ptr, v, r_chk, cs_ld, cs_chk, bytes, E_ld,
    _, _, _, _, hhash, hblake, hload_ld, hL1, hsub_ld, hld, ev_chk, _, hsub_chk⟩ :=
    Assembly.checkedAtFull_loadedL1 hbound ⟨n, hchkA⟩
  have hrecP : Ix.Cert.recordAt E₀ (memberAddr B i (.indc ind)) =
      some (memberProjection B i (.indc ind)) :=
    (hS.recordOf_eq_recordAt _).symm.trans (hrec.former i ind hmem)
  have hrecB : Ix.Cert.recordAt E₀ B = some cb :=
    (hS.recordOf_eq_recordAt _).symm.trans hrec.record
  -- the reading and `Reads`
  obtain ⟨ms₁, ind₁, ty₀, h1, h2, -, hty, hreads, -⟩ :=
    LoadedReads.loadedL1_ind_reads (p := ⟨i.toUInt64, B⟩) ht hS hload_ld hsub_ld hhash
      hblake hL1 hrecP rfl hrecB hrec.logic
  have hms₁ : ms₁ = ms := Ixon.ConstantInfo.muts.inj (h1.symm.trans hrec.muts)
  subst ms₁
  have h2' : ms[i]? = some (.indc ind₁) := by
    rw [← hidx]
    exact h2
  rw [hmem] at h2'
  have hind₁ : ind₁ = ind := (Ixon.MutConst.indc.inj (Option.some.inj h2')).symm
  subst ind₁
  -- the scope check of the prelude, on the loaded value
  obtain ⟨-, -, v', hld', hraw⟩ := LoadedReads.loadedL1_record hS hsub_ld hhash hblake hL1 hrecP
  have hvv : v' = v := Except.ok.inj (hld'.symm.trans hld)
  subst hvv
  have hinfo : (memberProjection B i (.indc ind)).info = .iPrj ⟨i.toUInt64, B⟩ := rfl
  unfold L1.RawCIRep at hraw
  rw [hinfo] at hraw
  obtain ⟨-, lcB, cb', ms', ind', blobs, hgetB, -, -, hexB, -, hcb', hms', -, raw⟩ := hraw
  obtain ⟨hhB, haB⟩ := hload_ld.1 _ lcB hgetB
  have hcb_eq : cb' = cb := hS.record_eq hrecB (Core.hashed_mono hsub_ld hhB) haB hexB
  subst cb'
  have hms_eq : ms' = ms := Ixon.ConstantInfo.muts.inj (hcb'.symm.trans hrec.muts)
  subst ms'
  rw [hidx] at hms' raw
  have hind_eq : ind' = ind := by
    rw [Array.getElem?_toList, hmem] at hms'
    exact (Ixon.MutConst.indc.inj (Option.some.inj hms')).symm
  subst ind'
  obtain ⟨hlv, hnp, hni, hnc, -, tyPtr, blkPtr, b, -, -, hv, rty⟩ := raw
  subst hv
  obtain ⟨prelude⟩ := Decl.native_prelude_calls ev_chk
  obtain ⟨-, hlbb, hdef⟩ := Assembly.validate_expr_well_scoped_spec
    (cx := readCtx t (fun x => E₀.blobs.get? x)) (self := blockSelf t B ms) hbound hlv rty
    prelude.initialExtended hty prelude.scopeRun (hsub_chk _ prelude.scopeMember)
  exact ⟨ty₀, hty, hlbb, hdef, Assembly.memberReader_read_noFvar hty, hlv, hnp, hni, hnc,
    hreads⟩

/-- **Every constructor slot of member `i` has its load and scope check**, on either route of the
`Induct` arm, with the member's level and parameter counts and their bounds. -/
theorem ctorSlots_at (hbound : Bounded calls) (hS : LoadedReads.RunStore calls E₀)
    (hrec : ModeledBlockRecord E₀ B cb ms) {i : Nat} {ind : Ixon.Inductive}
    (hmem : ms[i]? = some (.indc ind))
    (hchk : MutsMemberCheckedAtFullAt calls bAddr t B ms i n) :
    ∃ b : Bytes.Address, Core.ixAddr b = B ∧ ind.lvls.toNat < 4294967296 ∧
      ind.params.toNat < 72057594037927936 ∧ ind.ctors.size < 72057594037927936 ∧
      ∀ j < ind.ctors.size,
        CtorSlotScoped calls b ((i : Nat) : F) j ind.lvls.toNat ind.params.toNat := by
  have hi39 := member_idx_lt hbound hmem hchk
  have hi64 : i < UInt64.size := by
    have e : UInt64.size = 18446744073709551616 := rfl
    omega
  have hidx : (⟨i.toUInt64, B⟩ : Ixon.InductiveProj).idx.toNat = i := toNat_toUInt64_of_lt hi64
  have hchkA := mutsMemberAt_checkedAt hbound hchk hmem
  obtain ⟨_, _, m_chk, _, rc, ap, ptr, v, r_chk, cs_ld, cs_chk, bytes, E_ld,
    _, _, _, _, hhash, hblake, hload_ld, hL1, hsub_ld, hld, ev_chk, _, hsub_chk⟩ :=
    Assembly.checkedAtFull_loadedL1 hbound ⟨n, hchkA⟩
  have hrecP : Ix.Cert.recordAt E₀ (memberAddr B i (.indc ind)) =
      some (memberProjection B i (.indc ind)) :=
    (hS.recordOf_eq_recordAt _).symm.trans (hrec.former i ind hmem)
  have hrecB : Ix.Cert.recordAt E₀ B = some cb :=
    (hS.recordOf_eq_recordAt _).symm.trans hrec.record
  obtain ⟨-, -, v', hld', hraw⟩ := LoadedReads.loadedL1_record hS hsub_ld hhash hblake hL1 hrecP
  have hvv : v' = v := Except.ok.inj (hld'.symm.trans hld)
  subst hvv
  have hinfo : (memberProjection B i (.indc ind)).info = .iPrj ⟨i.toUInt64, B⟩ := rfl
  unfold L1.RawCIRep at hraw
  rw [hinfo] at hraw
  obtain ⟨-, lcB, cb', ms', ind', blobs, hgetB, -, -, hexB, -, hcb', hms', -, raw⟩ := hraw
  obtain ⟨hhB, haB⟩ := hload_ld.1 _ lcB hgetB
  have hcb_eq : cb' = cb := hS.record_eq hrecB (Core.hashed_mono hsub_ld hhB) haB hexB
  subst cb'
  have hms_eq : ms' = ms := Ixon.ConstantInfo.muts.inj (hcb'.symm.trans hrec.muts)
  subst ms'
  rw [hidx] at hms' raw
  have hind_eq : ind' = ind := by
    rw [Array.getElem?_toList, hmem] at hms'
    exact (Ixon.MutConst.indc.inj (Option.some.inj hms')).symm
  subst ind'
  obtain ⟨hlv, hnp, hni, hnc, -, tyPtr, blkPtr, b, hb_eq, hbp_m, hv, -⟩ := raw
  subst hv
  have hsafe : ind.isUnsafe = false := by
    have hl := hrec.logic
    simp only [IxVM.Consistency.InLogic, hrec.muts] at hl
    have hmemL : Ixon.MutConst.indc ind ∈ ms.toList :=
      List.mem_of_getElem? (by rw [Array.getElem?_toList]; exact hmem)
    exact (hl (.indc ind) hmemL).1
  simp only [L1.repBoolField, hsafe, Bool.false_eq_true, ↓reduceIte] at ev_chk
  refine ⟨b, hb_eq, hlv, hnp, hnc, ?_⟩
  intro j hj
  match Obs.«KernelCheck::check_const».obs ev_chk with
  | .Axiom_n1 (hv37 := hv) .. | .Axiom_other_n0 (hv37 := hv) ..
  | .Axiom_other_other (hv37 := hv) ..
  | .Defn (hv269 := hv) .. | .Thm (hv526 := hv) ..
  | .Opaque (hv825 := hv) .. | .Quot (hv1076 := hv) ..
  | .Ctor_n0_n0 (hv1941 := hv) .. | .Ctor_n0_other (hv1941 := hv) ..
  | .Ctor_other_n0 (hv1941 := hv) ..
  | .Ctor_other_other (hv1941 := hv) ..
  | .Rec_n0 (hv2631 := hv) .. | .Rec_other (hv2631 := hv) .. =>
    injection hv with _ htag _; exact absurd htag (by decide)
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
    injection hargs with hnp' hargs; injection hargs with hni' hargs
    injection hargs with hnc' hargs; injection hargs with hiu hargs
    injection hargs with hblk hargs; injection hargs with hidx' _
    subst hnl hty hnp' hni' hnc' hiu hblk hidx'
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
    | run _ m2_sh _ _ m50_sh _ _ _ _ m63_sh _ _ cs135 _ hm58 ev14_sh ev75_sh _ ev145_sh ev137
        hc225 =>
      have e_50 : Heap.Extends m1492 m50_sh := by rw [hm58]; exact Heap.Extends.snoc m1492 _
      have e_to_63 : Heap.Extends m_chk m63_sh :=
        e_to_1492.trans (e_50.trans (ev14_sh.heap_extends.trans
          (ev75_sh.heap_extends.trans ev145_sh.heap_extends)))
      have hsub_ctors : ∀ cl ∈ cs135, cl ∈ calls := fun cl hcl =>
        hsub_sh cl (by rw [hc225]; simp [hcl])
      have hbp := Bytes.repAddressRef_heapMono₂ Core.addrTy e_to_63 hbp_m
      exact native_ctor_slots_scoped hnc ind.ctors.size 0 (by omega) rfl rfl hsub_ctors hbp
        ev137 j (Nat.zero_le _) hj
  | .Induct_other_other (hv1240 := hv_ind) (hne1927 := hne_u) .. =>
    injection hv_ind with _ _ hargs
    injection hargs with _ hargs; injection hargs with _ hargs
    injection hargs with _ hargs; injection hargs with _ hargs
    injection hargs with _ hargs; injection hargs with hiu _
    exact absurd hiu.symm hne_u
  | .Induct_other_n0 (m2 := m2) (x_nlvls := xnl) (x_ty := xty)
      (x_n_params := xnp) (x_n_indices := xni) (x_num_ctors := xnc)
      (x_ind_block := xblk) (x_ind_idx := xidx)
      (m1283 := m1283) (m1333 := m1333) (m1354 := m1354) (m1376 := m1376)
      (m1396 := m1396) (m1427 := m1427) (m1440 := m1440) (m1470 := m1470)
      (m1492 := m1492) (m1701 := m1653) (m1745 := m1688) (m1793 := m1736)
      (cs1816 := cs_mc)
      (ev14 := ev_iu) (hv1240 := hv_ind) (ev1295 := ev_ws)
      (hm1362 := hm1354) (hm1384 := hm1376) (ev1343 := ev_emb)
      (hm1435 := hm1427) (ev1408 := ev_es) (ev1452 := ev_saf)
      (ev1482 := ev_mk) (ev1505 := ev_mod) (ev1663 := ev_fa) (ev1711 := ev_tele)
      (hm1801 := hm1736) (ev1757 := ev_rsl) (ev1818 := ev_mc) (hc1926 := hc) .. =>
    injection hv_ind with _ _ hargs
    injection hargs with hnl hargs; injection hargs with hty hargs
    injection hargs with hnp' hargs; injection hargs with hni' hargs
    injection hargs with hnc' hargs; injection hargs with _ hargs
    injection hargs with hblk hargs; injection hargs with hidx' _
    subst hnl hty hnp' hni' hnc' hblk hidx'
    have e_1376 : Heap.Extends m1283 m1376 := by rw [hm1376]; exact Heap.Extends.snoc m1283 _
    have e_1354 : Heap.Extends m1376 m1354 := by rw [hm1354]; exact Heap.Extends.snoc m1376 _
    have e_1427 : Heap.Extends m1333 m1427 := by rw [hm1427]; exact Heap.Extends.snoc m1333 _
    have e_1736 : Heap.Extends m1653 m1736 := by rw [hm1736]; exact Heap.Extends.snoc m1653 _
    have e_to_1688 : Heap.Extends m_chk m1688 :=
      ev_iu.heap_extends.trans (ev_ws.heap_extends.trans
        (e_1376.trans (e_1354.trans (ev_emb.heap_extends.trans
          (e_1427.trans (ev_es.heap_extends.trans (ev_saf.heap_extends.trans
            (ev_mk.heap_extends.trans (ev_mod.heap_extends.trans
              (ev_fa.heap_extends.trans (ev_tele.heap_extends.trans
                (e_1736.trans ev_rsl.heap_extends))))))))))))
    have hsub_mc : ∀ cl ∈ cs_mc, cl ∈ calls := fun cl hcl =>
      hsub_chk cl (by rw [hc]; simp [hcl])
    have hbp := Bytes.repAddressRef_heapMono₂ Core.addrTy e_to_1688 hbp_m
    exact modeled_ctor_slots_scoped hnc ind.ctors.size 0 (by omega) rfl rfl hsub_mc hbp ev_mc j
      (Nat.zero_le _) hj

/-- **The reading of a constructor at a loaded slot of member `i`**, over the run's store: closed,
with its level parameters defined and no free variable (the loop validated its scope), its stored
index, level count and parameter count pinned to the slot and the member's, its counts below
`2 ^ 56`, and `Reads` at its projection address. -/
theorem ctorSlot_reads_at (ht : t.check = .ok ()) (hbound : Bounded calls)
    (hS : LoadedReads.RunStore calls E₀) (hrec : ModeledBlockRecord E₀ B cb ms)
    {i : Nat} {ind : Ixon.Inductive} (hmem : ms[i]? = some (.indc ind))
    (hi : i < 72057594037927936)
    {b : Bytes.Address} (hb : Core.ixAddr b = B) (hlv : ind.lvls.toNat < 4294967296)
    (hnp : ind.params.toNat < 72057594037927936) {j : Nat} (hj : j < ind.ctors.size)
    (hjb : j < 72057594037927936)
    (hslot : CtorSlotScoped calls b ((i : Nat) : F) j ind.lvls.toNat ind.params.toNat) :
    ∃ (ct : Ixon.Constructor) (ty₀ : Ix.Kernel.Expr .anon),
      ind.ctors[j]? = some ct ∧ ct.cidx.toNat = j ∧ ct.lvls.toNat = ind.lvls.toNat ∧
      ct.params.toNat = ind.params.toNat ∧
      ct.params.toNat < 72057594037927936 ∧ ct.fields.toNat < 72057594037927936 ∧
      (exprReader t (fun x => E₀.blobs.get? x) cb id (blockSelf t B ms)).read ct.typ =
        .ok ty₀ ∧
      ty₀.looseBVarsBounded 0 = true ∧
      ty₀.allLevelParamsDefined (List.range ct.lvls.toNat) = true ∧ ty₀.hasFvar = false ∧
      Reads t E₀ (Core.cprjAddr B i j)
        (.ctorInfo ⟨Core.keyOf t (Core.cprjAddr B i j), List.range ct.lvls.toNat, ty₀⟩
          ct.params.toNat ct.fields.toNat) := by
  obtain ⟨bp, ptr, h, h', m₁, m₂, cs, cs₂, nl, ty, pb, mi, sl, np, nf, us, v₂, ev, hsub, hbp, hld,
    hsl, hnl, hnpv, hext₁, evS, hmemS⟩ := hslot
  have hbcs : Bounded cs := RomBound.bounded_mono hbound hsub
  subst hb
  have hrecB : Ix.Cert.recordAt E₀ (Core.ixAddr b) = some cb :=
    (hS.recordOf_eq_recordAt _).symm.trans hrec.record
  have hz : ZMod.val ((i : Nat) : F) = i :=
    ZMod.val_natCast_of_lt (by unfold Aiur.Library.U32.Goldilocks.modulus; omega)
  have hjv : ZMod.val ((j : Nat) : F) = j :=
    ZMod.val_natCast_of_lt (by unfold Aiur.Library.U32.Goldilocks.modulus; omega)
  obtain ⟨-, -, -, blkBytes, cb', ms', ind', ct', blobs, v, hhB, haB, hexB, -, hcb', hms', hct',
    -, hldv, hraw⟩ := L1.get_ci_cprj_spec hbcs hbp ev
  have hcb_eq : cb' = cb := hS.record_eq hrecB (Core.hashed_mono hsub hhB) haB hexB
  subst cb'
  have hms_eq : ms' = ms := Ixon.ConstantInfo.muts.inj (hcb'.symm.trans hrec.muts)
  subst ms'
  rw [hz] at hms'
  have hind_eq : ind' = ind := by
    rw [Array.getElem?_toList, hmem] at hms'
    exact (Ixon.MutConst.indc.inj (Option.some.inj hms')).symm
  subst ind'
  rw [hjv] at hct'
  have hctj : ind.ctors[j]? = some ct' := by
    rw [← Array.getElem?_toList]
    exact hct'
  have hvv : v = .construct Core.kciEnum "Ctor" [nl, ty, pb, mi, sl, np, nf, us] :=
    Except.ok.inj (hldv.symm.trans hld)
  obtain ⟨hclv, hccidx, hcpar, hcf, -, tyPtr, blkPtr, b', -, -, hv, rty⟩ := hraw
  rw [hv] at hvv
  injection hvv with _ _ hargs
  injection hargs with hl1 hargs
  injection hargs with ht1 hargs
  injection hargs with _ hargs
  injection hargs with _ hargs
  injection hargs with hc1 hargs
  injection hargs with hp1 _
  have hlvls : ct'.lvls.toNat = ind.lvls.toNat :=
    Decl.nat_eq_of_field_eq_bounded (by omega) (by omega) (hl1.trans hnl)
  have hcidx : ct'.cidx.toNat = j :=
    Decl.nat_eq_of_field_eq_bounded (by omega) (by omega) (hc1.trans hsl)
  have hpar : ct'.params.toNat = ind.params.toNat :=
    Decl.nat_eq_of_field_eq_bounded (by omega) (by omega) (hp1.trans hnpv)
  have hproj : recordOf E₀ (ctorAddr (Core.ixAddr b) (ZMod.val ((i : Nat) : F))
      (ZMod.val ((j : Nat) : F))) =
      some (constructorProjection (Core.ixAddr b) (ZMod.val ((i : Nat) : F))
        (ZMod.val ((j : Nat) : F))) := by
    rw [hz, hjv]
    exact hrec.ctors i ind hmem j hj
  have hcidxAll : ∀ (ms₁ : Array Ixon.MutConst) (ind₁ : Ixon.Inductive) (ct : Ixon.Constructor),
      cb.info = .muts ms₁ → ms₁[ZMod.val ((i : Nat) : F)]? = some (.indc ind₁) →
      ind₁.ctors[ZMod.val ((j : Nat) : F)]? = some ct →
      ct.cidx.toNat = ZMod.val ((j : Nat) : F) := by
    intro ms₁ ind₁ ct hcb hm hc
    have hms₁ : ms₁ = ms := Ixon.ConstantInfo.muts.inj (hcb.symm.trans hrec.muts)
    subst ms₁
    rw [hz, hmem] at hm
    have hi₁ : ind₁ = ind := (Ixon.MutConst.indc.inj (Option.some.inj hm)).symm
    subst ind₁
    rw [hjv] at hc ⊢
    have hct : ct = ct' := Option.some.inj (hc.symm.trans hctj)
    subst ct
    exact hcidx
  obtain ⟨ms₂, ind₂, ct₂, ty₀, v₃, hcbm, hm₂, hc₂, -, hty, hreads, -⟩ :=
    LoadedReads.get_ci_cprj_reads ht hS hbcs hsub hbp ev hrecB hrec.logic hcidxAll hproj
  have hms₂ : ms₂ = ms := Ixon.ConstantInfo.muts.inj (hcbm.symm.trans hrec.muts)
  subst ms₂
  rw [hz, hmem] at hm₂
  have hi₂ : ind₂ = ind := (Ixon.MutConst.indc.inj (Option.some.inj hm₂)).symm
  subst ind₂
  rw [hjv] at hc₂ hreads
  have hct₂ : ct₂ = ct' := Option.some.inj (hc₂.symm.trans hctj)
  subst ct₂
  rw [hz] at hreads
  -- the scope check of the loaded type
  rw [← ht1] at evS hmemS
  obtain ⟨-, hlbb, hdef⟩ := Assembly.validate_expr_well_scoped_spec
    (cx := readCtx t (fun x => E₀.blobs.get? x)) (self := blockSelf t (Core.ixAddr b) ms)
    hbound hlv rty hext₁ hty evS hmemS
  refine ⟨ct', ty₀, hctj, hcidx, hlvls, hpar, hcpar, hcf, hty, hlbb, ?_,
    Assembly.memberReader_read_noFvar hty, hreads⟩
  rw [hlvls]
  exact hdef

end Member

/-! ## Every member of the walked block -/

section Block

variable {t : Ix.Kernel.RoleTable} {calls : List (Call F)} {E₀ E : Ixon.Env}
  {bAddr B : _root_.Address} {cb : Ixon.Constant} {ms : Array Ixon.MutConst} {n : Nat}

/-- **The reading of every member of the walked block**, over the step's store (the one over the
run's store: the run's blobs are the step's), closed, with the member's counts below `2 ^ 56`,
and `Reads` over the run's store at the member's projection address. -/
theorem point_member_reads (ht : t.check = .ok ()) (hS : LoadedReads.RunStore calls E₀)
    (hst : StepStore calls t E₀ E) (hrec : ModeledBlockRecord E₀ B cb ms)
    (hchk : ∀ k < ms.size, MutsMemberCheckedAtFullAt calls bAddr t B ms k n)
    {i : Nat} {ind : Ixon.Inductive} (hmem : ms[i]? = some (.indc ind)) :
    ∃ ty₀ : Ix.Kernel.Expr .anon,
      blockRead t E B cb ms ind.typ = .ok ty₀ ∧
      (exprReader t (fun x => E₀.blobs.get? x) cb id (blockSelf t B ms)).read ind.typ =
        .ok ty₀ ∧
      ty₀.looseBVarsBounded 0 = true ∧
      ty₀.allLevelParamsDefined (List.range ind.lvls.toNat) = true ∧ ty₀.hasFvar = false ∧
      ind.params.toNat < 2 ^ 56 ∧ ind.indices.toNat < 2 ^ 56 ∧ ind.ctors.size < 2 ^ 56 ∧
      ∀ caps : Ix.Kernel.IndCaps .anon, Reads t E₀ (Core.iprjAddr B i)
        (.indInfo ⟨Core.keyOf t (Core.iprjAddr B i), List.range ind.lvls.toNat, ty₀⟩ caps) := by
  have hbound : Bounded calls := (hst.good Ix.Kernel.Env.empty none).2
  obtain ⟨ty₀, hty, hlbb, hdef, hfv, -, hnp, hni, hnc, hreads⟩ :=
    member_reads_at ht hbound hS hrec hmem (hchk i (Array.getElem?_eq_some_iff.mp hmem).1)
  exact ⟨ty₀, ReaderReads.exprReader_mono (fun x b hb => hst.runBlob x b hb) hty, hty, hlbb,
    hdef, hfv, by omega, by omega, by omega, hreads⟩

/-- **The reading of every constructor of every member of the walked block**, over the step's
store (the one over the run's store), closed, with its stored index its position, its level and
parameter counts the member's, its counts below `2 ^ 56`, and `Reads` over the run's store at its
projection address. -/
theorem point_ctor_reads (ht : t.check = .ok ()) (hS : LoadedReads.RunStore calls E₀)
    (hst : StepStore calls t E₀ E) (hrec : ModeledBlockRecord E₀ B cb ms)
    (hchk : ∀ k < ms.size, MutsMemberCheckedAtFullAt calls bAddr t B ms k n)
    {i : Nat} {ind : Ixon.Inductive} (hmem : ms[i]? = some (.indc ind))
    {j : Nat} (hj : j < ind.ctors.size) :
    ∃ (ct : Ixon.Constructor) (cty₀ : Ix.Kernel.Expr .anon),
      ind.ctors[j]? = some ct ∧ ct.cidx.toNat = j ∧ ct.lvls.toNat = ind.lvls.toNat ∧
      ct.params.toNat = ind.params.toNat ∧
      ct.params.toNat < 2 ^ 56 ∧ ct.fields.toNat < 2 ^ 56 ∧
      blockRead t E B cb ms ct.typ = .ok cty₀ ∧
      (exprReader t (fun x => E₀.blobs.get? x) cb id (blockSelf t B ms)).read ct.typ =
        .ok cty₀ ∧
      cty₀.looseBVarsBounded 0 = true ∧
      cty₀.allLevelParamsDefined (List.range ct.lvls.toNat) = true ∧ cty₀.hasFvar = false ∧
      Reads t E₀ (Core.cprjAddr B i j)
        (.ctorInfo ⟨Core.keyOf t (Core.cprjAddr B i j), List.range ct.lvls.toNat, cty₀⟩
          ct.params.toNat ct.fields.toNat) := by
  have hbound : Bounded calls := (hst.good Ix.Kernel.Env.empty none).2
  have hchki := hchk i (Array.getElem?_eq_some_iff.mp hmem).1
  have hi39 := member_idx_lt hbound hmem hchki
  obtain ⟨b, hb, hlv, hnp, hnc, hslots⟩ := ctorSlots_at hbound hS hrec hmem hchki
  obtain ⟨ct, cty₀, hct, hcidx, hlvls, hpar, hcp, hcf, hty, hlbb, hdef, hfv, hreads⟩ :=
    ctorSlot_reads_at ht hbound hS hrec hmem (by omega) hb hlv hnp hj (by omega) (hslots j hj)
  exact ⟨ct, cty₀, hct, hcidx, hlvls, hpar, by omega, by omega,
    ReaderReads.exprReader_mono (fun x b hb => hst.runBlob x b hb) hty, hty, hlbb, hdef, hfv,
    hreads⟩

end Block

/-! ## The keys of the block are distinct -/

section Keys

variable {t : Ix.Kernel.RoleTable} {E₀ : Ixon.Env} {B : _root_.Address} {cb : Ixon.Constant}
  {ms : Array Ixon.MutConst}

/-- **Two members' projection addresses are one only at one member**, the indices below
`2 ^ 64`: the run's store holds each member's projection at its address. -/
theorem iprjAddr_inj_member (hrec : ModeledBlockRecord E₀ B cb ms) {i i' : Nat}
    {ind ind' : Ixon.Inductive} (hi : ms[i]? = some (.indc ind))
    (hi' : ms[i']? = some (.indc ind')) (h64 : i < UInt64.size) (h64' : i' < UInt64.size)
    (he : Core.iprjAddr B i = Core.iprjAddr B i') : i = i' := by
  have h1 := hrec.former i ind hi
  rw [he, hrec.former i' ind' hi'] at h1
  have h2 : Ixon.ConstantInfo.iPrj ⟨i'.toUInt64, B⟩ = .iPrj ⟨i.toUInt64, B⟩ :=
    congrArg Ixon.Constant.info (Option.some.inj h1)
  injection h2 with h3
  injection h3 with h4 _
  exact (toUInt64_inj_of_lt h64' h64 h4).symm

/-- **Two constructor slots' projection addresses are one only at one slot**, the indices below
`2 ^ 64`. -/
theorem cprjAddr_inj_member (hrec : ModeledBlockRecord E₀ B cb ms) {i i' j j' : Nat}
    {ind ind' : Ixon.Inductive} (hi : ms[i]? = some (.indc ind))
    (hi' : ms[i']? = some (.indc ind')) (hj : j < ind.ctors.size) (hj' : j' < ind'.ctors.size)
    (h64 : i < UInt64.size) (h64' : i' < UInt64.size) (hj64 : j < UInt64.size)
    (hj64' : j' < UInt64.size) (he : Core.cprjAddr B i j = Core.cprjAddr B i' j') :
    i = i' ∧ j = j' := by
  have h1 := hrec.ctors i ind hi j hj
  rw [he, hrec.ctors i' ind' hi' j' hj'] at h1
  have h2 : Ixon.ConstantInfo.cPrj ⟨i'.toUInt64, j'.toUInt64, B⟩ =
      .cPrj ⟨i.toUInt64, j.toUInt64, B⟩ :=
    congrArg Ixon.Constant.info (Option.some.inj h1)
  injection h2 with h3
  injection h3 with h4 h5 _
  exact ⟨(toUInt64_inj_of_lt h64' h64 h4).symm, (toUInt64_inj_of_lt hj64' hj64 h5).symm⟩

/-- **A member's projection address is no constructor slot's.** -/
theorem iprj_ne_cprj_member (hrec : ModeledBlockRecord E₀ B cb ms) {i i' j : Nat}
    {ind ind' : Ixon.Inductive} (hi : ms[i]? = some (.indc ind))
    (hi' : ms[i']? = some (.indc ind')) (hj : j < ind'.ctors.size) :
    Core.iprjAddr B i ≠ Core.cprjAddr B i' j := by
  intro he
  have h1 := hrec.former i ind hi
  rw [he, hrec.ctors i' ind' hi' j hj] at h1
  have h2 : Ixon.ConstantInfo.cPrj ⟨i'.toUInt64, j.toUInt64, B⟩ = .iPrj ⟨i.toUInt64, B⟩ :=
    congrArg Ixon.Constant.info (Option.some.inj h1)
  cases h2

/-- **The block's keys are pairwise distinct**: members' keys among themselves, constructor
slots' keys among themselves (slot indices below `2 ^ 64`), and a member's key against a slot's.
Member indices are below `2 ^ 64`: the block has fewer than `2 ^ 39` members. -/
theorem point_keys_distinct (ht : t.check = .ok ()) (hrec : ModeledBlockRecord E₀ B cb ms)
    (hsize : ms.size < 2 ^ 39) :
    (∀ (i i' : Nat) (ind ind' : Ixon.Inductive), ms[i]? = some (.indc ind) →
      ms[i']? = some (.indc ind') →
      Core.keyOf t (Core.iprjAddr B i) = Core.keyOf t (Core.iprjAddr B i') → i = i') ∧
    (∀ (i i' j j' : Nat) (ind ind' : Ixon.Inductive), ms[i]? = some (.indc ind) →
      ms[i']? = some (.indc ind') → j < ind.ctors.size → j' < ind'.ctors.size →
      j < UInt64.size → j' < UInt64.size →
      Core.keyOf t (Core.cprjAddr B i j) = Core.keyOf t (Core.cprjAddr B i' j') →
      i = i' ∧ j = j') ∧
    (∀ (i i' j : Nat) (ind ind' : Ixon.Inductive), ms[i]? = some (.indc ind) →
      ms[i']? = some (.indc ind') → j < ind'.ctors.size →
      Core.keyOf t (Core.iprjAddr B i) ≠ Core.keyOf t (Core.cprjAddr B i' j)) := by
  have htwf : t.wf = true := by
    unfold Ix.Kernel.RoleTable.wf
    rw [ht]
    rfl
  have h64 : ∀ {i : Nat} {m : Ixon.MutConst}, ms[i]? = some m → i < UInt64.size := by
    intro i m hm
    have hk := (Array.getElem?_eq_some_iff.mp hm).1
    have e : UInt64.size = 18446744073709551616 := rfl
    omega
  refine ⟨fun i i' ind ind' hi hi' hk => ?_, fun i i' j j' ind ind' hi hi' hj hj' hj64 hj64' hk => ?_,
    fun i i' j ind ind' hi hi' hj hk => ?_⟩
  · exact iprjAddr_inj_member hrec hi hi' (h64 hi) (h64 hi') (Core.keyOf_inj htwf hk)
  · exact cprjAddr_inj_member hrec hi hi' hj hj' (h64 hi) (h64 hi') hj64 hj64'
      (Core.keyOf_inj htwf hk)
  · exact iprj_ne_cprj_member hrec hi hi' hj (Core.keyOf_inj htwf hk)

end Keys

end IxVM.Refinement.Typing
