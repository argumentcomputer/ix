import IxVMRefinement.Assembly.NativeBlockFormer
import IxVMRefinement.Assembly.ClaimsL1L6
import IxVMRefinement.Assembly.ReadBare
import IxVMRefinement.StatementRel.LoadedReadsWalked
import IxVMRefinement.Core.CallHeaps
import IxVMRefinement.Assembly.NativeScopeInputs
import IxVMRefinement.StatementRel.ReadsMono

/-! # The readings of a native block and its recognition

The walked check of the type former of a block of one inductive loads the former and, in the
`Induct` arm, loads every constructor of the block in order (`check_inductive_shape_ctors` on the
native route, `check_modeled_ctors` on the modeled one); each constructor load is pinned to its
slot, the block's level count and its parameter count. From these loads:

* `ctorSlots_of_member`: every constructor slot has its load, on either route;
* `former_reads`, `ctorSlot_reads`: the readings of the former and of each constructor over the
  run's store, with the constructor's stored index, level count and parameter count;
* `blockReads_of_member`: the declared block (former, then constructors) with its readings, no
  basis pin, and the declaration layer's non-derived keys;
* `blockReads_shape`: every block of readings at the unit's addresses has that shape;
* `nativeParts_of_member`: the block is recognised without its recursor at a former declared at
  its telescope, and its constructors' names are distinct.

The run-side facts are read at a bounded derivation (`Bounded calls`), as every load
specification of the record layer is. -/

namespace IxVM.Refinement.Typing

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library
open IxVM (F)
open IxVM.Consistency
open Ix.Kernel (ConstantInfo ConstantVal)

set_option maxHeartbeats 1600000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

universe u

/-! ## The case of the unit -/

/-- **The unit's record**: the block at `B` has one member, the inductive `ind`, is in Lean's
logic, and the run's store holds its member and constructor projection records. -/
structure BlockUnitRecord (E₀ : Ixon.Env) (B : _root_.Address) (cb : Ixon.Constant)
    (ind : Ixon.Inductive) : Prop where
  record : recordOf E₀ B = some cb
  muts : cb.info = .muts #[.indc ind]
  logic : InLogic cb
  former : recordOf E₀ (memberAddr B 0 (.indc ind)) = some (memberProjection B 0 (.indc ind))
  ctors : ∀ j < ind.ctors.size, recordOf E₀ (ctorAddr B 0 j) = some (constructorProjection B 0 j)

/-- **The native case**: every observation of the circuit's dispatch on the block in the run
answers `0` (not mutual, not nested). -/
def NativeRouteAt (calls : List (Call F)) (B : _root_.Address) : Prop :=
  ∀ (bp r : SourceValue F) (h h' : Heap F) (cs : List (Call F)) (b : Bytes.Address),
    ObsFn Core.W "KernelModeled::block_is_modeled" [bp] h r h' cs →
    (∀ cl ∈ cs, cl ∈ calls) → Bytes.RepAddressRef Core.addrTy h b bp →
    Core.ixAddr b = B → r = .field 0

/-- **The former is declared at its telescope**: the reading of its type is a syntactic
telescope of the parameters and indices ending in a sort. -/
def FormerAtTele (t : Ix.Kernel.RoleTable) (E₀ : Ixon.Env) (B : _root_.Address)
    (cb : Ixon.Constant) (ind : Ixon.Inductive) : Prop :=
  ∀ ty₀, (exprReader t (fun x => E₀.blobs.get? x) cb id (blockSelf t B #[.indc ind])).read
      ind.typ = .ok ty₀ →
    ∃ bs s, ty₀.stripPis (ind.params.toNat + ind.indices.toNat) = some (bs, .sort s)

/-- **The declared block**: the reading of the former, then the readings of the constructors in
order, each at its constant address. -/
def BlockReadings (t : Ix.Kernel.RoleTable) (E₀ : Ixon.Env) (B : _root_.Address)
    (ind : Ixon.Inductive) (blk : List (ConstantInfo .anon)) : Prop :=
  ∃ fr cs, blk = fr :: cs ∧ Reads t E₀ (memberAddr B 0 (.indc ind)) fr ∧
    cs.length = ind.ctors.size ∧ ∀ j c, cs[j]? = some c → Reads t E₀ (ctorAddr B 0 j) c

/-! ## Small facts -/

/-- A list with an element at every index below `n`, chosen from a relation. -/
theorem exists_list_of_forall {α : Type} {P : Nat → α → Prop} :
    ∀ n : Nat, (∀ j < n, ∃ x, P j x) →
      ∃ l : List α, l.length = n ∧ ∀ j x, l[j]? = some x → P j x
  | 0, _ => ⟨[], rfl, fun j x h => by simp at h⟩
  | n + 1, h => by
    obtain ⟨l, hl, hP⟩ := exists_list_of_forall n (fun j hj => h j (Nat.lt_succ_of_lt hj))
    obtain ⟨x, hx⟩ := h n (Nat.lt_succ_self n)
    refine ⟨l ++ [x], by simp [hl], fun j y hy => ?_⟩
    by_cases hj : j < l.length
    · rw [List.getElem?_append_left hj] at hy
      exact hP j y hy
    · rw [List.getElem?_append_right (Nat.le_of_not_lt hj)] at hy
      have hj' : j - l.length = 0 := by
        cases hk : j - l.length with
        | zero => rfl
        | succ k => rw [hk] at hy; simp at hy
      have hjn : j = n := by omega
      rw [hj'] at hy
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hy
      subst hy hjn
      exact hx

/-- The names of a list whose `j`-th element has the name `f j`, for `f` injective below the
length, are distinct. -/
theorem nodup_names_of_index {l : List (ConstantInfo .anon)} {f : Nat → Core.KKey}
    (hf : ∀ j x, l[j]? = some x → x.name = f j)
    (hinj : ∀ j j', j < l.length → j' < l.length → f j = f j' → j = j') :
    (l.map (·.name)).Nodup := by
  have heq : l.map (·.name) = (List.range l.length).map f := by
    apply List.ext_getElem?
    intro j
    rw [List.getElem?_map, List.getElem?_map]
    by_cases hj : j < l.length
    · rw [List.getElem?_range hj]
      obtain ⟨x, hx⟩ : ∃ x, l[j]? = some x := ⟨l[j], List.getElem?_eq_getElem hj⟩
      rw [hx]
      simp [hf j x hx]
    · rw [List.getElem?_eq_none (Nat.le_of_not_lt hj),
        List.getElem?_eq_none (by simpa using Nat.le_of_not_lt hj)]
      rfl
  rw [heq]
  exact List.Nodup.map_on (fun a ha b hb e => hinj a b (List.mem_range.mp ha)
    (List.mem_range.mp hb) e) List.nodup_range

/-- The key of an address is not derived. -/
theorem nonAux_keyOf (t : Ix.Kernel.RoleTable) (x : _root_.Address) :
    Decl.NonAuxKey (keyOf t x) :=
  Decl.isBaseKey_iff_nonAuxKey.mp (Decl.isBaseKey_keyOf t x)

/-- **A reading of a block member's expression names only non-derived keys.** -/
theorem read_refsIn_nonAux {t : Ix.Kernel.RoleTable} {blob : _root_.Address → Option ByteArray}
    {src : Ixon.Constant} {B : _root_.Address} {ms : Array Ixon.MutConst} {ie : Ixon.Expr}
    {e : Ix.Kernel.Expr .anon}
    (h : (exprReader t blob src id (blockSelf t B ms)).read ie = .ok e) :
    e.RefsIn Decl.NonAuxKey := by
  have hself : ∀ i m k, blockSelf t B ms i = some m → m = .ok k → Assembly.NonAuxKey k := by
    intro i m k hs hm
    unfold blockSelf at hs
    cases hmi : ms[i]? with
    | none => rw [hmi] at hs; cases hs
    | some m₀ =>
      rw [hmi] at hs
      have h2 : (Except.ok (keyOf t (memberAddr B i m₀)) :
          Ix.Kernel.Reader.ReadM (Ix.Kernel.Key .anon)) = m := Option.some.inj hs
      rw [hm] at h2
      rw [← Except.ok.inj h2]
      exact nonAux_keyOf t _
  exact Assembly.memberReader_read_refsIn_nonAux (cx := readCtx t blob)
    (fun ref k hk => Ix.Cert.ReaderUnits.bindingsOf_keyed _ t ref k hk) hself h

/-- A constant that is a recursor. -/
def isRecInfo : ConstantInfo .anon → Bool
  | .recInfo .. => true
  | _ => false

theorem canonEqFast_recInfo {x : ConstantInfo .anon} {y : ConstantInfo .anon}
    (hy : isRecInfo y = true) (h : Ix.Kernel.ConstantInfo.canonEqFast x y = true) :
    isRecInfo x = true := by
  cases y <;> simp [isRecInfo] at hy
  cases x <;> simp_all [Ix.Kernel.ConstantInfo.canonEqFast, isRecInfo]

theorem canonEqListFast_recInfo :
    ∀ {xs ys : List (ConstantInfo .anon)}, Ix.Kernel.canonEqListFast xs ys = true →
      ys.any isRecInfo = true → xs.any isRecInfo = true
  | [], [], _, hy => by simp at hy
  | [], _ :: _, h, _ => by simp [Ix.Kernel.canonEqListFast] at h
  | _ :: _, [], h, _ => by simp [Ix.Kernel.canonEqListFast] at h
  | x :: xs, y :: ys, h, hy => by
    simp only [Ix.Kernel.canonEqListFast, Bool.and_eq_true] at h
    simp only [List.any_cons, Bool.or_eq_true] at hy ⊢
    rcases hy with hy | hy
    · exact Or.inl (canonEqFast_recInfo hy h.1)
    · exact Or.inr (canonEqListFast_recInfo h.2 hy)

/-- **A block with no recursor is no pinned basis block**: every pinned block ends with its
recursor, and the canonical comparison keeps each constant's kind. -/
theorem basisPinHit_none_of_noRec {blk : List (ConstantInfo .anon)}
    (h : blk.any isRecInfo = false) : Ix.Kernel.basisPinHit blk = none := by
  unfold Ix.Kernel.basisPinHit
  cases hf : ([Ix.Kernel.BasisKind.eqK, .natK, .punitK, .emptyK, .falseK].find? fun k =>
      (k.decls (md := .anon)).map (·.name) == blk.map (·.name)) with
  | none => rfl
  | some k =>
    have hk := List.mem_of_find?_eq_some hf
    have hrec : (k.decls (md := .anon)).any isRecInfo = true := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> rfl
    have hne : Ix.Kernel.canonEqList blk k.decls = false := by
      rw [Ix.Kernel.canonEqList_eq_canonEqListFast]
      cases hc : Ix.Kernel.canonEqListFast blk k.decls with
      | false => rfl
      | true =>
        have := canonEqListFast_recInfo hc hrec
        rw [h] at this
        exact absurd this (by decide)
    simp [Option.filter, hne]

/-- **The declaration layer's non-derived keys for a block that is no pinned basis block.** -/
theorem declNonAux_indDecl_of {blk : List (ConstantInfo .anon)} {nP : Nat}
    (hpin : Ix.Kernel.basisPinHit blk = none)
    (hci : ∀ ci ∈ blk, Decl.ConstantInfoNonAux ci) (hnd : (blk.map (·.name)).Nodup) :
    Decl.DeclNonAux (.indDecl blk nP) := by
  have hinst : IxVM.Consistency.installs (.indDecl blk nP) = blk := by
    simp [IxVM.Consistency.installs, hpin]
  exact ⟨by rw [hinst]; exact hci, by rw [hinst]; exact hnd⟩

/-! ## The constructor loads of the two loops -/

/-- **A constructor slot the circuit loaded**: a `get_ci_cprj` run in `calls` on the block `b` at
member `i` and slot `j`, whose `Ctor` value carries the slot, the level count and the parameter
count the loop pinned. -/
def CtorSlotLoaded (calls : List (Call F)) (b : Bytes.Address) (i : F) (j levels params : Nat) :
    Prop :=
  ∃ (bp ptr : SourceValue F) (h h' : Heap F) (cs : List (Call F))
    (nl ty pb mi sl np nf us : SourceValue F),
    ObsFn Core.W "Ingress::get_ci_cprj" [bp, .field i, .field (j : F)] h ptr h' cs ∧
    (∀ cl ∈ cs, cl ∈ calls) ∧ Bytes.RepAddressRef Core.addrTy h b bp ∧
    loadValue h' ptr = .ok (.construct Core.kciEnum "Ctor" [nl, ty, pb, mi, sl, np, nf, us]) ∧
    sl = .field (j : F) ∧ nl = .field (levels : F) ∧ np = .field (params : F)

/-- **The native constructor loop loads every slot from its start.** -/
theorem native_ctor_slots {b : Bytes.Address} {n levels params : Nat} {i : F}
    (hn : n < 72057594037927936) {calls : List (Call F)} :
    ∀ (m k : Nat) {rc former np ni nl blockArg sortLevel safety r : SourceValue F}
      {h h' : Heap F} {cs : List (Call F)}, m + k = n →
      np = .field (params : F) → nl = .field (levels : F) →
      (∀ cl ∈ cs, cl ∈ calls) →
      Bytes.RepAddressRef Core.addrTy h b blockArg →
      ObsFn Core.W "KernelCheck::check_inductive_shape_ctors"
        [rc, former, np, ni, .field (n : F), nl, blockArg, .field i, sortLevel, safety,
          .field (k : F)] h r h' cs →
      ∀ j, k ≤ j → j < n → CtorSlotLoaded calls b i j levels params := by
  intro m
  induction m with
  | zero =>
    intro k rc former np ni nl blockArg sortLevel safety r h h' cs hmk _ _ _ _ _ j hkj hjn
    omega
  | succ m ih =>
    intro k rc former np ni nl blockArg sortLevel safety r h h' cs hmk hnp hnl hsub hbp ev
      j hkj hjn
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
        (x_c_unsafe := cus) (m725 := nextHeap) (cs765 := nextCalls) (v778 := nextIndex)
        (ev49 := loaded) (ld43 := tag) (heq233 := slotChecked) (heq261 := levelsChecked)
        (heq289 := paramsChecked) (op862 := addition) (ev767 := nextRun)
        (hc864 := allCalls) .. =>
      by_cases hjk : j = k
      · subst hjk
        exact ⟨blockArg, ptr, h, after, loadCalls, cnl, cty, cblk, cmi, csl, cnp, cnf, cus,
          loaded, fun cl hcl => hsub cl (by rw [allCalls]; simp [hcl]), hbp, tag, slotChecked,
          levelsChecked.trans hnl, paramsChecked.trans hnp⟩
      · have added := Decl.evalBinOp_add_nat k 1 addition
        subst nextIndex
        have nextMember : (⟨"KernelCheck::check_inductive_shape_ctors",
            [rc, former, np, ni, .field (n : F), nl, blockArg, .field i, sortLevel, safety,
              .field ((k + 1 : Nat) : F)], nextHeap⟩ : Call F) ∈ cs := by
          rw [allCalls]
          simp
        have nextBlock := Bytes.repAddressRef_heapMono₂ Core.addrTy
          (ev.call_heap_bounds nextMember).1 hbp
        exact ih (k + 1) (by omega) hnp hnl
          (fun cl hcl => hsub cl (by rw [allCalls]; simp [hcl])) nextBlock nextRun j
          (by omega) hjn

/-- **The modeled constructor loop loads every slot from its start.** -/
theorem modeled_ctor_slots {b : Bytes.Address} {n levels params : Nat} {i : F}
    (hn : n < 72057594037927936) {calls : List (Call F)} :
    ∀ (m k : Nat) {rc np ni nl blockArg safety r : SourceValue F}
      {h h' : Heap F} {cs : List (Call F)}, m + k = n →
      np = .field (params : F) → nl = .field (levels : F) →
      (∀ cl ∈ cs, cl ∈ calls) →
      Bytes.RepAddressRef Core.addrTy h b blockArg →
      ObsFn Core.W "KernelCheck::check_modeled_ctors"
        [rc, np, ni, .field (n : F), nl, blockArg, .field i, safety, .field (k : F)] h r h' cs →
      ∀ j, k ≤ j → j < n → CtorSlotLoaded calls b i j levels params := by
  intro m
  induction m with
  | zero =>
    intro k rc np ni nl blockArg safety r h h' cs hmk _ _ _ _ _ j hkj hjn
    omega
  | succ m ih =>
    intro k rc np ni nl blockArg safety r h h' cs hmk hnp hnl hsub hbp ev j hkj hjn
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
        (x_c_unsafe := cus) (m500 := nextHeap) (cs540 := nextCalls) (v551 := nextIndex)
        (ev49 := loaded) (ld43 := tag) (heq233 := slotChecked) (heq261 := levelsChecked)
        (heq289 := paramsChecked) (op621 := addition) (ev542 := nextRun)
        (hc623 := allCalls) .. =>
      by_cases hjk : j = k
      · subst hjk
        exact ⟨blockArg, ptr, h, after, loadCalls, cnl, cty, cblk, cmi, csl, cnp, cnf, cus,
          loaded, fun cl hcl => hsub cl (by rw [allCalls]; simp [hcl]), hbp, tag, slotChecked,
          levelsChecked.trans hnl, paramsChecked.trans hnp⟩
      · have added := Decl.evalBinOp_add_nat k 1 addition
        subst nextIndex
        have nextMember : (⟨"KernelCheck::check_modeled_ctors",
            [rc, np, ni, .field (n : F), nl, blockArg, .field i, safety,
              .field ((k + 1 : Nat) : F)], nextHeap⟩ : Call F) ∈ cs := by
          rw [allCalls]
          simp
        have nextBlock := Bytes.repAddressRef_heapMono₂ Core.addrTy
          (ev.call_heap_bounds nextMember).1 hbp
        exact ih (k + 1) (by omega) hnp hnl
          (fun cl hcl => hsub cl (by rw [allCalls]; simp [hcl])) nextBlock nextRun j
          (by omega) hjn

section Member

variable {t : Ix.Kernel.RoleTable} {calls : List (Call F)} {E₀ : Ixon.Env}
  {bAddr B : _root_.Address} {cb : Ixon.Constant} {ind : Ixon.Inductive} {n : Nat}

private theorem idx_zero (B : _root_.Address) :
    (⟨(0 : Nat).toUInt64, B⟩ : Ixon.InductiveProj).idx.toNat = 0 := by
  show ((0 : Nat).toUInt64).toNat = 0
  decide

/-- **Every constructor slot of the block has its load**, on either route of the `Induct` arm,
with the block's level and parameter counts and their bounds. -/
theorem ctorSlots_of_member (hbound : Bounded calls) (hS : LoadedReads.RunStore calls E₀)
    (hrec : BlockUnitRecord E₀ B cb ind)
    (hchk : MutsMemberCheckedAtFullAt calls bAddr t B #[.indc ind] 0 n) :
    ∃ b : Bytes.Address, Core.ixAddr b = B ∧ ind.lvls.toNat < 4294967296 ∧
      ind.params.toNat < 72057594037927936 ∧ ind.ctors.size < 72057594037927936 ∧
      ∀ j < ind.ctors.size,
        CtorSlotLoaded calls b ((0 : Nat) : F) j ind.lvls.toNat ind.params.toNat := by
  have hchkA := mutsMemberAt_checkedAt (mc := .indc ind) hbound hchk rfl
  obtain ⟨_, _, m_chk, _, rc, ap, ptr, v, r_chk, cs_ld, cs_chk, bytes, E_ld,
    _, _, _, _, hhash, hblake, hload_ld, hL1, hsub_ld, hld, ev_chk, _, hsub_chk⟩ :=
    Assembly.checkedAtFull_loadedL1 hbound ⟨n, hchkA⟩
  have hrecP : Ix.Cert.recordAt E₀ (memberAddr B 0 (.indc ind)) =
      some (memberProjection B 0 (.indc ind)) :=
    (hS.recordOf_eq_recordAt _).symm.trans hrec.former
  have hrecB : Ix.Cert.recordAt E₀ B = some cb :=
    (hS.recordOf_eq_recordAt _).symm.trans hrec.record
  obtain ⟨-, -, v', hld', hraw⟩ := LoadedReads.loadedL1_record hS hsub_ld hhash hblake hL1 hrecP
  have hvv : v' = v := Except.ok.inj (hld'.symm.trans hld)
  subst hvv
  have hinfo : (memberProjection B 0 (.indc ind)).info = .iPrj ⟨(0 : Nat).toUInt64, B⟩ := rfl
  unfold L1.RawCIRep at hraw
  rw [hinfo] at hraw
  obtain ⟨-, lcB, cb', ms', ind', blobs, hgetB, -, -, hexB, -, hcb', hms', -, raw⟩ := hraw
  obtain ⟨hhB, haB⟩ := hload_ld.1 _ lcB hgetB
  have hcb_eq : cb' = cb := hS.record_eq hrecB (Core.hashed_mono hsub_ld hhB) haB hexB
  subst cb'
  have hms_eq : ms' = #[.indc ind] := Ixon.ConstantInfo.muts.inj (hcb'.symm.trans hrec.muts)
  subst ms'
  rw [idx_zero B] at hms' raw
  have hind_eq : ind' = ind := by
    have e : (Ixon.MutConst.indc ind : Ixon.MutConst) = .indc ind' := Option.some.inj hms'
    exact (Ixon.MutConst.indc.inj e).symm
  subst ind'
  obtain ⟨hlv, hnp, hni, hnc, -, tyPtr, blkPtr, b, hb_eq, hbp_m, hv, -⟩ := raw
  subst hv
  have hsafe : ind.isUnsafe = false := by
    have hl := hrec.logic
    simp only [IxVM.Consistency.InLogic, hrec.muts] at hl
    exact (hl (.indc ind) (by simp)).1
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
    injection hargs with hblk hargs; injection hargs with hidx _
    subst hnl hty hnp' hni' hnc' hiu hblk hidx
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
      exact native_ctor_slots hnc ind.ctors.size 0 (by omega) rfl rfl hsub_ctors hbp ev137 j
        (Nat.zero_le _) hj
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
      (m1492 := m1492) (m1749 := m1653) (m1793 := m1688) (m1841 := m1736)
      (cs1864 := cs_mc)
      (ev14 := ev_iu) (hv1240 := hv_ind) (ev1295 := ev_ws)
      (hm1362 := hm1354) (hm1384 := hm1376) (ev1343 := ev_emb)
      (hm1435 := hm1427) (ev1408 := ev_es) (ev1452 := ev_saf)
      (ev1482 := ev_mk) (ev1505 := ev_mod) (ev1663 := ev_fa) (ev1711 := ev_lead) (ev1759 := ev_tele)
      (hm1849 := hm1736) (ev1805 := ev_rsl) (ev1866 := ev_mc) (hc1974 := hc) .. =>
    injection hv_ind with _ _ hargs
    injection hargs with hnl hargs; injection hargs with hty hargs
    injection hargs with hnp' hargs; injection hargs with hni' hargs
    injection hargs with hnc' hargs; injection hargs with _ hargs
    injection hargs with hblk hargs; injection hargs with hidx _
    subst hnl hty hnp' hni' hnc' hblk hidx
    have e_1376 : Heap.Extends m1283 m1376 := by rw [hm1376]; exact Heap.Extends.snoc m1283 _
    have e_1354 : Heap.Extends m1376 m1354 := by rw [hm1354]; exact Heap.Extends.snoc m1376 _
    have e_1427 : Heap.Extends m1333 m1427 := by rw [hm1427]; exact Heap.Extends.snoc m1333 _
    have e_1736 : Heap.Extends m1653 m1736 := by rw [hm1736]; exact Heap.Extends.snoc m1653 _
    have e_to_1688 : Heap.Extends m_chk m1688 :=
      ev_iu.heap_extends.trans (ev_ws.heap_extends.trans
        (e_1376.trans (e_1354.trans (ev_emb.heap_extends.trans
          (e_1427.trans (ev_es.heap_extends.trans (ev_saf.heap_extends.trans
            (ev_mk.heap_extends.trans (ev_mod.heap_extends.trans
              ((ev_fa.heap_extends.trans ev_lead.heap_extends).trans (ev_tele.heap_extends.trans
                (e_1736.trans ev_rsl.heap_extends))))))))))))
    have hsub_mc : ∀ cl ∈ cs_mc, cl ∈ calls := fun cl hcl =>
      hsub_chk cl (by rw [hc]; simp [hcl])
    have hbp := Bytes.repAddressRef_heapMono₂ Core.addrTy e_to_1688 hbp_m
    exact modeled_ctor_slots hnc ind.ctors.size 0 (by omega) rfl rfl hsub_mc hbp ev_mc j
      (Nat.zero_le _) hj

/-- **The reading of the former**, over the run's store. -/
theorem former_reads (ht : t.check = .ok ()) (hbound : Bounded calls)
    (hS : LoadedReads.RunStore calls E₀) (hrec : BlockUnitRecord E₀ B cb ind)
    (hchk : MutsMemberCheckedAtFullAt calls bAddr t B #[.indc ind] 0 n) :
    ∃ ty₀ : Ix.Kernel.Expr .anon,
      (exprReader t (fun x => E₀.blobs.get? x) cb id (blockSelf t B #[.indc ind])).read
        ind.typ = .ok ty₀ ∧
      ∀ caps, Reads t E₀ (memberAddr B 0 (.indc ind))
        (.indInfo ⟨keyOf t (memberAddr B 0 (.indc ind)), List.range ind.lvls.toNat, ty₀⟩
          caps) := by
  have hchkA := mutsMemberAt_checkedAt (mc := .indc ind) hbound hchk rfl
  obtain ⟨_, _, m_chk, _, rc, ap, ptr, v, r_chk, cs_ld, cs_chk, bytes, E_ld,
    _, _, _, _, hhash, hblake, hload_ld, hL1, hsub_ld, hld, ev_chk, _, hsub_chk⟩ :=
    Assembly.checkedAtFull_loadedL1 hbound ⟨n, hchkA⟩
  have hrecP : Ix.Cert.recordAt E₀ (memberAddr B 0 (.indc ind)) =
      some (memberProjection B 0 (.indc ind)) :=
    (hS.recordOf_eq_recordAt _).symm.trans hrec.former
  have hrecB : Ix.Cert.recordAt E₀ B = some cb :=
    (hS.recordOf_eq_recordAt _).symm.trans hrec.record
  obtain ⟨ms', ind', ty₀, h1, h2, -, hty, hreads, -⟩ :=
    LoadedReads.loadedL1_ind_reads (p := ⟨(0 : Nat).toUInt64, B⟩) ht hS hload_ld hsub_ld hhash
      hblake hL1 hrecP rfl hrecB hrec.logic
  have hms : ms' = #[.indc ind] := Ixon.ConstantInfo.muts.inj (h1.symm.trans hrec.muts)
  subst hms
  rw [idx_zero B] at h2
  have hind : ind' = ind := by
    have e : (Ixon.MutConst.indc ind : Ixon.MutConst) = .indc ind' := Option.some.inj h2
    exact (Ixon.MutConst.indc.inj e).symm
  subst hind
  exact ⟨ty₀, hty, hreads⟩

/-- **The reading of a constructor at a loaded slot**, over the run's store, with its stored
index, level count and parameter count pinned to the slot and the block's. -/
theorem ctorSlot_reads (ht : t.check = .ok ()) (hbound : Bounded calls)
    (hS : LoadedReads.RunStore calls E₀) (hrec : BlockUnitRecord E₀ B cb ind)
    {b : Bytes.Address} (hb : Core.ixAddr b = B) (hlv : ind.lvls.toNat < 4294967296)
    (hnp : ind.params.toNat < 72057594037927936) {j : Nat} (hj : j < ind.ctors.size)
    (hjb : j < 72057594037927936)
    (hslot : CtorSlotLoaded calls b ((0 : Nat) : F) j ind.lvls.toNat ind.params.toNat) :
    ∃ (ct : Ixon.Constructor) (ty₀ : Ix.Kernel.Expr .anon),
      ind.ctors[j]? = some ct ∧ ct.cidx.toNat = j ∧ ct.lvls.toNat = ind.lvls.toNat ∧
      ct.params.toNat = ind.params.toNat ∧
      (exprReader t (fun x => E₀.blobs.get? x) cb id (blockSelf t B #[.indc ind])).read
        ct.typ = .ok ty₀ ∧
      Reads t E₀ (ctorAddr B 0 j)
        (.ctorInfo ⟨keyOf t (ctorAddr B 0 j), List.range ct.lvls.toNat, ty₀⟩ ct.params.toNat
          ct.fields.toNat) := by
  obtain ⟨bp, ptr, h, h', cs, nl, ty, pb, mi, sl, np, nf, us, ev, hsub, hbp, hld, hsl, hnl,
    hnpv⟩ := hslot
  have hbcs : Bounded cs := RomBound.bounded_mono hbound hsub
  subst hb
  have hrecB : Ix.Cert.recordAt E₀ (Core.ixAddr b) = some cb :=
    (hS.recordOf_eq_recordAt _).symm.trans hrec.record
  have hz : ZMod.val ((0 : Nat) : F) = 0 := by simp
  have hjv : ZMod.val ((j : Nat) : F) = j :=
    ZMod.val_natCast_of_lt (by unfold Aiur.Library.U32.Goldilocks.modulus; omega)
  obtain ⟨-, -, -, blkBytes, cb', ms', ind', ct', blobs, v, hhB, haB, hexB, -, hcb', hms', hct',
    -, hldv, hraw⟩ := L1.get_ci_cprj_spec hbcs hbp ev
  have hcb_eq : cb' = cb := hS.record_eq hrecB (Core.hashed_mono hsub hhB) haB hexB
  subst cb'
  have hms_eq : ms' = #[.indc ind] := Ixon.ConstantInfo.muts.inj (hcb'.symm.trans hrec.muts)
  subst ms'
  rw [hz] at hms'
  have hind_eq : ind' = ind := by
    have e : (Ixon.MutConst.indc ind : Ixon.MutConst) = .indc ind' := Option.some.inj hms'
    exact (Ixon.MutConst.indc.inj e).symm
  subst ind'
  rw [hjv] at hct'
  have hctj : ind.ctors[j]? = some ct' := by
    rw [← Array.getElem?_toList]
    exact hct'
  have hvv : v = .construct Core.kciEnum "Ctor" [nl, ty, pb, mi, sl, np, nf, us] :=
    Except.ok.inj (hldv.symm.trans hld)
  obtain ⟨hclv, hccidx, hcpar, -, -, tyPtr, blkPtr, b', -, -, hv, -⟩ := hraw
  rw [hv] at hvv
  injection hvv with _ _ hargs
  injection hargs with hl1 hargs
  injection hargs with _ hargs
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
  have hproj : recordOf E₀ (ctorAddr (Core.ixAddr b) (ZMod.val ((0 : Nat) : F))
      (ZMod.val ((j : Nat) : F))) =
      some (constructorProjection (Core.ixAddr b) (ZMod.val ((0 : Nat) : F))
        (ZMod.val ((j : Nat) : F))) := by
    rw [hz, hjv]
    exact hrec.ctors j hj
  have hcidxAll : ∀ (ms : Array Ixon.MutConst) (ind₁ : Ixon.Inductive) (ct : Ixon.Constructor),
      cb.info = .muts ms → ms[ZMod.val ((0 : Nat) : F)]? = some (.indc ind₁) →
      ind₁.ctors[ZMod.val ((j : Nat) : F)]? = some ct →
      ct.cidx.toNat = ZMod.val ((j : Nat) : F) := by
    intro ms ind₁ ct hcb hm hc
    have hms₁ : ms = #[.indc ind] := Ixon.ConstantInfo.muts.inj (hcb.symm.trans hrec.muts)
    subst ms
    rw [hz] at hm
    have e : (Ixon.MutConst.indc ind : Ixon.MutConst) = .indc ind₁ := Option.some.inj hm
    have hi : ind₁ = ind := (Ixon.MutConst.indc.inj e).symm
    subst ind₁
    rw [hjv] at hc ⊢
    have hct : ct = ct' := Option.some.inj (hc.symm.trans hctj)
    subst ct
    exact hcidx
  obtain ⟨ms₂, ind₂, ct₂, ty₀, v₂, hcbm, hm₂, hc₂, -, hty, hreads, -⟩ :=
    LoadedReads.get_ci_cprj_reads ht hS hbcs hsub hbp ev hrecB hrec.logic hcidxAll hproj
  have hms₂ : ms₂ = #[.indc ind] := Ixon.ConstantInfo.muts.inj (hcbm.symm.trans hrec.muts)
  subst ms₂
  rw [hz] at hm₂
  have e₂ : (Ixon.MutConst.indc ind : Ixon.MutConst) = .indc ind₂ := Option.some.inj hm₂
  have hi₂ : ind₂ = ind := (Ixon.MutConst.indc.inj e₂).symm
  subst ind₂
  rw [hjv] at hc₂ hreads
  have hct₂ : ct₂ = ct' := Option.some.inj (hc₂.symm.trans hctj)
  subst ct₂
  rw [hz] at hreads
  exact ⟨ct', ty₀, hctj, hcidx, hlvls, hpar, hty, hreads⟩

/-- **The constructors' addresses are distinct**: the store holds the constructor projection of
each slot at its address, and these records differ. -/
theorem ctorAddr_inj (hrec : BlockUnitRecord E₀ B cb ind)
    (hjb : ∀ {j}, j < ind.ctors.size → j < UInt64.size) :
    ∀ j j', j < ind.ctors.size → j' < ind.ctors.size →
      ctorAddr B 0 j = ctorAddr B 0 j' → j = j' := by
  intro j j' hj hj' he
  have h1 := hrec.ctors j hj
  rw [he, hrec.ctors j' hj'] at h1
  have h2 : Ixon.ConstantInfo.cPrj ⟨(0 : Nat).toUInt64, j'.toUInt64, B⟩ =
      .cPrj ⟨(0 : Nat).toUInt64, j.toUInt64, B⟩ :=
    congrArg Ixon.Constant.info (Option.some.inj h1)
  injection h2 with h3
  injection h3 with _ h4 _
  have e := congrArg UInt64.toNat h4
  have ej : j.toUInt64.toNat = j := UInt64.toNat_ofNat_of_lt (hjb hj)
  have ej' : j'.toUInt64.toNat = j' := UInt64.toNat_ofNat_of_lt (hjb hj')
  rw [ej, ej'] at e
  exact e.symm

/-- **The declared block of the unit, read over the run's store**: the former, then one
constructor per slot, each with its reading; no pinned basis block; non-derived keys. The
former's capability record in the reading is any (`Reads` leaves it open). -/
theorem blockReads_of_member (ht : t.check = .ok ()) (hbound : Bounded calls)
    (hS : LoadedReads.RunStore calls E₀) (hrec : BlockUnitRecord E₀ B cb ind)
    (hchk : MutsMemberCheckedAtFullAt calls bAddr t B #[.indc ind] 0 n) :
    ∃ (ty₀ : Ix.Kernel.Expr .anon) (cs : List (ConstantInfo .anon)),
      (exprReader t (fun x => E₀.blobs.get? x) cb id (blockSelf t B #[.indc ind])).read
        ind.typ = .ok ty₀ ∧
      cs.length = ind.ctors.size ∧
      (∀ j c, cs[j]? = some c → ∃ (ct : Ixon.Constructor) (tyj : Ix.Kernel.Expr .anon),
        ind.ctors[j]? = some ct ∧ ct.cidx.toNat = j ∧ ct.lvls.toNat = ind.lvls.toNat ∧
        ct.params.toNat = ind.params.toNat ∧
        (exprReader t (fun x => E₀.blobs.get? x) cb id (blockSelf t B #[.indc ind])).read
          ct.typ = .ok tyj ∧
        c = .ctorInfo ⟨keyOf t (ctorAddr B 0 j), List.range ct.lvls.toNat, tyj⟩
          ct.params.toNat ct.fields.toNat ∧
        Reads t E₀ (ctorAddr B 0 j) c) ∧
      ∀ caps : Ix.Kernel.IndCaps .anon,
        BlockReadings t E₀ B ind (.indInfo ⟨keyOf t (memberAddr B 0 (.indc ind)),
          List.range ind.lvls.toNat, ty₀⟩ caps :: cs) ∧
        Ix.Kernel.basisPinHit (.indInfo ⟨keyOf t (memberAddr B 0 (.indc ind)),
          List.range ind.lvls.toNat, ty₀⟩ caps :: cs) = none ∧
        Decl.DeclNonAux (.indDecl (.indInfo ⟨keyOf t (memberAddr B 0 (.indc ind)),
          List.range ind.lvls.toNat, ty₀⟩ caps :: cs) ind.params.toNat) := by
  have htwf : t.wf = true := by
    unfold Ix.Kernel.RoleTable.wf
    rw [ht]
    rfl
  obtain ⟨ty₀, hty, hfr⟩ := former_reads ht hbound hS hrec hchk
  obtain ⟨b, hb, hlv, hnp, hnc, hslots⟩ := ctorSlots_of_member hbound hS hrec hchk
  obtain ⟨cs, hlen, hcs⟩ := exists_list_of_forall (P := fun j c =>
    ∃ (ct : Ixon.Constructor) (tyj : Ix.Kernel.Expr .anon),
      ind.ctors[j]? = some ct ∧ ct.cidx.toNat = j ∧ ct.lvls.toNat = ind.lvls.toNat ∧
      ct.params.toNat = ind.params.toNat ∧
      (exprReader t (fun x => E₀.blobs.get? x) cb id (blockSelf t B #[.indc ind])).read
        ct.typ = .ok tyj ∧
      c = .ctorInfo ⟨keyOf t (ctorAddr B 0 j), List.range ct.lvls.toNat, tyj⟩
        ct.params.toNat ct.fields.toNat ∧
      Reads t E₀ (ctorAddr B 0 j) c) ind.ctors.size (by
    intro j hj
    obtain ⟨ct, tyj, h1, h2, h3, h4, h5, h6⟩ :=
      ctorSlot_reads ht hbound hS hrec hb hlv hnp hj (by omega) (hslots j hj)
    exact ⟨_, ct, tyj, h1, h2, h3, h4, h5, rfl, h6⟩)
  refine ⟨ty₀, cs, hty, hlen, hcs, fun caps => ?_⟩
  -- the constructors are no recursors
  have hnorec : (ConstantInfo.indInfo
      ⟨keyOf t (memberAddr B 0 (.indc ind)), List.range ind.lvls.toNat, ty₀⟩ caps :: cs).any
      isRecInfo = false := by
    simp only [List.any_cons, isRecInfo, Bool.false_or, List.any_eq_false]
    intro c hc
    obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hc
    obtain ⟨ct, tyj, -, -, -, -, -, rfl, -⟩ := hcs j c hj
    simp [isRecInfo]
  have hpin := basisPinHit_none_of_noRec hnorec
  -- distinct addresses, distinct keys
  have hjb : ∀ {j}, j < ind.ctors.size → j < UInt64.size := fun hj => by
    show _ < 18446744073709551616
    omega
  have hctor_ne : ∀ j, j < ind.ctors.size → ctorAddr B 0 j ≠ memberAddr B 0 (.indc ind) := by
    intro j hj he
    have h1 := hrec.ctors j hj
    rw [he, hrec.former] at h1
    have h2 : Ixon.ConstantInfo.iPrj ⟨(0 : Nat).toUInt64, B⟩ =
        .cPrj ⟨(0 : Nat).toUInt64, j.toUInt64, B⟩ :=
      congrArg Ixon.Constant.info (Option.some.inj h1)
    cases h2
  have hctor_inj : ∀ j j', j < ind.ctors.size → j' < ind.ctors.size →
      ctorAddr B 0 j = ctorAddr B 0 j' → j = j' :=
    ctorAddr_inj hrec (fun hj => hjb hj)
  have hname : ∀ j c, cs[j]? = some c → c.name = keyOf t (ctorAddr B 0 j) := by
    intro j c hc
    obtain ⟨ct, tyj, -, -, -, -, -, rfl, -⟩ := hcs j c hc
    rfl
  have hlt : ∀ j c, cs[j]? = some c → j < ind.ctors.size := by
    intro j c hc
    rw [← hlen]
    exact (List.getElem?_eq_some_iff.mp hc).1
  have hndcs : (cs.map (·.name)).Nodup :=
    nodup_names_of_index hname (fun j j' hj hj' e => hctor_inj j j' (by omega) (by omega)
      (Core.keyOf_inj (a₁ := ctorAddr B 0 j) (a₂ := ctorAddr B 0 j') htwf e))
  have hnd : ((ConstantInfo.indInfo
      ⟨keyOf t (memberAddr B 0 (.indc ind)), List.range ind.lvls.toNat, ty₀⟩ caps :: cs).map
      (·.name)).Nodup := by
    rw [List.map_cons, List.nodup_cons]
    refine ⟨fun hm => ?_, hndcs⟩
    obtain ⟨c, hc, hcn⟩ := List.mem_map.mp hm
    obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hc
    have e : keyOf t (ctorAddr B 0 j) = keyOf t (memberAddr B 0 (.indc ind)) :=
      (hname j c hj).symm.trans hcn
    exact hctor_ne j (hlt j c hj)
      (Core.keyOf_inj (a₁ := ctorAddr B 0 j) (a₂ := memberAddr B 0 (.indc ind)) htwf e)
  refine ⟨⟨_, cs, rfl, hfr caps, hlen, fun j c hc => ?_⟩, hpin,
    declNonAux_indDecl_of hpin ?_ hnd⟩
  · obtain ⟨ct, tyj, -, -, -, -, -, -, hr⟩ := hcs j c hc
    exact hr
  · intro ci hci
    rcases List.mem_cons.mp hci with rfl | hc
    · exact ⟨nonAux_keyOf t _, read_refsIn_nonAux hty, trivial⟩
    · obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hc
      obtain ⟨ct, tyj, -, -, -, -, htyj, rfl, -⟩ := hcs j ci hj
      exact ⟨nonAux_keyOf t _, read_refsIn_nonAux htyj, trivial⟩

/-- **Every block of readings at the unit's addresses is the read block**: the former's reading
up to its capability record, and the constructors' readings. -/
theorem blockReads_shape (ht : t.check = .ok ()) (hbound : Bounded calls)
    (hS : LoadedReads.RunStore calls E₀) (hrec : BlockUnitRecord E₀ B cb ind)
    (hchk : MutsMemberCheckedAtFullAt calls bAddr t B #[.indc ind] 0 n)
    {blk : List (ConstantInfo .anon)} (hblk : BlockReadings t E₀ B ind blk) :
    ∃ (ty₀ : Ix.Kernel.Expr .anon) (caps : Ix.Kernel.IndCaps .anon)
      (cs : List (ConstantInfo .anon)),
      blk = .indInfo ⟨keyOf t (memberAddr B 0 (.indc ind)), List.range ind.lvls.toNat, ty₀⟩ caps
        :: cs ∧
      (exprReader t (fun x => E₀.blobs.get? x) cb id (blockSelf t B #[.indc ind])).read
        ind.typ = .ok ty₀ ∧
      cs.length = ind.ctors.size ∧
      ∀ j c, cs[j]? = some c → ∃ (ct : Ixon.Constructor) (tyj : Ix.Kernel.Expr .anon),
        ind.ctors[j]? = some ct ∧ ct.cidx.toNat = j ∧ ct.lvls.toNat = ind.lvls.toNat ∧
        ct.params.toNat = ind.params.toNat ∧
        (exprReader t (fun x => E₀.blobs.get? x) cb id (blockSelf t B #[.indc ind])).read
          ct.typ = .ok tyj ∧
        c = .ctorInfo ⟨keyOf t (ctorAddr B 0 j), List.range ct.lvls.toNat, tyj⟩
          ct.params.toNat ct.fields.toNat ∧
        Reads t E₀ (ctorAddr B 0 j) c := by
  have hroles : (t.bound.toList.map (·.1)).Nodup := (Ix.Kernel.RoleTable.check_nodup ht).1
  obtain ⟨fr, cs, rfl, hfr, hlen, hcs⟩ := hblk
  obtain ⟨ty₀, hty, hfr₀⟩ := former_reads ht hbound hS hrec hchk
  obtain ⟨b, hb, hlv, hnp, hnc, hslots⟩ := ctorSlots_of_member hbound hS hrec hchk
  have hsame := Reads.functional hroles hfr (hfr₀ {})
  obtain ⟨caps, hcaps⟩ : ∃ caps, fr = .indInfo
      ⟨keyOf t (memberAddr B 0 (.indc ind)), List.range ind.lvls.toNat, ty₀⟩ caps := by
    rcases hsame with e | ⟨cv, v, h₁, h₂, -, e⟩ | ⟨cv, c₁, c₂, e₁, e₂⟩
    · exact ⟨{}, e⟩
    · cases e
    · injection e₂ with ecv
      exact ⟨c₁, by rw [e₁, ecv]⟩
  refine ⟨ty₀, caps, cs, by rw [hcaps], hty, hlen, fun j c hc => ?_⟩
  have hj : j < ind.ctors.size := by
    rw [← hlen]
    exact (List.getElem?_eq_some_iff.mp hc).1
  obtain ⟨ct, tyj, h1, h2, h3, h4, h5, h6⟩ :=
    ctorSlot_reads ht hbound hS hrec hb hlv hnp hj (by omega) (hslots j hj)
  have hsame' := Reads.functional hroles (hcs j c hc) h6
  have hceq : c = .ctorInfo ⟨keyOf t (ctorAddr B 0 j), List.range ct.lvls.toNat, tyj⟩
      ct.params.toNat ct.fields.toNat := by
    rcases hsame' with e | ⟨cv, v, h₁, h₂, -, e⟩ | ⟨cv, c₁, c₂, -, e⟩
    · exact e
    · cases e
    · cases e
  exact ⟨ct, tyj, h1, h2, h3, h4, h5, hceq, hcs j c hc⟩

end Member

/-! ## The recognition of the block -/

theorem stripPis_sort_piBinders :
    ∀ (n : Nat) (e : Ix.Kernel.Expr .anon) {bs : List (Ix.Kernel.Expr .anon × Ix.Kernel.BinderMeta)}
      {s : Ix.Kernel.Level},
      e.stripPis n = some (bs, .sort s) → e.piBinders = (bs, .sort s) ∧ bs.length = n
  | 0, e, bs, s, h => by
    simp only [Ix.Kernel.Expr.stripPis, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨rfl, rfl⟩
  | n + 1, .forallE ty b m, bs, s, h => by
    simp only [Ix.Kernel.Expr.stripPis] at h
    cases hb : b.stripPis n with
    | none => rw [hb] at h; cases h
    | some p =>
      rw [hb] at h
      obtain ⟨bs', e'⟩ := p
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨ih1, ih2⟩ := stripPis_sort_piBinders n b hb
      refine ⟨?_, by simp [ih2]⟩
      simp only [Ix.Kernel.Expr.piBinders, ih1]
  | n + 1, .bvar _, _, _, h | n + 1, .fvar _ _, _, _, h | n + 1, .sort _, _, _, h
  | n + 1, .const _ _, _, _, h | n + 1, .app _ _, _, _, h | n + 1, .lam _ _ _, _, _, h
  | n + 1, .letE _ _ _ _, _, _, h | n + 1, .lit _, _, _, h | n + 1, .proj _ _ _, _, _, h => by
    simp [Ix.Kernel.Expr.stripPis] at h

/-- **The recogniser reads a former at its telescope and its constructors without the recursor
record**, where the counts and level parameters agree and no name is a reserved basis name. -/
theorem nativePartsNoRec?_isSome {nP : Nat} {cvT : ConstantVal .anon}
    {caps : Ix.Kernel.IndCaps .anon} {cs : List (ConstantInfo .anon)} {k : Nat}
    {bs : List (Ix.Kernel.Expr .anon × Ix.Kernel.BinderMeta)} {s : Ix.Kernel.Level}
    (htele : cvT.type.stripPis k = some (bs, .sort s)) (hle : nP ≤ k)
    (hT : Ix.Kernel.reservedBasisNames.contains cvT.name = false)
    (hcs : ∀ c ∈ cs, ∃ cv nF, c = .ctorInfo cv nP nF ∧ cv.levelParams = cvT.levelParams ∧
      Ix.Kernel.reservedBasisNames.contains cv.name = false) :
    ∃ p₀, Ix.Kernel.Semantics.nativePartsNoRec? nP (.indInfo cvT caps :: cs) = some p₀ := by
  obtain ⟨hpb, hlen⟩ := stripPis_sort_piBinders k _ htele
  have hall : (cs.all fun | .ctorInfo .. => true | _ => false) = true := by
    rw [List.all_eq_true]
    intro c hc
    obtain ⟨cv, nF, rfl, -, -⟩ := hcs c hc
    rfl
  obtain ⟨csT, hsp, hrest⟩ := Decl.sumSplit_append_recStub cs
    ⟨Ix.Kernel.auxKey cvT.name .recursor, cvT.levelParams, .sort .zero⟩ hall
  have hcnt : Ix.Kernel.nativeCounts? nP cvT csT 0 0 = some (nP, bs.length - nP) := by
    unfold Ix.Kernel.nativeCounts?
    rw [hpb]
    simp [hlen, hle]
  simp only [Ix.Kernel.Semantics.nativePartsNoRec?]
  split
  case isFalse hneg =>
    exfalso
    apply hneg
    rw [List.all_eq_true]
    intro c hc
    obtain ⟨cv, nF, rfl, -, -⟩ := hcs c hc
    rfl
  unfold Ix.Kernel.nativeParts?
  suffices h : ∃ q, Ix.Kernel.nativeShape? nP
      (.indInfo cvT caps :: (cs ++ [Ix.Kernel.Semantics.nativeRecStub cvT])) = some q by
    obtain ⟨q, hq⟩ := h
    exact ⟨_, by rw [hq]; rfl⟩
  simp only [Ix.Kernel.nativeShape?, Ix.Kernel.Semantics.nativeRecStub, hsp, hcnt]
  split
  · split <;> exact ⟨_, rfl⟩
  · rename_i hneg
    exfalso
    apply hneg
    simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true]
    refine ⟨⟨hT, Ix.Kernel.reservedBasisNames_contains_auxKey _ _⟩, ?_⟩
    intro c hc
    have hmem : ConstantInfo.ctorInfo c.1 c.2.1 c.2.2 ∈ cs := by
      rw [hrest]
      exact List.mem_map.mpr ⟨c, hc, rfl⟩
    obtain ⟨cv, nF, e, hlps, hres⟩ := hcs _ hmem
    injection e with e1 e2 e3
    subst e1 e2
    exact ⟨⟨rfl, hlps⟩, hres⟩

section Recognise

variable {t : Ix.Kernel.RoleTable} {calls : List (Call F)} {E₀ : Ixon.Env}
  {bAddr B : _root_.Address} {cb : Ixon.Constant} {ind : Ixon.Inductive} {n : Nat}

/-- **The declared block is recognised without its recursor**, at a former declared at its
telescope, with distinct constructor names. -/
theorem nativeParts_of_member (ht : t.check = .ok ()) (hbound : Bounded calls)
    (hS : LoadedReads.RunStore calls E₀) (hrec : BlockUnitRecord E₀ B cb ind)
    (hchk : MutsMemberCheckedAtFullAt calls bAddr t B #[.indc ind] 0 n)
    (htele : FormerAtTele t E₀ B cb ind) {blk : List (ConstantInfo .anon)}
    (hblk : BlockReadings t E₀ B ind blk)
    (hfree : ∀ x, ConstAddrOf B cb x → Decl.KeyFree (keyOf t x)) :
    ∃ p₀, Ix.Kernel.Semantics.nativePartsNoRec? ind.params.toNat blk = some p₀ ∧
      (p₀.ctors.map (·.1.name)).Nodup := by
  have htwf : t.wf = true := by
    unfold Ix.Kernel.RoleTable.wf
    rw [ht]
    rfl
  obtain ⟨ty₀, caps, cs, rfl, hty, hlen, hcs⟩ := blockReads_shape ht hbound hS hrec hchk hblk
  obtain ⟨bs, s, hts⟩ := htele ty₀ hty
  have hfreeF : Decl.KeyFree (keyOf t (memberAddr B 0 (.indc ind))) :=
    hfree _ (Or.inr ⟨_, 0, .indc ind, hrec.muts, rfl, Or.inl rfl⟩)
  have hfreeC : ∀ j, j < ind.ctors.size → Decl.KeyFree (keyOf t (ctorAddr B 0 j)) :=
    fun j hj => hfree _ (Or.inr ⟨_, 0, .indc ind, hrec.muts, rfl, Or.inr ⟨ind, j, rfl, hj, rfl⟩⟩)
  have hlt : ∀ j c, cs[j]? = some c → j < ind.ctors.size := by
    intro j c hc
    rw [← hlen]
    exact (List.getElem?_eq_some_iff.mp hc).1
  obtain ⟨p₀, hp₀⟩ := nativePartsNoRec?_isSome (caps := caps) (cs := cs)
    (cvT := ⟨keyOf t (memberAddr B 0 (.indc ind)), List.range ind.lvls.toNat, ty₀⟩) hts
    (Nat.le_add_right _ _) hfreeF.1 (by
      intro c hc
      obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hc
      obtain ⟨ct, tyj, -, -, hl, hp, -, rfl, -⟩ := hcs j c hj
      exact ⟨_, _, by rw [hp], by simp [hl], (hfreeC j (hlt j _ hj)).1⟩)
  refine ⟨p₀, hp₀, ?_⟩
  obtain ⟨caps₀, hshape, -⟩ := Decl.nativePartsNoRec?_inv hp₀
  injection hshape with _ hcs'
  have hnames : p₀.ctors.map (·.1.name) = cs.map (·.name) := by
    rw [hcs', List.map_map]
    rfl
  rw [hnames]
  obtain ⟨-, -, -, -, hnc, -⟩ := ctorSlots_of_member hbound hS hrec hchk
  have hjb : ∀ {j}, j < ind.ctors.size → j < UInt64.size := fun hj => by
    show _ < 18446744073709551616
    omega
  refine nodup_names_of_index (f := fun j => keyOf t (ctorAddr B 0 j)) (fun j c hc => ?_)
    (fun j j' hj hj' e => ctorAddr_inj hrec hjb j j' (by omega) (by omega)
      (Core.keyOf_inj (a₁ := ctorAddr B 0 j) (a₂ := ctorAddr B 0 j') htwf e))
  obtain ⟨ct, tyj, -, -, -, -, -, rfl, -⟩ := hcs j c hc
  rfl

/-! ## The former stage -/

/-- **The reading of the former's type is closed, with its level parameters defined and no free
variable**: the walked check validated its scope before anything else (`Induct` arm prelude). -/
theorem former_scope (hbound : Bounded calls) (hS : LoadedReads.RunStore calls E₀)
    (hrec : BlockUnitRecord E₀ B cb ind)
    (hchk : MutsMemberCheckedAtFullAt calls bAddr t B #[.indc ind] 0 n)
    {blob : _root_.Address → Option ByteArray} {ty₀ : Ix.Kernel.Expr .anon}
    (hty : (exprReader t blob cb id (blockSelf t B #[.indc ind])).read ind.typ = .ok ty₀) :
    ty₀.looseBVarsBounded 0 = true ∧
      ty₀.allLevelParamsDefined (List.range ind.lvls.toNat) = true ∧ ty₀.hasFvar = false := by
  have hchkA := mutsMemberAt_checkedAt (mc := .indc ind) hbound hchk rfl
  obtain ⟨_, _, m_chk, _, rc, ap, ptr, v, r_chk, cs_ld, cs_chk, bytes, E_ld,
    _, _, _, _, hhash, hblake, hload_ld, hL1, hsub_ld, hld, ev_chk, _, hsub_chk⟩ :=
    Assembly.checkedAtFull_loadedL1 hbound ⟨n, hchkA⟩
  have hrecP : Ix.Cert.recordAt E₀ (memberAddr B 0 (.indc ind)) =
      some (memberProjection B 0 (.indc ind)) :=
    (hS.recordOf_eq_recordAt _).symm.trans hrec.former
  have hrecB : Ix.Cert.recordAt E₀ B = some cb :=
    (hS.recordOf_eq_recordAt _).symm.trans hrec.record
  obtain ⟨-, -, v', hld', hraw⟩ := LoadedReads.loadedL1_record hS hsub_ld hhash hblake hL1 hrecP
  have hvv : v' = v := Except.ok.inj (hld'.symm.trans hld)
  subst hvv
  have hinfo : (memberProjection B 0 (.indc ind)).info = .iPrj ⟨(0 : Nat).toUInt64, B⟩ := rfl
  unfold L1.RawCIRep at hraw
  rw [hinfo] at hraw
  obtain ⟨-, lcB, cb', ms', ind', blobs, hgetB, -, -, hexB, -, hcb', hms', -, raw⟩ := hraw
  obtain ⟨hhB, haB⟩ := hload_ld.1 _ lcB hgetB
  have hcb_eq : cb' = cb := hS.record_eq hrecB (Core.hashed_mono hsub_ld hhB) haB hexB
  subst cb'
  have hms_eq : ms' = #[.indc ind] := Ixon.ConstantInfo.muts.inj (hcb'.symm.trans hrec.muts)
  subst ms'
  rw [idx_zero B] at hms' raw
  have hind_eq : ind' = ind := by
    have e : (Ixon.MutConst.indc ind : Ixon.MutConst) = .indc ind' := Option.some.inj hms'
    exact (Ixon.MutConst.indc.inj e).symm
  subst ind'
  obtain ⟨hlv, -, -, -, -, tyPtr, blkPtr, b, -, -, hv, rty⟩ := raw
  subst hv
  obtain ⟨prelude⟩ := Decl.native_prelude_calls ev_chk
  obtain ⟨-, hlbb, hdef⟩ := Assembly.validate_expr_well_scoped_spec (cx := readCtx t blob)
    (self := blockSelf t B #[.indc ind]) hbound hlv rty prelude.initialExtended hty
    prelude.scopeRun (hsub_chk _ prelude.scopeMember)
  exact ⟨hlbb, hdef, Assembly.memberReader_read_noFvar hty⟩

/-- **The former's stage of IxC at the prefix** (T6): the recognised block's former is checked
against the prefix as its canonical annotation, at a telescope ending in the block's sort, and
stored at the native capability record of the completed shape, for either recursion flag. The
former's key is the key of its projection address. -/
theorem formerStage_of_member {E : Ixon.Env} (ht : t.check = .ok ())
    (hS : LoadedReads.RunStore calls E₀) (hst : StepStore calls t E₀ E)
    (hrec : BlockUnitRecord E₀ B cb ind)
    (hchk : MutsMemberCheckedAtFullAt calls bAddr t B #[.indc ind] 0 n)
    {blk : List (ConstantInfo .anon)} (hblk : BlockReadings t E₀ B ind blk)
    {p₀ : Ix.Kernel.NativeParts .anon}
    (hp₀ : Ix.Kernel.Semantics.nativePartsNoRec? ind.params.toNat blk = some p₀)
    {env : Ix.Kernel.Env .anon} (hinv : Decl.PrefixInv.{u} E t (some n) env)
    (hstored : Decl.UsedRefsStored t env cb)
    (hfresh : env.find? (Core.keyOf t (Core.iprjAddr B 0)) = none)
    (hfree : Decl.KeyFree (Core.keyOf t (Core.iprjAddr B 0))) :
    ∀ isRec : Bool, ∃ (cvS : ConstantVal .anon) (p₁ : Ix.Kernel.InductiveShape .anon),
      Ix.Kernel.Semantics.SumIndRunJ Ix.Kernel.Model.rulesJ env p₀.toInductiveShape
        (fun p₁ => Ix.Kernel.nativeCapsAt p₁ isRec)
        ⟨.indInfo cvS (Ix.Kernel.nativeCapsAt p₁ isRec) :: env.consts⟩ cvS p₁ ∧
      cvS.name = Core.keyOf t (Core.iprjAddr B 0) := by
  intro isRec
  have hbound : Bounded calls := (hst.good env none).2
  obtain ⟨ty₀, caps, cs, rfl, hty, -, -⟩ := blockReads_shape ht hbound hS hrec hchk hblk
  obtain ⟨hlbb, hdef, hfv⟩ := former_scope hbound hS hrec hchk hty
  have hblockE : recordOf E B = some cb :=
    (recordOf_eq_recordAt_of_decoded hst.decoded B).trans (hst.runRecord B cb hrec.record)
  have hprojE : recordOf E (Core.iprjAddr B 0) = some (memberProjection B 0 (.indc ind)) :=
    (recordOf_eq_recordAt_of_decoded hst.decoded _).trans (hst.runRecord _ _ hrec.former)
  have htyE : (exprReader t (fun x => E.blobs.get? x) cb id
      (blockSelf t B #[.indc ind])).read ind.typ = .ok ty₀ :=
    ReaderReads.exprReader_mono (fun x b hb => hst.runBlob x b hb) hty
  obtain ⟨ty', -, hann, hcheck, -⟩ := formerChecked_of_member ht hst hinv hblockE hrec.muts
    hprojE hchk htyE hlbb hdef hfv hstored hfresh hfree
  obtain ⟨caps₀, hshape, -, -, -, -, ⟨bs₀, hst₀⟩, -⟩ := Decl.nativePartsNoRec?_inv hp₀
  injection hshape with hhead _
  injection hhead with hcv _
  have hcvT : p₀.toInductiveShape.cvT =
      ⟨Core.keyOf t (Core.iprjAddr B 0), List.range ind.lvls.toNat, ty₀⟩ := hcv.symm
  have hst₀' : ty₀.stripPis (p₀.nP + p₀.nIdx) = some (bs₀, .sort p₀.resSort) := by
    have h := hst₀
    rw [hcvT] at h
    exact h
  obtain ⟨bs', hst', -⟩ := Decl.stripPis_sort_of_annotates _ hann hst₀'
  refine ⟨⟨Core.keyOf t (Core.iprjAddr B 0), List.range ind.lvls.toNat, ty'⟩,
    p₀.toInductiveShape.withSort p₀.resSort, ?_, rfl⟩
  have hchk' : Ix.Kernel.Semantics.ConstantValCheckJ Ix.Kernel.Model.rulesJ env
      p₀.toInductiveShape.cvT ⟨Core.keyOf t (Core.iprjAddr B 0), List.range ind.lvls.toNat, ty'⟩ := by
    rw [hcvT]
    exact hcheck
  exact sumIndRunJ_of_former (isRec := isRec) hchk' hst'

end Recognise

end IxVM.Refinement.Typing
