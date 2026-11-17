import IxVMRefinement.Assembly.NativeBlockCtorRuns
import IxVMRefinement.Decl.NativeRec
import IxC.Kernel.Verify.Inductives.StructBody

/-! # The later-use condition of a native constructor

`check_positivity_fields` walks every binder of a constructor's type after its parameters. At a
binder whose domain mentions the block (`expr_mentions_block(dom, [B]) ≠ 0`) it asserts that the
binder's body has no loose occurrence of the binder's variable
(`expr_has_bvar_at(body, 0) = 0`): no later field and not the constructor's result uses a field
whose domain mentions the block. This is IxC's later-use condition (`structUsedLater`) at every
field whose domain mentions the family.

* `check_positivity_fields_later_go`, `check_positivity_later_spec`: the raw scan's assertion, read
  on the type the heap term represents;
* `CtorPositivitySlot`, `native_ctor_positivity_slots`: every slot of the native constructor
  loop loads its constructor and runs `check_positivity` on the loaded type.
-/

namespace IxVM.Refinement.Decl

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open IxVM.Refinement.Core
open Ix.Kernel (ConstantInfo ConstantVal Expr Level LevelParam)

set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-- **The raw scan's later-use assertion.** On a run of `check_positivity_fields` over a heap
term that represents `E` (with its raw syntax `R`) and mentions no projection at `T`, for each of
the first `m` binders: if its domain mentions `T`, the body after it has no loose occurrence of
its variable. -/
theorem check_positivity_fields_later_go {c : ScopedCtx} [c.TableKeyed] {indIndex : F}
    {b₀ : Bytes.Address} {T : KKey} {nl nP nIdx nCtors : Nat} {Γ : Nat → KExpr}
    (hpeer : OneTypePeerReads c b₀ T nl nP nIdx nCtors indIndex) (hlf : RawRecordFacts c) :
    ∀ (m : Nat) {k : Nat} {R E : KExpr} {rbs bs : List (KExpr × Ix.Kernel.BinderMeta)}
      {rbody body : KExpr} {pty bas dp r : SourceValue F} {h h' : Heap F} {cs : List (Call F)},
      R.stripPis m = some (rbs, rbody) →
      E.stripPis m = some (bs, body) →
      Good c.toCtx cs →
      RawRecordCoverage c cs →
      RawTmExact c.κ 0 Γ h k R E pty →
      noProjAt T E = true →
      RepList addrListEnum (Bytes.RepAddressRef addrTy) h [b₀] bas →
      ObsFn W "KernelCheck::check_positivity_fields" [pty, bas, dp] h r h' cs →
      ∀ i < m, (bs.getD i default).1.mentionsConst T = true →
        ∀ bs' rest, E.stripPis (i + 1) = some (bs', rest) → rest.hasLooseBVar 0 = false := by
  intro m
  induction m with
  | zero =>
    intro k R E rbs bs rbody body pty bas dp r h h' cs _ _ _ _ _ _ _ _ i hi
    exact absurd hi (Nat.not_lt_zero _)
  | succ m ih =>
    intro k R E rbs bs rbody body pty bas dp r h h' cs hstR hst hgood hscope hRaw hnp hbas ev
      i hi hmen bs' rest hrest
    match Obs.«KernelCheck::check_positivity_fields».obs ev with
    | .other (ld12 := ld) (hne218 := hne) .. =>
      cases R with
      | forallE rd rb rm =>
        exact (hRaw.not_forallE_of_load ld hne rd rb rm rfl).elim
      | bvar _ | fvar _ _ | sort _ | const _ _ | app _ _ | lam _ _ _ | letE _ _ _ _
      | lit _ | proj _ _ _ =>
        simp [Expr.stripPis] at hstR
    | .Forall (x_dom := xdom) (x_body := xbody) (m37 := m37) (cs47 := cs_aug)
        (m171 := m171) (cs173 := cs_sg) (cs182 := cs_rec) (ld12 := ld)
        (ev49 := ev_aug) (sg178 := sg) (ev184 := ev_rec) (hc217 := hc) .. =>
      obtain ⟨RT, RB, TT, BB, ℓ, rfl, rfl, hRT, hRB, -⟩ := hRaw.forallE_of_load ld
      simp only [Expr.stripPis, Option.map_eq_some_iff] at hstR hst
      obtain ⟨⟨rbs', rbody'⟩, hstR', heq_rbs⟩ := hstR
      obtain ⟨⟨bs'', body'⟩, hst', heq_bs⟩ := hst
      simp only [Prod.mk.injEq] at heq_rbs heq_bs
      obtain ⟨rfl, rfl⟩ := heq_rbs
      obtain ⟨rfl, rfl⟩ := heq_bs
      simp only [noProjAt, Bool.and_eq_true] at hnp
      have e_aug := ev_aug.heap_extends
      cases i with
      | zero =>
        have hmen' : TT.mentionsConst T = true := by simpa using hmen
        have hrest' : rest = BB := by
          have h1 : (Expr.forallE TT BB (bmeta ℓ)).stripPis (0 + 1) =
              some ([(TT, bmeta ℓ)], BB) := by
            simp [Expr.stripPis]
          rw [h1] at hrest
          simp only [Option.some.injEq, Prod.mk.injEq] at hrest
          exact hrest.2.symm
        rw [hrest']
        cases sg with
        | n0 m75 cs86 ev_m _ _ hc_sg =>
          have hg_m : Good c.toCtx cs86 := hgood.sub (fun x hx => by simp [hc, hc_sg, hx])
          have hs_m : RawRecordCoverage c cs86 := hscope.sub (fun x hx => by simp [hc, hc_sg, hx])
          have hzero := expr_mentions_block_zero_observed_spec hpeer hlf hg_m hs_m
            (hRT.toTmExact.mono e_aug) hnp.1
            (repList_heapMono₂ addrListEnum (Bytes.repAddressRef_heapMono₂ addrTy) e_aug hbas) ev_m
          rw [hmen'] at hzero
          cases hzero
        | other v74 m75 cs86 v129 m132 cs140 ev_m _ ev_b heq _ _ hc_sg =>
          subst heq
          have hg_b : Good c.toCtx cs140 := hgood.sub (fun x hx => by simp [hc, hc_sg, hx])
          have hBB : Tm c.κ 0 Γ m75 (k + 1) BB xbody :=
            (hRB.toTmExact.toTm).mono (e_aug.trans ev_m.heap_extends)
          exact (expr_has_bvar_at_zero_spec (j := 0) (by omega) (by decide) hg_b.2 hBB
            (by rw [Nat.cast_zero]; exact ev_b)).1
      | succ i' =>
        have e_scan : Heap.Extends m37 m171 := by
          cases sg with
          | n0 _ _ ev_m _ he _ => rw [he]; exact ev_m.heap_extends
          | other _ _ _ _ _ _ ev_m _ ev_b _ _ he _ =>
            rw [he]; exact ev_m.heap_extends.trans ev_b.heap_extends
        have e1 := e_aug.trans e_scan
        have hg_rec : Good c.toCtx cs_rec := hgood.sub (fun x hx => by simp [hc, hx])
        have hs_rec : RawRecordCoverage c cs_rec := hscope.sub (fun x hx => by simp [hc, hx])
        have hbas' := repList_heapMono₂ addrListEnum (Bytes.repAddressRef_heapMono₂ addrTy) e1 hbas
        simp only [List.getD_cons_succ] at hmen
        have hrest' : ∃ tl, BB.stripPis (i' + 1) = some (tl, rest) := by
          simp only [Expr.stripPis, Option.map_eq_some_iff] at hrest
          obtain ⟨⟨tl, rest'⟩, hr, heq⟩ := hrest
          simp only [Prod.mk.injEq] at heq
          obtain ⟨-, rfl⟩ := heq
          exact ⟨tl, hr⟩
        obtain ⟨tl, hr⟩ := hrest'
        exact ih hstR' hst' hg_rec hs_rec (hRB.mono e1) hnp.2 hbas' ev_rec i' (by omega) hmen
          tl rest hr

/-- **`check_positivity` asserts IxC's later-use condition** at every field whose domain
mentions `T`: on a constructor type `E` (raw syntax `R`, both with `nP + nF` leading binders)
whose heap term the run checks, a field whose domain mentions `T` is used by no later binder
and not by the result (`structUsedLater`). -/
theorem check_positivity_later_spec {c : ScopedCtx} [c.TableKeyed] {indIndex : F}
    {b₀ : Bytes.Address} {T : KKey} {nl nP nIdx nCtors nF : Nat} {Γ : Nat → KExpr}
    {R E : KExpr} {rcbs cbs : List (KExpr × Ix.Kernel.BinderMeta)} {rbody cbody : KExpr}
    {pcty pblk r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (hnP : nP < 18446744069414584321)
    (hpeer : OneTypePeerReads c b₀ T nl nP nIdx nCtors indIndex) (hlf : RawRecordFacts c)
    (hgood : Good c.toCtx cs) (hscope : RawRecordCoverage c cs)
    (hcty : RawTmExact c.κ 0 Γ h 0 R E pcty) (hnp : noProjAt T E = true)
    (hstR : R.stripPis (nP + nF) = some (rcbs, rbody))
    (hstrip : E.stripPis (nP + nF) = some (cbs, cbody))
    (hblk : Bytes.RepAddressRef addrTy h b₀ pblk)
    (ev : ObsFn W "KernelCheck::check_positivity" [pcty, .field (nP : F), pblk] h r h' cs) :
    ∀ i < nF, (cbs.getD (nP + i) default).1.mentionsConst T = true →
      Ix.Kernel.structUsedLater E nP i = false := by
  match Obs.«KernelCheck::check_positivity».obs ev with
  | .run (m2 := m2) (m26 := m26) (m39 := m39) (cs71 := cs_fields) (hm12 := hm2) (hm34 := hm26)
      (ev51 := ev_peel) (ev73 := ev_fields) (hc98 := hc) .. =>
    have e26 : Heap.Extends h m26 := by rw [hm26]; exact Heap.Extends.snoc h _
    have e2 : Heap.Extends m26 m2 := by rw [hm2]; exact Heap.Extends.snoc m26 _
    have ext_m2 : Heap.Extends h m2 := e26.trans e2
    obtain ⟨hm39, rbsP, rcrest₀, bsP, crest₀, hstRP, hstP, -, -, hcrest₀⟩ :=
      peel_n_foralls_raw_bounded_spec nP hnP (hcty.mono ext_m2) ev_peel
    rw [hm39] at ev_fields
    rw [Nat.zero_add] at hcrest₀
    obtain ⟨rcbs₁, rcrest₁, rcbs₂, hstRP', hstRF, -, -⟩ := stripPis_split nP nF hstR
    rw [hstRP] at hstRP'
    simp only [Option.some.injEq, Prod.mk.injEq] at hstRP'
    obtain ⟨rfl, rfl⟩ := hstRP'
    obtain ⟨cbs₁, crest₁, cbs₂, hstP', hstF, hcbs_app, hlen₁⟩ := stripPis_split nP nF hstrip
    rw [hstP] at hstP'
    simp only [Option.some.injEq, Prod.mk.injEq] at hstP'
    obtain ⟨rfl, rfl⟩ := hstP'
    have hnil : RepList addrListEnum (Bytes.RepAddressRef addrTy) m2 []
        (.ptr (.enum addrListEnum) h.length) :=
      RepLinkedList.nil (e2.getElem?_eq (by rw [hm26]; simp))
    have hbas_m2 : RepList addrListEnum (Bytes.RepAddressRef addrTy) m2 [b₀]
        (.ptr (.enum addrListEnum) m26.length) :=
      RepLinkedList.cons (by rw [hm2]; simp)
        (Bytes.repAddressRef_heapMono₂ addrTy ext_m2 hblk) hnil
    have hg_fields : Good c.toCtx cs_fields := hgood.sub (fun x hx => by simp [hc, hx])
    have hs_fields : RawRecordCoverage c cs_fields := hscope.sub (fun x hx => by simp [hc, hx])
    have hnp_crest := (noProjAt_stripPis (T := T) hstP hnp).2
    have hgo := check_positivity_fields_later_go hpeer hlf nF hstRF hstF hg_fields hs_fields
      hcrest₀ hnp_crest hbas_m2 ev_fields
    intro i hi hmen
    have hget : (cbs.getD (nP + i) default).1 = (cbs₂.getD i default).1 := by
      have hi₂ : i < cbs₂.length := by
        have := Expr.stripPis_length nF hstF; omega
      have hi_all : nP + i < cbs.length := by
        rw [← hcbs_app, List.length_append, hlen₁]; omega
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi_all,
        List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi₂]
      simp only [Option.getD_some]
      have hget? : cbs[nP + i]? = cbs₂[i]? := by
        rw [← hcbs_app, List.getElem?_append_right (by omega), hlen₁, Nat.add_sub_cancel_left]
      rw [List.getElem?_eq_getElem hi_all, List.getElem?_eq_getElem hi₂, Option.some.injEq] at hget?
      exact congrArg Prod.fst hget?
    rw [hget] at hmen
    cases hU : E.stripPis (nP + i + 1) with
    | none => simp only [Ix.Kernel.structUsedLater, hU]
    | some p =>
      obtain ⟨bsU, rest⟩ := p
      simp only [Ix.Kernel.structUsedLater, hU]
      rw [show nP + i + 1 = nP + (i + 1) by omega] at hU
      obtain ⟨bU₁, midU, bU₂, hUP, hUmid, -, -⟩ := stripPis_split nP (i + 1) hU
      rw [hstP] at hUP
      simp only [Option.some.injEq, Prod.mk.injEq] at hUP
      obtain ⟨-, rfl⟩ := hUP
      rw [Expr.hasLooseBVarB_eq]
      exact hgo i hi hmen bU₂ rest hUmid

/-! ## The positivity check of every slot of the native constructor loop -/

/-- **A constructor slot whose positivity the circuit checked**: a `get_ci_cprj` run in `calls`
on the block `b` at member `i` and slot `j`, and a later `check_positivity` run in `calls` on
the loaded type, at `nP` parameters, on the same block argument. -/
def CtorPositivitySlot (calls : List (Call F)) (b : Bytes.Address) (i : F) (j nP : Nat) : Prop :=
  ∃ (bp ptr : SourceValue F) (h h' : Heap F) (cs : List (Call F))
    (nl ty pb mi sl np nf us : SourceValue F) (h1 h2 : Heap F) (r : SourceValue F)
    (cs' : List (Call F)),
    ObsFn W "Ingress::get_ci_cprj" [bp, .field i, .field (j : F)] h ptr h' cs ∧
    (∀ cl ∈ cs, cl ∈ calls) ∧ Bytes.RepAddressRef addrTy h b bp ∧
    loadValue h' ptr = .ok (.construct kciEnum "Ctor" [nl, ty, pb, mi, sl, np, nf, us]) ∧
    Heap.Extends h' h1 ∧
    ObsFn W "KernelCheck::check_positivity" [ty, .field (nP : F), bp] h1 r h2 cs' ∧
    (∀ cl ∈ cs', cl ∈ calls)

/-- **The safe native constructor loop checks the positivity of every slot from its start.** -/
theorem native_ctor_positivity_slots {b : Bytes.Address} {n nP : Nat} {i : F}
    (hn : n < 72057594037927936) {calls : List (Call F)} :
    ∀ (m k : Nat) {rc former ni nl blockArg sortLevel r : SourceValue F}
      {h h' : Heap F} {cs : List (Call F)}, m + k = n →
      (∀ cl ∈ cs, cl ∈ calls) →
      Bytes.RepAddressRef addrTy h b blockArg →
      ObsFn W "KernelCheck::check_inductive_shape_ctors"
        [rc, former, .field (nP : F), ni, .field (n : F), nl, blockArg, .field i, sortLevel,
          .field 0, .field (k : F)] h r h' cs →
      ∀ j, k ≤ j → j < n → CtorPositivitySlot calls b i j nP := by
  intro m
  induction m with
  | zero =>
    intro k rc former ni nl blockArg sortLevel r h h' cs hmk _ _ _ j hkj hjn
    omega
  | succ m ih =>
    intro k rc former ni nl blockArg sortLevel r h h' cs hmk hsub hbp ev j hkj hjn
    match Obs.«KernelCheck::check_inductive_shape_ctors».obs ev with
    | .n0 (op17 := op) .. =>
      have hzero : (.field ((0 : Nat) : F) : SourceValue F) =
          .field (((n - k : Nat) : F)) := by
        simpa using evalBinOp_sub_nat (by omega : k ≤ n) op
      have := nat_eq_of_field_eq_bounded (by decide) (by omega) hzero
      omega
    | .other (m34 := after) (p41 := ptr) (cs47 := loadCalls)
        (x_c_nlvls := cnl) (x_cty := cty) (x_c_block := cblk)
        (x_c_ind_idx := cmi) (x_c_cidx := csl) (x_c_np := cnp) (x_c_nf := cnf)
        (x_c_unsafe := cus)
        (m144 := m144) (m319 := m319) (m387 := m387) (m400 := m400) (m430 := m430)
        (m476 := m476) (m546 := m546) (m646 := m646) (cs648 := cs_sg)
        (m655 := nextHeap) (cs695 := nextCalls) (v708 := nextIndex)
        (ev49 := loaded) (ld43 := tag) (ev154 := ev_aeq) (heq289 := paramsChecked)
        (ev331 := ev_ws) (hm395 := hm387) (ev368 := ev_es) (ev412 := ev_saf)
        (ev442 := ev_pa) (ev488 := ev_rt) (ev558 := ev_fu) (sg653 := sg_pos)
        (op792 := addition) (ev697 := nextRun) (hc794 := allCalls) .. =>
      by_cases hjk : j = k
      · subst hjk
        have e_nil : Heap.Extends m319 m387 := by rw [hm387]; exact Heap.Extends.snoc m319 _
        have e_to_pos : Heap.Extends after m546 :=
          ev_aeq.heap_extends.trans (ev_ws.heap_extends.trans (e_nil.trans
            (ev_es.heap_extends.trans (ev_saf.heap_extends.trans (ev_pa.heap_extends.trans
              (ev_rt.heap_extends.trans ev_fu.heap_extends))))))
        cases sg_pos with
        | other hne _ _ _ => exact absurd rfl hne
        | n0 cs_pos _ ev_pos hc_sg =>
          rw [paramsChecked] at ev_pos
          exact ⟨blockArg, ptr, h, after, loadCalls, cnl, cty, cblk, cmi, csl, cnp, cnf, cus,
            m546, m646, _, cs_pos, loaded,
            fun cl hcl => hsub cl (by rw [allCalls]; simp [hcl]), hbp, tag, e_to_pos, ev_pos,
            fun cl hcl => hsub cl (by rw [allCalls]; simp [hc_sg, hcl])⟩
      · have added := evalBinOp_add_nat k 1 addition
        subst nextIndex
        have nextMember : (⟨"KernelCheck::check_inductive_shape_ctors",
            [rc, former, .field (nP : F), ni, .field (n : F), nl, blockArg, .field i, sortLevel,
              .field 0, .field ((k + 1 : Nat) : F)], nextHeap⟩ : Call F) ∈ cs := by
          rw [allCalls]
          simp
        have nextBlock := Bytes.repAddressRef_heapMono₂ addrTy
          (ev.call_heap_bounds nextMember).1 hbp
        exact ih (k + 1) (by omega)
          (fun cl hcl => hsub cl (by rw [allCalls]; simp [hcl])) nextBlock nextRun j
          (by omega) hjn

end IxVM.Refinement.Decl
