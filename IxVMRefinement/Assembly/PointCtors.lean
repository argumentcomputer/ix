import IxVMRefinement.Assembly.PointFormer
import IxVMRefinement.Assembly.NativeBlockCtorLoads
import IxVMRefinement.Assembly.NativeBlockNewFacts
import IxVMRefinement.Assembly.BareState

/-! # The constructors of a block member on the modeled route, at the stage of the formers

On the modeled branch of `check_const`'s `Induct` arm, the check of member `i` runs
`check_modeled_ctors` over the member's constructors. For constructor `j` it loads the
constructor record (`get_ci_cprj`), asserts its slot, member, level count, parameter count and
safety against the member's, validates the scope of its type, checks that type is a sort
(`k_ensure_sort`) and checks its return type (`check_ctor_return_type`: after the parameters and
fields, a spine headed by the member itself with `n_params + n_indices` arguments).

* `ModeledCtorRun`, `modeled_ctor_runs`: every slot of the loop, with its load, its scope check,
  its sort check and its return-type check;
* `induct_native_or_ctors`: a successful `Induct` check either observed `block_is_modeled`
  answering `0` (the native branch) or ran the modeled constructor loop;
* `check_ctor_return_type_head`: the return-type check on an exactly represented type gives a
  telescope ending in an application of the member's projection address to
  `n_params + n_indices` arguments;
* `pointCtors_of_member`: for every constructor `j` of member `i`, its reading and canonical
  annotation, its counts, its front door at the stage of the formers (`ConstantValRunJ`) and its
  return shape (`EndsHead` at the member's former).
-/

universe u

set_option maxHeartbeats 1600000
set_option maxRecDepth 100000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace IxVM.Refinement.Typing

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open IxVM (F)
open IxVM.Consistency

private theorem toUInt64_toNat_ct {n : Nat} (hn : n < UInt64.size) : n.toUInt64.toNat = n := by
  change (UInt64.ofNat n).toNat = n
  rw [UInt64.toNat_ofNat']
  exact Nat.mod_eq_of_lt hn

/-! ## Environments with constants in front -/

/-- **A constant of the list is found at its name** (perhaps as an earlier constant of that
name). -/
theorem find?_some_of_mem :
    ∀ {l : List (Ix.Kernel.ConstantInfo .anon)} {x : Ix.Kernel.ConstantInfo .anon}, x ∈ l →
      ∃ ci, (⟨l⟩ : Ix.Kernel.Env .anon).find? x.name = some ci
  | c :: l, x, hx => by
    by_cases hc : c.name = x.name
    · refine ⟨c, ?_⟩
      rw [← hc]
      exact Ix.Kernel.Env.find?_cons_self c ⟨l⟩
    · rcases List.mem_cons.mp hx with rfl | hx
      · exact absurd rfl hc
      · obtain ⟨ci, hci⟩ := find?_some_of_mem hx
        exact ⟨ci, (Ix.Kernel.EnvExt.find?_cons_ne (env := (⟨l⟩ : Ix.Kernel.Env .anon)) hc).trans
          hci⟩

/-- **A key the prefix stores is stored with constants in front.** -/
theorem find?_append_some {env : Ix.Kernel.Env .anon} {k : Ix.Kernel.Key .anon}
    {ci : Ix.Kernel.ConstantInfo .anon} (h : env.find? k = some ci) :
    ∀ xs : List (Ix.Kernel.ConstantInfo .anon),
      ∃ ci', (⟨xs ++ env.consts⟩ : Ix.Kernel.Env .anon).find? k = some ci'
  | [] => ⟨ci, h⟩
  | c :: xs => by
    by_cases hc : c.name = k
    · refine ⟨c, ?_⟩
      rw [← hc]
      exact Ix.Kernel.Env.find?_cons_self c ⟨xs ++ env.consts⟩
    · obtain ⟨ci', h'⟩ := find?_append_some h xs
      exact ⟨ci', (Ix.Kernel.EnvExt.find?_cons_ne
        (env := (⟨xs ++ env.consts⟩ : Ix.Kernel.Env .anon)) hc).trans h'⟩

/-- **The stage stores what the prefix stores.** -/
theorem stage_find_of_env {env : Ix.Kernel.Env .anon} {formers : List Decl.Point.FormerRec}
    {k : Ix.Kernel.Key .anon} {ci : Ix.Kernel.ConstantInfo .anon} (h : env.find? k = some ci) :
    ∃ ci', (Decl.Point.stage env formers).find? k = some ci' :=
  find?_append_some h _

/-- **The stage stores each former at its name.** -/
theorem stage_find_of_mem {env : Ix.Kernel.Env .anon} {formers : List Decl.Point.FormerRec}
    {f : Decl.Point.FormerRec} (hf : f ∈ formers) :
    ∃ ci, (Decl.Point.stage env formers).find? f.cv.name = some ci := by
  have hm : f.stored ∈ (Decl.Point.stage env formers).consts :=
    List.mem_append_left _ (List.mem_reverse.mpr (List.mem_map_of_mem hf))
  exact find?_some_of_mem hm

/-! ## Telescopes ending in an application -/

theorem mkAppN_ne_forallE :
    ∀ (As : List Core.KExpr) (f : Core.KExpr), (∀ ty b m, f ≠ .forallE ty b m) →
      ∀ ty b m, Ix.Kernel.Expr.mkAppN f As ≠ .forallE ty b m
  | [], _, hf => hf
  | a :: As, f, _ => mkAppN_ne_forallE As (.app f a) (fun _ _ _ h => nomatch h)

theorem endsHead_of_notForall {T : Ix.Kernel.Key .anon} {us : List Ix.Kernel.Level} {n : Nat} :
    ∀ (e : Ix.Kernel.Expr .anon), (∀ ty b m, e ≠ .forallE ty b m) →
      e.getAppFn = .const T us → e.getAppArgs.length = n → Decl.Point.EndsHead T us n e
  | .forallE ty b m, hne, _, _ => (hne ty b m rfl).elim
  | .bvar _, _, h1, h2 | .fvar _ _, _, h1, h2 | .sort _, _, h1, h2 | .const _ _, _, h1, h2
  | .app _ _, _, h1, h2 | .lam _ _ _, _, h1, h2 | .letE _ _ _ _, _, h1, h2 | .lit _, _, h1, h2
  | .proj _ _ _, _, h1, h2 => And.intro h1 h2

/-- **A telescope of `k` binders into an application of `T` at `us` to `n` arguments ends in
that head.** -/
theorem endsHead_of_stripPis {T : Ix.Kernel.Key .anon} {us : List Ix.Kernel.Level} {n : Nat} :
    ∀ (k : Nat) (e : Ix.Kernel.Expr .anon)
      {bs : List (Ix.Kernel.Expr .anon × Ix.Kernel.BinderMeta)} {As : List Core.KExpr},
      e.stripPis k = some (bs, Ix.Kernel.Expr.mkAppN (.const T us) As) → As.length = n →
      Decl.Point.EndsHead T us n e
  | 0, e, bs, As, h, hn => by
    simp only [Ix.Kernel.Expr.stripPis, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    refine endsHead_of_notForall _
      (mkAppN_ne_forallE As (.const T us) (fun _ _ _ h => nomatch h)) ?_ ?_
    · rw [Core.getAppFn_mkAppN]
      rfl
    · rw [Decl.getAppArgs_mkAppN_const]
      exact hn
  | k + 1, .forallE ty b m, bs, As, h, hn => by
    simp only [Ix.Kernel.Expr.stripPis] at h
    cases hb : b.stripPis k with
    | none => rw [hb] at h; cases h
    | some p =>
      rw [hb] at h
      obtain ⟨bs', e'⟩ := p
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      exact endsHead_of_stripPis k b hb hn
  | k + 1, .bvar _, _, _, h, _ | k + 1, .fvar _ _, _, _, h, _ | k + 1, .sort _, _, _, h, _
  | k + 1, .const _ _, _, _, h, _ | k + 1, .app _ _, _, _, h, _ | k + 1, .lam _ _ _, _, _, h, _
  | k + 1, .letE _ _ _ _, _, _, h, _ | k + 1, .lit _, _, _, h, _
  | k + 1, .proj _ _ _, _, _, h, _ => by
    simp [Ix.Kernel.Expr.stripPis] at h

/-! ## The return-type check -/

/-- `KernelCheck::peel_n_foralls` on an exactly represented term strips `n` leading binders, at
the full field bound. -/
theorem peel_n_foralls_exact_bounded {κ : _root_.Address → Core.KKey} {d : Nat}
    {Γ : Nat → Core.KExpr} :
    ∀ (n : Nat) {k : Nat} {E : Core.KExpr} {pe r : SourceValue F} {h h' : Heap F}
      {cs : List (Call F)},
      n < 18446744069414584321 →
      Decl.TmExact κ d Γ h k E pe →
      ObsFn Core.W "KernelCheck::peel_n_foralls" [pe, .field (n : F)] h r h' cs →
      h' = h ∧ ∃ bs body,
        E.stripPis n = some (bs, body) ∧ bs.length = n ∧ Decl.TmExact κ d Γ h (k + n) body r
  | 0, k, E, pe, r, h, h', cs, _, hE, ev => by
    rcases Obs.«KernelCheck::peel_n_foralls».obs ev with
      ⟨_, rfl, rfl, _⟩ | ⟨_, _, _, _, _, hne, _, _, _, _⟩
    · exact ⟨rfl, [], E, rfl, rfl, by simpa using hE⟩
    · exact absurd rfl hne
  | m + 1, k, E, pe, r, h, h', cs, hlt, hE, ev => by
    rcases Obs.«KernelCheck::peel_n_foralls».obs ev with
      ⟨hv, _, _, _⟩ | ⟨w42, x_body, w43, cs62, v66, _, ld34, op87, ev64, _⟩
    · exact absurd hv (Decl.succ_field_ne_zero_bounded hlt)
    · obtain ⟨T, B, ℓ, rfl, _, hb, _⟩ := hE.forallE_of_load ld34
      rw [Decl.evalBinOp_sub_succ m op87] at ev64
      obtain ⟨hh, bs, body, hstrip, hlen, hbody⟩ :=
        peel_n_foralls_exact_bounded m (by omega) hb ev64
      refine ⟨hh, (T, Core.bmeta ℓ) :: bs, body, ?_, by simp [hlen], ?_⟩
      · simp [Ix.Kernel.Expr.stripPis, hstrip]
      · rw [show k + (m + 1) = k + 1 + m by omega]
        exact hbody

/-- **The return-type check reads the head of the residual.** On an exactly represented type,
`check_ctor_return_type` at block `b₀` and member index `i` peels `n_params + n_fields`
binders off a body that is an application of a constant to `n_params + n_indices` arguments,
and the constant is at the projection address of member `i` of the block at `b₀`
(`assert_return_head_is_parent` loads an inductive record of that block and member). -/
theorem check_ctor_return_type_head {κ : _root_.Address → Core.KKey} {Γ : Nat → Core.KExpr}
    {nP nIdx nF : Nat} {cty : Core.KExpr} {pcty pnl pblk r : SourceValue F} {i : F}
    {b₀ : Bytes.Address} {h h' : Heap F} {cs : List (Call F)}
    (hbound : Bounded cs) (hnPF : nP + nF < 18446744069414584321)
    (hnPI : nP + nIdx < 18446744069414584321)
    (hcty : Decl.TmExact κ 0 Γ h 0 cty pcty)
    (hblk : Bytes.RepAddressRef Core.addrTy h b₀ pblk)
    (ev : ObsFn Core.W "KernelCheck::check_ctor_return_type"
      [pcty, .field (nP : F), .field (nIdx : F), .field (nF : F), pnl, pblk, .field i]
      h r h' cs) :
    ∃ (cbs : List (Core.KExpr × Ix.Kernel.BinderMeta)) (a : Bytes.Address)
      (us : List Core.KLevel) (As : List Core.KExpr),
      cty.stripPis (nP + nF) =
        some (cbs, Ix.Kernel.Expr.mkAppN (.const (κ (Core.ixAddr a)) us) As) ∧
      As.length = nP + nIdx ∧ Core.ixAddr a = Core.iprjAddr (Core.ixAddr b₀) (ZMod.val i) := by
  match Obs.«KernelCheck::check_ctor_return_type».obs ev with
  | .run (m2 := m2) (m41 := m41) (x_head := xhd) (x_args := xargs) (m109 := m109)
      (m147 := m147) (op37 := op_pf) (ev14 := ev_peel) (ev54 := ev_sp) (ld90 := ld_hd)
      (ev121 := ev_par) (ev159 := ev_lvls) (ev207 := ev_len) (op229 := op_pi)
      (heq232 := heq_len) (hc397 := hc) .. =>
    subst hc
    rw [Decl.evalBinOp_add_nat nP nF op_pf] at ev_peel
    obtain ⟨hm2, cbs, body, hstrip, -, hbody⟩ :=
      peel_n_foralls_exact_bounded (nP + nF) hnPF hcty ev_peel
    subst hm2
    rw [Nat.zero_add] at hbody
    obtain ⟨hd, sp, H, As, htup, hH, hAs, rfl⟩ := Decl.collect_spine_exact_spec hbody ev_sp
    injection htup with hl; injection hl with h1 hl; injection hl with h2; subst h1 h2
    obtain ⟨a_hd, us_hd, rfl, ha_hd, -⟩ := hH.const_of_load ld_hd
    have hblk41 := Bytes.repAddressRef_heapMono₂ Core.addrTy ev_sp.heap_extends hblk
    have hpar : Core.ixAddr a_hd = Core.iprjAddr (Core.ixAddr b₀) (ZMod.val i) := by
      match Obs.«KernelCheck::assert_return_head_is_parent».obs ev_par with
      | .run (m2 := mp2) (p9 := p9) (cs15 := csp1) (x_ba := xba) (x_ii := xii)
          (ev17 := ev_ci) (ld11 := ld_ind) (ev112 := ev_aeq) (heq135 := heq1)
          (heq163 := heq_ii) (hc168 := hcp) .. =>
        subst hcp
        have hbcs : Bounded csp1 := RomBound.bounded_mono hbound (fun x hx => by simp [hx])
        subst heq_ii
        obtain ⟨-, -, -, -, -, -, b', -, -, -, -, -, -, -, -, -, hb', -⟩ :=
          L1.inductRecord_raw_tables_of_get_ci ev_ci hbcs ha_hd ld_ind
        have haddr := get_ci_induct_addr ev_ci hbcs ha_hd ld_ind hb'
        obtain ⟨hv_eq, -⟩ := Lib.address_eq_spec ev_aeq hb'
          (Bytes.repAddressRef_heapMono₂ Core.addrTy ev_ci.heap_extends hblk41)
        rw [heq1] at hv_eq
        by_cases hbe : b' = b₀
        · rw [haddr, hbe]
        · simp [hbe] at hv_eq
    have hAs147 := repList_heapMono₂ Core.kexprListEnum Decl.tmExact_heapMono₂
      (ev_par.heap_extends.trans ev_lvls.heap_extends) hAs
    obtain ⟨hv_len, -⟩ := Decl.klength_exact ev_len hAs147
    rw [Decl.evalBinOp_add_nat nP nIdx op_pi, hv_len] at heq_len
    have hAs_lt : As.length < 2 ^ 39 :=
      RomBound.bounded_length_lt hbound
        (c := ⟨Obs.Names.«Lists::length<&KernelTypes::KExprNode>», [xargs], m147⟩)
        (by simp) List.mem_cons_self hAs147
    have hAs_len : As.length = nP + nIdx :=
      Decl.nat_eq_of_field_eq_bounded (by omega) hnPI heq_len
    exact ⟨cbs, a_hd, us_hd, As, hstrip, hAs_len, hpar⟩

/-! ## The modeled constructor loop -/

/-- **One slot of the modeled constructor loop**: the load of the constructor and its header and
scope checks (`Assembly.CtorScopeRead`), the start of the loop extended to the slot, the sort
check of the type in the empty context, and the return-type check. -/
structure ModeledCtorRun (block : Bytes.Address) (indIndex ctorIndex : F)
    (params indices levels : Nat) (safety : F) (rc : SourceValue F) (start : Heap F)
    (calls : List (Call F)) extends
    Assembly.CtorScopeRead block indIndex ctorIndex safety params levels calls where
  fromStart : Heap.Extends start before
  sortBefore : Heap F
  sortResult : SourceValue F
  sortAfter : Heap F
  sortCalls : List (Call F)
  nilTypes : sortBefore = scopeAfter ++ [.construct Core.kexprListEnum "Nil" []]
  sortRun : ObsFn Core.W "KernelInfer::k_ensure_sort"
    [rc, ty, .ptr (.enum Core.kexprListEnum) scopeAfter.length]
    sortBefore sortResult sortAfter sortCalls
  sortSubset : ∀ call ∈ sortCalls, call ∈ calls
  retBefore : Heap F
  sortToRet : Heap.Extends sortAfter retBefore
  retResult : SourceValue F
  retAfter : Heap F
  retCalls : List (Call F)
  retRun : ObsFn Core.W "KernelCheck::check_ctor_return_type"
    [ty, .field (params : F), .field (indices : F), numFields, .field (levels : F), blockArg,
      .field indIndex] retBefore retResult retAfter retCalls
  retSubset : ∀ call ∈ retCalls, call ∈ calls

/-- **The modeled constructor loop runs every slot from its start.** -/
theorem modeled_ctor_runs {b : Bytes.Address} {n levels params indices : Nat} {i safety : F}
    (hn : n < 72057594037927936) {calls : List (Call F)} {rc : SourceValue F}
    {start : Heap F} :
    ∀ (m k : Nat) {blockArg r : SourceValue F} {h h' : Heap F} {cs : List (Call F)},
      m + k = n → Heap.Extends start h → (∀ cl ∈ cs, cl ∈ calls) →
      Bytes.RepAddressRef Core.addrTy h b blockArg →
      ObsFn Core.W "KernelCheck::check_modeled_ctors"
        [rc, .field (params : F), .field (indices : F), .field (n : F), .field (levels : F),
          blockArg, .field i, .field safety, .field (k : F)] h r h' cs →
      ∀ j, k ≤ j → j < n →
        Nonempty (ModeledCtorRun b i (j : F) params indices levels safety rc start calls) := by
  intro m
  induction m with
  | zero =>
    intro k blockArg r h h' cs hmk _ _ _ _ j hkj hjn
    omega
  | succ m ih =>
    intro k blockArg r h h' cs hmk hst hsub hbp ev j hkj hjn
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
        (x_c_unsafe := cus) (v318 := scopeResult) (m144 := scopeBefore) (m319 := scopeAfter)
        (cs329 := scopeCalls) (m387 := sortBefore) (v355 := sortResult) (m356 := sortAfter)
        (cs366 := sortCalls) (m400 := retBefore) (v429 := retResult) (m430 := retAfter)
        (cs440 := retCalls) (m500 := nextHeap) (cs540 := nextCalls) (v551 := nextIndex)
        (ev49 := loaded) (ld43 := tag) (ev154 := addressEq)
        (heq205 := memberChecked) (heq233 := slotChecked) (heq261 := levelsChecked)
        (heq289 := paramsChecked) (heq317 := safetyChecked) (ev331 := scopeRun)
        (hm395 := nilTypes) (ev368 := sortRun) (ev412 := safetyRun) (ev442 := retRun)
        (op621 := addition) (ev542 := nextRun) (hc623 := allCalls) .. =>
      by_cases hjk : j = k
      · subst hjk
        have retRun' : ObsFn Core.W "KernelCheck::check_ctor_return_type"
            [cty, .field (params : F), .field (indices : F), cnf, .field (levels : F), blockArg,
              .field i] retBefore retResult retAfter retCalls := by
          rw [paramsChecked] at retRun
          exact retRun
        exact ⟨{
          blockArg := blockArg, ptr := ptr, result := scopeResult
          before := h, after := after, scopeBefore := scopeBefore, scopeAfter := scopeAfter
          loadCalls := loadCalls, scopeCalls := scopeCalls
          nl := cnl, ty := cty, parent := cblk, member := cmi, slot := csl
          numParams := cnp, numFields := cnf, unsafeFlag := cus
          loaded := loaded, blockRep := hbp, tag := tag
          memberChecked := memberChecked, slotChecked := slotChecked
          levelsChecked := levelsChecked, paramsChecked := paramsChecked
          safetyChecked := safetyChecked
          extended := addressEq.heap_extends
          scopeRun := by simpa only [levelsChecked] using scopeRun
          loadSubset := fun call member => hsub call (by rw [allCalls]; simp [member])
          scopeMember := by
            rw [levelsChecked]
            exact hsub _ (by rw [allCalls]; simp)
          fromStart := hst
          sortBefore := sortBefore, sortResult := sortResult, sortAfter := sortAfter
          sortCalls := sortCalls
          nilTypes := nilTypes, sortRun := sortRun
          sortSubset := fun call member => hsub call (by rw [allCalls]; simp [member])
          retBefore := retBefore, sortToRet := safetyRun.heap_extends
          retResult := retResult, retAfter := retAfter, retCalls := retCalls
          retRun := retRun'
          retSubset := fun call member => hsub call (by rw [allCalls]; simp [member]) }⟩
      · have added := Decl.evalBinOp_add_nat k 1 addition
        subst nextIndex
        have nextMember : (⟨"KernelCheck::check_modeled_ctors",
            [rc, .field (params : F), .field (indices : F), .field (n : F), .field (levels : F),
              blockArg, .field i, .field safety, .field ((k + 1 : Nat) : F)], nextHeap⟩ :
              Call F) ∈ cs := by
          rw [allCalls]
          simp
        have hb := (ev.call_heap_bounds nextMember).1
        exact ih (k + 1) (by omega) (hst.trans hb)
          (fun cl hcl => hsub cl (by rw [allCalls]; simp [hcl]))
          (Bytes.repAddressRef_heapMono₂ Core.addrTy hb hbp) nextRun j (by omega) hjn

/-! ## The route of an `Induct` check, at its constructors -/

/-- **A successful `Induct` check took the native branch or ran the modeled constructor loop.**
Either `KernelModeled::block_is_modeled` was observed answering `0` on the record's block field,
within the check's calls (the native arm), or `KernelCheck::check_modeled_ctors` was observed
from slot `0` with the record's counts, block and member index, and safety argument `0` or the
record's flag (the two modeled arms), at a heap extending the check's input heap and within its
calls. -/
theorem induct_native_or_ctors {rc typePtr blockArg index safety addr result : SourceValue F}
    {params indices count levels : Nat} {h h' : Heap F} {calls : List (Call F)}
    (observed : ObsFn Core.W "KernelCheck::check_const"
      [rc, .construct Core.kciEnum "Induct"
        [.field (levels : F), typePtr, .field (params : F), .field (indices : F),
          .field (count : F), safety, blockArg, index], addr] h result h' calls) :
    (∃ (before after : Heap F) (cs : List (Call F)),
      ObsFn Core.W "KernelModeled::block_is_modeled" [blockArg] before (.field 0) after cs ∧
      Heap.Extends h before ∧ ∀ cl ∈ cs, cl ∈ calls) ∨
    ∃ (unsafeArg : SourceValue F) (before after : Heap F) (res : SourceValue F)
      (cs : List (Call F)),
      (unsafeArg = .field 0 ∨ unsafeArg = safety) ∧
      ObsFn Core.W "KernelCheck::check_modeled_ctors"
        [rc, .field (params : F), .field (indices : F), .field (count : F), .field (levels : F),
          blockArg, index, unsafeArg, .field 0] before res after cs ∧
      Heap.Extends h before ∧ ∀ cl ∈ cs, cl ∈ calls := by
  match Obs.«KernelCheck::check_const».obs observed with
  | .Axiom_n1 (hv37 := shape) ..
  | .Axiom_other_n0 (hv37 := shape) ..
  | .Axiom_other_other (hv37 := shape) ..
  | .Defn (hv269 := shape) ..
  | .Thm (hv526 := shape) ..
  | .Opaque (hv825 := shape) ..
  | .Quot (hv1076 := shape) .. =>
    injection shape with _ tag _
    exact absurd tag (by decide)
  | .Ctor_n0_n0 (hne1936 := notInduct) ..
  | .Ctor_n0_other (hne1936 := notInduct) ..
  | .Ctor_other_n0 (hne1936 := notInduct) ..
  | .Ctor_other_other (hne1936 := notInduct) ..
  | .Rec_n0 (hne1936 := notInduct) ..
  | .Rec_other (hne1936 := notInduct) .. =>
    exact (notInduct [_, _, _, _, _, _, _, _] rfl rfl).elim
  | .Induct_n0 (m1470 := before) (m1492 := after) (cs1503 := children)
      (hv1240 := fields) (ev1505 := modeRun) (hc1634 := allCalls) .. =>
    injection fields with _ _ fields
    simp only [List.cons.injEq, and_true] at fields
    obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := fields
    have member : (⟨"KernelModeled::block_is_modeled", [blockArg], before⟩ : Call F) ∈ calls := by
      rw [allCalls]; simp
    exact .inl ⟨before, after, children, modeRun, (observed.call_heap_bounds member).1,
      fun cl inside => by rw [allCalls]; simp [inside]⟩
  | .Induct_other_n0 (m1745 := before) (v1805 := res) (m1806 := after) (cs1816 := children)
      (hv1240 := fields) (ev1818 := ctorsRun) (hc1926 := allCalls) .. =>
    injection fields with _ _ fields
    simp only [List.cons.injEq, and_true] at fields
    obtain ⟨rfl, rfl, rfl, rfl, rfl, -, rfl, rfl⟩ := fields
    have member : (⟨"KernelCheck::check_modeled_ctors",
        [rc, .field (params : F), .field (indices : F), .field (count : F), .field (levels : F),
          blockArg, index, .field 0, .field 0], before⟩ : Call F) ∈ calls := by
      rw [allCalls]; simp
    exact .inr ⟨.field 0, before, after, res, children, .inl rfl, ctorsRun,
      (observed.call_heap_bounds member).1, fun cl inside => by rw [allCalls]; simp [inside]⟩
  | .Induct_other_other (m1745 := before) (v1805 := res) (m1806 := after) (cs1816 := children)
      (hv1240 := fields) (ev1818 := ctorsRun) (hc1935 := allCalls) .. =>
    injection fields with _ _ fields
    simp only [List.cons.injEq, and_true] at fields
    obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := fields
    have member : (⟨"KernelCheck::check_modeled_ctors",
        [rc, .field (params : F), .field (indices : F), .field (count : F), .field (levels : F),
          blockArg, index, safety, .field 0], before⟩ : Call F) ∈ calls := by
      rw [allCalls]; simp
    exact .inr ⟨safety, before, after, res, children, .inr rfl, ctorsRun,
      (observed.call_heap_bounds member).1, fun cl inside => by rw [allCalls]; simp [inside]⟩

/-! ## The constructors of member `i`, at the stage of the formers -/

/-- **The constructors of member `i` of a modeled block, at the stage of the formers.** From the
walked check of member `i` of the block `ms` at `B` (any number of inductive members) under the
walk's role context at the limit `n`, where the circuit's dispatch on the block is the modeled
branch (`hmod`): for every constructor slot `j` of the member, the constructor `ct` of the slot,
its reading `cty₀` and canonical annotation `cty'` over the step's store (`CtorRead`), its
parameter and level counts the member's, its front door at the stage of the formers
(`ConstantValRunJ` at `Decl.Point.stage env formers`, the prefix `env` with the formers in
front), and its annotated type a telescope ending in the member's former applied to
`n_params + n_indices` arguments (`EndsHead`).

Named inputs beyond those of `pointFormer_of_member`:
* `hS`: the run's store is a run store (every blob the run hashed is stored), so the
  constructors' types read;
* `hstage`: the core facts at the stage context (the prefix with the formers in front, keyed by
  what it stores, projections permitted where the prefix stores): the sort check of each
  constructor's type is read there;
* `hformers`: every member's former is among `formers` at its key (as `PointReads.formerAt`
  gives), so the members' addresses resolve at the stage;
* `hfreshC`, `hidC`: each constructor key is fresh at the stage and an input key (`.id`), the
  front door's freshness and its not-a-basis-name guard. -/
theorem pointCtors_of_member {calls : List (Call F)} {t : Ix.Kernel.RoleTable}
    (ht : t.check = .ok ()) {E₀ E : Ixon.Env} {bAddr B : _root_.Address} {cb : Ixon.Constant}
    {ms : Array Ixon.MutConst} {i : Nat} {ind : Ixon.Inductive} {n : Nat}
    {env : Ix.Kernel.Env .anon} {formers : List Decl.Point.FormerRec}
    (hS : LoadedReads.RunStore calls E₀) (hst : StepStore calls t E₀ E)
    (hblock : recordOf E B = some cb) (hmuts : cb.info = .muts ms)
    (hmem : ms[i]? = some (.indc ind))
    (hproj : recordOf E (Core.iprjAddr B i) = some (memberProjection B i (.indc ind)))
    (hinds : ∀ (k : Nat) (m : Ixon.MutConst), ms[k]? = some m →
      ∃ ind' : Ixon.Inductive, m = .indc ind')
    (hchk : MutsMemberCheckedAtFullAt calls bAddr t B ms i n)
    (hmod : ModeledAt E B)
    (hstage : Core.ScopedCoreFacts
      ((⟨E, Decl.Point.stage env formers, t, some n⟩ : Core.Ctx).stagedOver env))
    (hstored : Decl.UsedRefsStored t env cb)
    (hformers : ∀ (k : Nat) (ind' : Ixon.Inductive), ms[k]? = some (.indc ind') →
      ∃ f ∈ formers, f.cv.name = Core.keyOf t (Core.iprjAddr B k))
    (hfreshC : ∀ j < ind.ctors.size,
      (Decl.Point.stage env formers).find? (Core.keyOf t (Core.cprjAddr B i j)) = none)
    (hidC : ∀ j < ind.ctors.size, ∃ a, Core.keyOf t (Core.cprjAddr B i j) = .id a) :
    ∀ j < ind.ctors.size, ∃ (ct : Ixon.Constructor) (cty₀ cty' : Ix.Kernel.Expr .anon),
      ind.ctors[j]? = some ct ∧ CtorRead t E B cb ms i j ct cty₀ cty' ∧
      ct.params.toNat = ind.params.toNat ∧ ct.lvls = ind.lvls ∧
      Ix.Kernel.Semantics.ConstantValRunJ Ix.Kernel.Model.rulesJ (Decl.Point.stage env formers)
        ⟨Core.keyOf t (Core.cprjAddr B i j), List.range ct.lvls.toNat, cty₀⟩ cty' ∧
      ∃ us, Decl.Point.EndsHead (Core.keyOf t (Core.iprjAddr B i)) us
        (ind.params.toNat + ind.indices.toNat) cty' := by
  intro j hj
  have hbound : Bounded calls := (hst.good env none).2
  have hsize : ms.size < 2 ^ 39 := mutsMemberAt_size_lt hbound hchk
  have hi_lt : i < ms.size := (Array.getElem?_eq_some_iff.mp hmem).1
  have hi64 : i < UInt64.size := by
    have e : UInt64.size = 18446744073709551616 := rfl
    omega
  have hval_i : ZMod.val ((i : Nat) : F) = i :=
    ZMod.val_natCast_of_lt (by unfold Aiur.Library.U32.Goldilocks.modulus; omega)
  have hchkA := mutsMemberAt_checkedAt hbound hchk hmem
  obtain ⟨h_pre, m_chk, h'_chk, rc, ap, ptr, v, r_chk, cs_load, cs_chk, hrc_pre, hrc_m, ha_pre,
    ha_m, ev_ld, hcl_ld, hsub_ld, hld, ev_chk, hcl_chk, hsub_chk⟩ := hchkA
  obtain ⟨a, ha, hax⟩ := ha_pre
  have hgood : Core.Good ⟨E, env, t, some n⟩ calls := hst.good env (some n)
  have hg_ld : Core.Good ⟨E, env, t, some n⟩ cs_load := hgood.sub hsub_ld
  have hg_chk : Core.Good ⟨E, env, t, some n⟩ cs_chk := hgood.sub hsub_chk
  have hi' : (⟨i.toUInt64, B⟩ : Ixon.InductiveProj).idx.toNat = i := toUInt64_toNat_ct hi64
  -- the load of the member's projection record
  obtain ⟨rawBytes, c', hh, haddr, hex, htv, hres⟩ := L1.get_ci_block_trace_spec hg_ld.2 ha ev_ld
  have hrec : recordOf E (Core.ixAddr a) = some (memberProjection B i (.indc ind)) := by
    rw [hax, LoadedReads.memberAddr_indc]
    exact hproj
  obtain ⟨lc, hget, hdecA⟩ := LoadedReads.recordOf_inv hrec
  have hb0 : rawBytes = lc.rawBytes := Core.load_escape hget hg_ld.1 rawBytes hh haddr
  have hc : c' = memberProjection B i (.indc ind) := by
    rw [hb0, hdecA] at hex
    exact (Except.ok.inj hex).symm
  subst hc
  unfold L1.GetCIBlockTraceResult at hres
  have hinfo : (memberProjection B i (.indc ind)).info = .iPrj ⟨i.toUInt64, B⟩ := rfl
  rw [hinfo] at hres
  obtain ⟨hidx, blkBytes, cb', ms', ind', blobs, tree, plan, v₀, hhB, haB, hexB, hcb, hms,
    hhp, built, planned, hld₀, hraw, hlev⟩ := hres
  obtain ⟨lcB, hgetB, hdecB⟩ := LoadedReads.recordOf_inv hblock
  have hbB : blkBytes = lcB.rawBytes := Core.load_escape hgetB hg_ld.1 blkBytes hhB haB
  have hcB : cb' = cb := by
    rw [hbB, hdecB] at hexB
    exact (Except.ok.inj hexB).symm
  subst cb'
  have hmsEq : ms' = ms := Ixon.ConstantInfo.muts.inj (hcb.symm.trans hmuts)
  rw [hmsEq] at hms hraw
  rw [hi'] at hms hraw
  have hiEq : ind' = ind := by
    rw [Array.getElem?_toList, hmem] at hms
    exact (Ixon.MutConst.indc.inj (Option.some.inj hms)).symm
  subst ind'
  have hvv : v₀ = v := Except.ok.inj (hld₀.symm.trans hld)
  subst v₀
  obtain ⟨hlvls, hp56, hi56, hc56, hidx56, tyPtr, blkPtr, b, hb_eq, hb_rep, hv, rty⟩ := hraw
  subst hv
  have hbB' : Core.ixAddr b = B := hb_eq
  -- the route: the native branch is excluded, the modeled branch ran its constructor loop
  rcases induct_native_or_ctors ev_chk with ⟨mb, ma, mcs, modeRun, hextN, hsubN⟩ |
      ⟨uarg, mcb, mca, mcr, mccs, hu, ctorsRun, hextC, hsubC⟩
  · have hgN : Core.Good ⟨E, env, t, some n⟩ mcs := hg_chk.sub hsubN
    exact absurd (show NativeAt E B from ⟨blkPtr, mb, ma, mcs, b, modeRun, hgN.1, hgN.2,
      Bytes.repAddressRef_heapMono₂ Core.addrTy hextN hb_rep, hbB'⟩) hmod
  obtain ⟨s, rfl⟩ : ∃ s : F, uarg = .field s := by
    rcases hu with rfl | rfl
    · exact ⟨0, rfl⟩
    · exact ⟨_, rfl⟩
  have hsubC' : ∀ cl ∈ mccs, cl ∈ calls := fun cl hcl => hsub_chk cl (hsubC cl hcl)
  obtain ⟨st⟩ := modeled_ctor_runs (b := b) (start := mcb) hc56 ind.ctors.size 0 (by omega)
    (Heap.Extends.refl _) hsubC' (Bytes.repAddressRef_heapMono₂ Core.addrTy hextC hb_rep)
    ctorsRun j (Nat.zero_le _) hj
  -- the slot's record
  have hval_j : ZMod.val ((j : Nat) : F) = j :=
    ZMod.val_natCast_of_lt (by unfold Aiur.Library.U32.Goldilocks.modulus; omega)
  have hgL : Core.Good ⟨E, env, t, some n⟩ st.loadCalls := hgood.sub st.loadSubset
  obtain ⟨-, -, -, blkBytes₂, cb₂, ms₂, ind₂, ct, blobs₂, v₂, hhB₂, haB₂, hexB₂, -, hcb₂, hms₂,
    hct₂, hhp₂, hldv₂, hraw₂⟩ := L1.get_ci_cprj_spec hgL.2 st.blockRep st.loaded
  have hblock_b : recordOf E (Core.ixAddr b) = some cb := by
    rw [hbB']
    exact hblock
  have hbB₂ : blkBytes₂ = lcB.rawBytes :=
    Core.load_escape hgetB hgL.1 blkBytes₂ hhB₂ (haB₂.trans hbB')
  have hcB₂ : cb₂ = cb := by
    rw [hbB₂, hdecB] at hexB₂
    exact (Except.ok.inj hexB₂).symm
  subst cb₂
  have hmsEq₂ : ms₂ = ms := Ixon.ConstantInfo.muts.inj (hcb₂.symm.trans hmuts)
  subst ms₂
  rw [hval_i] at hms₂
  have hind₂ : ind₂ = ind := by
    rw [Array.getElem?_toList, hmem] at hms₂
    exact (Ixon.MutConst.indc.inj (Option.some.inj hms₂)).symm
  subst ind₂
  rw [hval_j] at hct₂
  have hctj : ind.ctors[j]? = some ct := by
    rw [← Array.getElem?_toList]
    exact hct₂
  have hvv₂ : v₂ = .construct Core.kciEnum "Ctor" [st.nl, st.ty, st.parent, st.member, st.slot,
      st.numParams, st.numFields, st.unsafeFlag] :=
    Except.ok.inj (hldv₂.symm.trans st.tag)
  obtain ⟨hclv, hccidx, hcpar, hcf, -, tyPtrC, blkPtrC, bC, -, -, hvC, rtyC⟩ := hraw₂
  rw [hvC] at hvv₂
  injection hvv₂ with _ _ hargs
  injection hargs with hnl hargs; injection hargs with hty_eq hargs
  injection hargs with _ hargs; injection hargs with _ hargs
  injection hargs with hsl hargs; injection hargs with hnp_eq hargs
  injection hargs with hnf_eq _
  have hlvN : ct.lvls.toNat = ind.lvls.toNat :=
    Decl.nat_eq_of_field_eq_bounded (by omega) (by omega) (hnl.trans st.levelsChecked)
  have hcidxN : ct.cidx.toNat = j :=
    Decl.nat_eq_of_field_eq_bounded (by omega) (by omega) (hsl.trans st.slotChecked)
  have hparN : ct.params.toNat = ind.params.toNat :=
    Decl.nat_eq_of_field_eq_bounded (by omega) (by omega) (hnp_eq.trans st.paramsChecked)
  -- the slot's reading
  have hblobE : ∀ x bs, (x, bs) ∈ blobs₂ → E.blobs.get? x = some bs := by
    intro x bs hm
    obtain ⟨hhx, hxa⟩ := hhp₂ (x, bs) hm
    have h0 := hS.blobs bs (Core.hashed_mono st.loadSubset hhx)
    rw [hxa] at h0
    exact hst.runBlob x bs h0
  obtain ⟨cty₀, hty⟩ := LoadedReads.exprReader_read_ok (blob := fun x => E.blobs.get? x) ht
    (param := id) (self := blockSelf t (Core.ixAddr b) ms) rtyC
    (LoadedReads.blockSelf_ok t (Core.ixAddr b) ms) hblobE
  have hmemF : ms[ZMod.val ((i : Nat) : F)]? = some (.indc ind) := by
    rw [hval_i]
    exact hmem
  have hctF : ind.ctors[ZMod.val ((j : Nat) : F)]? = some ct := by
    rw [hval_j]
    exact hctj
  obtain ⟨hlbb, hdef⟩ := LoadedReads.ctor_scope_closed (c := ⟨E, env, t, some n⟩) ht hgood
    st.toCtorScopeRead hblock_b hmuts hmemF hctF hty
  have hcidxF : ct.cidx.toNat = ZMod.val ((j : Nat) : F) := by
    rw [hval_j]
    exact hcidxN
  obtain ⟨tyPtr₂, blkPtr₂, b₂, cty', R', hld₂, -, -, -, -, -, hcanon, -, hann, -, hκ⟩ :=
    LoadedReads.ctor_load_canon ht hgL.1 hgL.2 st.blockRep st.loaded hblock_b hmuts hmemF hctF
      hcidxF hty hlbb hdef
  have htyP : tyPtr₂ = st.ty := by
    have e := Except.ok.inj (hld₂.symm.trans st.tag)
    injection e with _ _ hargs₂
    injection hargs₂ with _ hargs₂
    injection hargs₂ with e2 _
    exact e2
  -- the stage's keying resolves the type's cells
  let S := (⟨E, Decl.Point.stage env formers, t, some n⟩ : Core.Ctx).stagedOver env
  have hκused : ∀ i' ∈ usedRefIdxs cb, ∀ x, cb.refs.toList[i']? = some x →
      S.κ x = Core.keyOf t x ∧ Core.ProjPermitted S.κ x := by
    intro i' hi' x hx
    obtain ⟨ci, hci⟩ := hstored i' hi' x hx
    obtain ⟨ci', hci'⟩ := stage_find_of_env (formers := formers) hci
    exact ⟨Core.Ctx.stagedOver_key_of_find (c := ⟨E, Decl.Point.stage env formers, t, some n⟩)
        (pre := env) hci',
      Core.Ctx.stagedOver_projPermitted_of_find
        (c := ⟨E, Decl.Point.stage env formers, t, some n⟩) (pre := env) hci⟩
  have hκmem : ∀ (k : Nat) (ind' : Ixon.Inductive), ms[k]? = some (.indc ind') →
      S.κ (Core.iprjAddr B k) = Core.keyOf t (Core.iprjAddr B k) := by
    intro k ind' hk
    obtain ⟨f, hf, hfn⟩ := hformers k ind' hk
    obtain ⟨ci, hci⟩ := stage_find_of_mem (env := env) hf
    rw [hfn] at hci
    exact Core.Ctx.stagedOver_key_of_find (c := ⟨E, Decl.Point.stage env formers, t, some n⟩)
      (pre := env) hci
  have hκrec : ∀ x ∈ L1.blockRecurAddrs (Core.ixAddr b) ms.toList, S.κ x = Core.keyOf t x := by
    intro x hx
    obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hx
    obtain ⟨m, hm, hxm⟩ := LoadedReads.blockRecurAddrs_get hk
    obtain ⟨indk, rfl⟩ := hinds k m hm
    rw [LoadedReads.memberAddr_indc, hbB'] at hxm
    have hxm' : x = Core.iprjAddr B k := hxm
    rw [hxm']
    exact hκmem k indk hm
  have htmS := hκ S.κ hκused hκrec
  rw [htyP] at htmS
  -- the front door at the stage
  have e_after_scope : Heap.Extends st.after st.scopeBefore := st.extended
  have e_scope_sort : Heap.Extends st.scopeBefore st.sortBefore := by
    have e1 := st.scopeRun.heap_extends
    rw [st.nilTypes]
    exact e1.trans (Heap.Extends.snoc _ _)
  have hnlv : st.nl = .field ((List.range ct.lvls.toNat).length : F) := by
    rw [List.length_range]
    exact hnl.symm
  have hvS : Decl.ValRepExact S.κ st.scopeBefore st.nl st.ty
      ⟨Core.keyOf t (Core.cprjAddr B i j), List.range ct.lvls.toNat, cty'⟩ :=
    ⟨hnlv, by simpa using hclv, by simp, htmS.mono e_after_scope⟩
  have e_chk_sort : Heap.Extends m_chk st.sortBefore :=
    hextC.trans (st.fromStart.trans (st.loaded.heap_extends.trans
      (e_after_scope.trans e_scope_sort)))
  have hgS : Core.CoreGood S st.sortCalls :=
    Core.CoreGood.ofRaw ((hst.good (Decl.Point.stage env formers) (some n)).sub st.sortSubset)
      (fun _ _ => trivial)
  obtain ⟨cid, hcid⟩ := hidC j hj
  have htypes : Core.TypesRep S.κ (fun _ => default) st.sortBefore 0
      (.ptr (.enum Core.kexprListEnum) st.scopeAfter.length) := by
    rw [st.nilTypes]
    exact Decl.typesRep_alloc_nil _ _ _
  obtain ⟨checked, -, -, -, -, -, -, -⟩ :=
    Decl.constantValCheckJ_of_scoped (c := S) (Γ := fun _ => default)
      (cv := ⟨Core.keyOf t (Core.cprjAddr B i j), List.range ct.lvls.toNat, cty₀⟩)
      (cv' := ⟨Core.keyOf t (Core.cprjAddr B i j), List.range ct.lvls.toNat, cty'⟩)
      ⟨rfl, rfl, hann⟩ hvS hlbb (Assembly.memberReader_read_noFvar hty) (hfreshC j hj)
      (by rw [hcid]; exact (keyFree_id cid).1)
      (Decl.isProjFnShape_of_isBaseKey (Decl.isBaseKey_keyOf t _)) hstage.env.store
      (Decl.PosSortLift.of_range rfl) st.scopeRun e_scope_sort
      (hrc_m.toRCRep.mono e_chk_sort) htypes hstage.env hstage.loads hgS st.sortRun
  obtain ⟨type', hrunJ, hcv⟩ := checked
  have htype : type' = cty' := (congrArg Ix.Kernel.ConstantVal.type hcv).symm
  rw [htype] at hrunJ
  -- the return shape
  have e_after_ret : Heap.Extends st.after st.retBefore :=
    e_after_scope.trans (e_scope_sort.trans (st.sortRun.heap_extends.trans st.sortToRet))
  have htmR : Decl.TmExact S.κ 0 (fun _ => default) st.retBefore 0 cty' st.ty := by
    have h0 := (htmS 0 (fun _ => default)).mono e_after_ret
    rwa [Decl.posOf_range] at h0
  have hretRun := st.retRun
  rw [← hnf_eq] at hretRun
  have hgR : Core.Good ⟨E, env, t, some n⟩ st.retCalls := hgood.sub st.retSubset
  obtain ⟨cbs, a_hd, us, As, hstrip, hAs_len, hpar⟩ :=
    check_ctor_return_type_head hgR.2 (by omega) (by omega) htmR
      (Bytes.repAddressRef_heapMono₂ Core.addrTy (st.loaded.heap_extends.trans e_after_ret)
        st.blockRep) hretRun
  rw [hbB', hval_i] at hpar
  rw [hpar, hκmem i ind hmem] at hstrip
  have hty' : blockRead t E B cb ms ct.typ = .ok cty₀ := by
    rw [← hbB']
    exact hty
  rw [hval_i] at hcanon
  exact ⟨ct, cty₀, cty', hctj, ⟨hcidxN, hty', hlbb, hdef, hcanon⟩, hparN,
    UInt64.toNat_inj.mp hlvN, hrunJ, us, endsHead_of_stripPis _ _ hstrip hAs_len⟩

end IxVM.Refinement.Typing
