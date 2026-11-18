import IxVMRefinement.Assembly.NativeAliasRecCheck
import IxVMRefinement.Assembly.GuardHeadTrace

/-! # The telescope builders follow the telescope walk

The three functions that rebuild a former's telescope are read here as the walks of
`NativeAliasOpenTrace`, from the observation of their runs and the head-trace specification of
`KernelGuard::head` (`Core.GuardData.head_trace`):

* `nat_former_tele_traced`: the recursor run's builder `KernelCheck::nat_former_tele` returns a
  pointer representing the term `OpenBinderTrace` builds from the term its input represents;
* `get_result_sort_level_traced`: the result-sort walk returns a level that is semantically
  equal to the level `OpenSortTrace` reaches;
* `former_tele_at_traced`: the block run's builder `KernelCheck::former_tele_at` returns a
  pointer representing a telescope into the given sort whose binder prefix is the one
  `OpenBinderTrace` builds.

No hypothesis says what the heap telescope is: each statement takes the observation of the run
and a term the input pointer represents, at the tolerance of the term seam.

Consequences. `NatFormerTeleTraced.of_run` discharges the premise of
`late_nat_rec_check_spec_registered` for every term, which gives
`late_nat_rec_check_spec_traced`: the native recursor comparison at the registered telescope
of a family declared at a type that needs head steps, with no premise about the builder.
`alias_block_runs_traced` produces what a registered family records from the two runs of the
block check, when the telescope constant's type is taken to be the term the builder's output
represents. -/

namespace IxVM.Refinement.Decl

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open IxVM.Refinement.Core
open IxVM.Refinement.KernelLevels (RepKLevel RepKLevelList repKLevel_heapMono₂)
open Ix.Kernel (Expr Level LevelParam ConstantVal ConstantInfo RecRule Declaration BinderMeta)
open Ix.Kernel.HeadDeltaBeta (Trace DefnLevelsClosed)

set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-! ## The recursor run's builder -/

/-- **`nat_former_tele` follows the telescope walk**: at depth `d` with the context `types`, on
a pointer representing `E`, the result represents the term the walk builds from `E` for `k`
binders. -/
theorem nat_former_tele_traced {c : ScopedCtx} (hc : ScopedCoreFacts c) :
    ∀ (k : Nat) {d : Nat} {Γ : Nat → KExpr} {E : KExpr}
      {x_rc x_ty x_types r : SourceValue F} {h h' : Heap F} {cs : List (Call F)},
      k < 4294967296 →
      RCRep c.t c.lim h x_rc → TypesRep c.κ Γ h d x_types → GhostScoped Γ d →
      CoreGood c cs → Tm c.κ d Γ h 0 E x_ty →
      ObsFn W "KernelCheck::nat_former_tele" [x_rc, x_ty, .field (k : F), x_types] h r h' cs →
      Heap.Extends h h' ∧ ∃ Y, OpenBinderTrace c.env d k E Y ∧ Tm c.κ d Γ h' 0 Y r
  | 0, d, Γ, E, x_rc, x_ty, x_types, r, h, h', cs, _, _, _, _, _, hE, ev => by
    match Obs.«KernelCheck::nat_former_tele».obs ev with
    | .n0 (he16 := hr) (he17 := hh) .. =>
      subst hr hh
      exact ⟨Heap.Extends.refl _, E, .done, hE⟩
    | .other_Forall (hne19 := hne) .. => exact absurd rfl hne
    | .other_other (hne19 := hne) .. => exact absurd rfl hne
  | m + 1, d, Γ, E, x_rc, x_ty, x_types, r, h, h', cs, hlt, hrc, hty, hsc, hgood, hE, ev => by
    match Obs.«KernelCheck::nat_former_tele».obs ev with
    | .n0 (hv14 := hv14) .. => exact absurd hv14 (succ_field_ne_zero (by omega))
    | .other_Forall (x_d := x_d) (x_b := x_b) (x_m := x_m) (v66 := v66) (m76 := m76)
        (cs84 := cs84) (v89 := v89) (ld34 := ld34) (he61 := hr) (hm60 := hh')
        (op118 := op118) (hm129 := hm121) (ev86 := ev_rec) (hc156 := hcs) .. =>
      obtain ⟨T, B, ℓ, rfl, hT, hB, hℓ⟩ := hE.forallE_of_load ld34
      rw [evalBinOp_sub_succ m op118] at ev_rec
      obtain ⟨e_push, htypes', hsc'⟩ := push_binder_types hT hty hsc
      subst hm121
      have hB_open := (hB.mono e_push).open_body (Ghost.extend_at Γ d T)
        (Ghost.extend_below Γ d T)
      have hgood_rec : CoreGood c cs84 := hgood.sub (by rw [hcs]; intro x hx; simp [hx])
      obtain ⟨e_rec, R, htraceR, hrec⟩ := nat_former_tele_traced hc m (by omega)
        (hrc.mono e_push) htypes' hsc' hgood_rec hB_open ev_rec
      have hclose := tm_close (Γ' := Γ) (fun j hj => (Ghost.extend_below Γ d T j hj).symm) hrec
      subst hr hh'
      have e_out : Heap.Extends m76
          (m76 ++ [.construct "KernelTypes::KExprNode" "Forall" [x_d, v66, x_m]]) :=
        Heap.Extends.snoc _ _
      have e_all := e_push.trans (e_rec.trans e_out)
      refine ⟨e_all, .forallE T (R.abstract1 d 0) (bmeta ℓ), .step .refl htraceR, ?_⟩
      exact .forallE (by simp) (hT.mono e_all) (hclose.mono e_out) (repKLevel_heapMono₂ e_all hℓ)
    | .other_other (m162 := m162) (p169 := p169) (cs175 := cs175) (x_d := x_d) (x_b := x_b)
        (x_m := x_m) (v220 := v229) (m230 := m239) (cs238 := cs247) (v243 := v252)
        (ld171 := ld171) (ev177 := ev_whnf) (he215 := hr) (hm214 := hh') (op272 := op281)
        (hm283 := hm284) (ev240 := ev_rec) (hc310 := hcs) .. =>
      have hgood_w : CoreGood c cs175 := hgood.sub (by rw [hcs]; intro x hx; simp [hx])
      obtain ⟨te', htr, -, hte'⟩ := Core.GuardData.head_trace hc hgood_w hE ev_whnf
      have e_w := ev_whnf.heap_extends
      obtain ⟨T, B, ℓ, rfl, hT, hB, hℓ⟩ := hte'.forallE_of_load ld171
      rw [evalBinOp_sub_succ m op281] at ev_rec
      obtain ⟨e_push, htypes', hsc'⟩ := push_binder_types hT (hty.mono e_w) hsc
      subst hm284
      have hB_open := (hB.mono e_push).open_body (Ghost.extend_at Γ d T)
        (Ghost.extend_below Γ d T)
      have hgood_rec : CoreGood c cs247 := hgood.sub (by rw [hcs]; intro x hx; simp [hx])
      obtain ⟨e_rec, R, htraceR, hrec⟩ := nat_former_tele_traced hc m (by omega)
        ((hrc.mono e_w).mono e_push) htypes' hsc' hgood_rec hB_open ev_rec
      have hclose := tm_close (Γ' := Γ) (fun j hj => (Ghost.extend_below Γ d T j hj).symm) hrec
      subst hr hh'
      have e_out : Heap.Extends m239
          (m239 ++ [.construct "KernelTypes::KExprNode" "Forall" [x_d, v229, x_m]]) :=
        Heap.Extends.snoc _ _
      have e_all := e_w.trans (e_push.trans (e_rec.trans e_out))
      refine ⟨e_all, .forallE T (R.abstract1 d 0) (bmeta ℓ), .step htr htraceR, ?_⟩
      exact .forallE (by simp) ((hT.mono e_push).mono (e_rec.trans e_out))
        (hclose.mono e_out) (repKLevel_heapMono₂ (e_push.trans (e_rec.trans e_out)) hℓ)

/-- The builder follows the head traces of every term. -/
theorem NatFormerTeleTraced.of_run {c : ScopedCtx} (hc : ScopedCoreFacts c) {n : Nat}
    (hn : n < 4294967296) (A : KExpr) : NatFormerTeleTraced c n A := by
  intro x_rc x_ty x_types r h h' cs hrc htypes hgood hA ev
  exact (nat_former_tele_traced hc n hn hrc htypes (ghostScoped_zero _) hgood hA ev).2

/-- **The native recursor comparison of a late recursor, at the registered telescope, with no
premise about the builder.** `pty₀` is the loaded stored former's type and `ttyReg` a telescope
with the traced binders of `pty₀`; the generated recursor type and rules are those of
`ttyReg`. -/
theorem late_nat_rec_check_spec_traced {c : ScopedCtx} (hc : ScopedCoreFacts c)
    (hall : ∀ cl, c.allowed cl)
    {κ₂ : _root_.Address → KKey} {find₂ : KKey → Option (ConstantInfo .anon)}
    (hkeep : ∀ x, c.κ x ≠ unresolvedKey → κ₂ x = c.κ x)
    (hwl₂ : WrapLoads c.toCtx κ₂ find₂)
    {cst : Ixon.Constant} {rc' : Ixon.Recursor}
    {T recC : KKey} {b₀ bT bRec bRB : Bytes.Address} {idx k nP nIdx : Nat} {large : Bool}
    {pty₀ ttyReg rec_ty₀ : KExpr}
    {ctors_info : List (KKey × Nat × KExpr × KExpr × List Nat)}
    {rls : List (RecRule .anon)}
    {x_rc x_nlvls x_ty x_n_mot x_n_min x_rules w_k w_u x_rec_blk w_ridx : SourceValue F}
    {x_pty w_p1 w_p2 w_pu x_block : SourceValue F}
    {x_addr x_parent_addr r : SourceValue F}
    {h h' : Heap F} {cs : List (Call F)}
    [Resolved (κ₂ (ixAddr bRec))]
    (hT_ind : ∃ cv caps, c.env.find? T = some (.indInfo cv caps))
    (hrecblk : Ix.Cert.recordAt c.E (ixAddr bRB) = some cst)
    (hcst : cst.info = .recr rc')
    (hT : c.κ (ixAddr bT) = T)
    (hκ₂_inj : ∀ a : Bytes.Address, κ₂ (ixAddr a) = T → a = bT)
    (hRec : κ₂ (ixAddr bRec) = recC)
    (hidx : idx < 4294967296)
    (hCres : ∀ i, i < ctors_info.length → c.κ (cprjAddr (ixAddr b₀) idx i) ≠ unresolvedKey)
    (hk_lt : k < 2147483648)
    (hnP_lt : nP < 2147483648)
    (hnIdx_lt : nIdx < 2147483648)
    (hnCtors_lt : ctors_info.length < 2147483648)
    (hnall_lt : nP + 1 + ctors_info.length + nIdx + 1 < 4294967296)
    (hlps_pty : pty₀.allLevelParamsDefined (List.range k) = true)
    (hwf_all : ∀ info ∈ ctors_info,
      NatCtorInfoWfT T k large nP nIdx ctors_info.length info)
    (hrls_len : rls.length = ctors_info.length)
    (hload : NatCtorLoadT c.κ b₀ idx k ctors_info x_block cs)
    (hhead : NatCtorRetHeadT b₀ idx nP ctors_info x_block cs)
    (hgood : CoreGood c cs)
    (hrc : RCRep c.t c.lim h x_rc)
    (hb₀_blk : Bytes.RepAddressRef addrTy h b₀ x_block)
    (hbRB : Bytes.RepAddressRef addrTy h bRB x_rec_blk)
    (hbT : Bytes.RepAddressRef addrTy h bT x_parent_addr)
    (hbRec : Bytes.RepAddressRef addrTy h bRec x_addr)
    (hpty : Tm c.κ 0 (fun _ => default) h 0 pty₀ x_pty)
    (hdef : DefnLevelsClosed c.env)
    (hreg : TracedBinders c.env (nP + nIdx) pty₀ ttyReg)
    (hrec_ty : Tm c.κ 0 (fun _ => default) h 0
      (posOf (if large then k :: List.range k else List.range k) rec_ty₀) x_ty)
    (hrules : RulesRep κ₂ h
      (if large then k :: List.range k else List.range k) 0 x_rules rls)
    (ev : ObsFn W "KernelCheck::nat_rec_check"
      [x_rc,
        .construct kciEnum "Rec"
          [x_nlvls, x_ty, .field (nP : F), .field (nIdx : F), x_n_mot, x_n_min,
            x_rules, w_k, w_u, x_rec_blk, w_ridx],
        x_addr,
        .construct kciEnum "Induct"
          [.field (k : F), x_pty, w_p1, w_p2, .field (ctors_info.length : F),
            w_pu, x_block, .field (idx : F)],
        x_parent_addr,
        .field ((if large then 1 else 0 : Nat) : F)]
      h r h' cs) :
    let rlps := if large then k :: List.range k else List.range k
    let elim := if large then k else 0
    let ctors₀ := ctors_info.map (fun info => (info.1, info.2.1, info.2.2.2.1, info.2.2.2.2))
    x_nlvls = .field (rlps.length : F) ∧
    x_n_mot = .field 1 ∧
    x_n_min = .field (ctors_info.length : F) ∧
    (∃ recTy,
      Ix.Kernel.structRecTyR T (List.range k) elim large nP nIdx ttyReg ctors₀ = some recTy ∧
      WrapRelSem c.env.find? recTy rec_ty₀) ∧
    (∀ a_d ls_d,
      ForallRightHeadLvls h a_d ls_d (nP + 1 + ctors_info.length + nIdx) x_ty →
      ls_d = (List.range k).map (fun i => Level.param ((if large then 1 else 0) + i))) ∧
    ∀ j (hlt : j < rls.length) (hj : j < ctors_info.length),
      (rls[j]'hlt).nfields = (ctors_info[j]'hj).2.1 ∧
      ∃ rhsG,
        Ix.Kernel.structRecRhsR T (List.range k) elim large nP nIdx ttyReg ctors₀
          recC (rlps.map .param) j = some rhsG ∧
        WrapRelSem find₂ rhsG (rls[j]'hlt).rhs := by
  exact late_nat_rec_check_spec_registered hc hall hkeep hwl₂
    (hT_ind := hT_ind) (hrecblk := hrecblk) (hcst := hcst) (hT := hT) (hκ₂_inj := hκ₂_inj)
    (hRec := hRec) (hidx := hidx) (hCres := hCres) (hk_lt := hk_lt) (hnP_lt := hnP_lt)
    (hnIdx_lt := hnIdx_lt) (hnCtors_lt := hnCtors_lt) (hnall_lt := hnall_lt)
    (hlps_pty := hlps_pty) (hwf_all := hwf_all) (hrls_len := hrls_len)
    (hload := hload) (hhead := hhead) (hgood := hgood) (hrc := hrc) (hb₀_blk := hb₀_blk)
    (hbRB := hbRB) (hbT := hbT) (hbRec := hbRec) (hpty := hpty) (hdef := hdef) (hreg := hreg)
    (hfollow := NatFormerTeleTraced.of_run hc (by omega) _)
    (hrec_ty := hrec_ty) (hrules := hrules) (ev := ev)

/-! ## The result-sort walk -/

/-- **`get_result_sort_level` follows the result-sort walk**: the returned level is
semantically equal to the level the walk reaches from the term the input represents. -/
theorem get_result_sort_level_traced {c : ScopedCtx} (hc : ScopedCoreFacts c) :
    ∀ (n : Nat) {d : Nat} {Γ : Nat → KExpr} {E : KExpr}
      {rc pe types r : SourceValue F} {h h' : Heap F} {cs : List (Call F)},
      n < 18446744069414584321 →
      RCRep c.t c.lim h rc → TypesRep c.κ Γ h d types → GhostScoped Γ d →
      CoreGood c cs → Tm c.κ d Γ h 0 E pe →
      ObsFn W "KernelCheck::get_result_sort_level" [rc, pe, .field (n : F), types] h r h' cs →
      ∃ (s ℓ : KLevel), OpenSortTrace c.env d n E s ∧ RepKLevel h' ℓ r ∧ LvEq s ℓ
  | 0, d, Γ, E, rc, pe, types, r, h, h', cs, _, hrc, hty, hsc, hgood, hE, ev => by
    match Obs.«KernelCheck::get_result_sort_level».obs ev with
    | .n0 (cs12 := cs12) (ev14 := ev_w) (ld55 := ld) (he69 := hr) (he70 := hh)
        (hc71 := hcs) .. =>
      subst hcs hr hh
      have hg1 : CoreGood c cs12 := hgood.sub (fun x hx => by simp [hx])
      obtain ⟨E', htr, -, hE'⟩ := Core.GuardData.head_trace hc hg1 hE ev_w
      obtain ⟨u, rfl, ℓ, hℓ, huℓ⟩ := hE'.sort_of_load ld
      exact ⟨u, ℓ, .done htr, hℓ, huℓ⟩
    | .other (hne73 := hne) .. => exact absurd rfl hne
  | m + 1, d, Γ, E, rc, pe, types, r, h, h', cs, hlt, hrc, hty, hsc, hgood, hE, ev => by
    match Obs.«KernelCheck::get_result_sort_level».obs ev with
    | .n0 (hv43 := hv) .. => exact absurd hv (succ_field_ne_zero_bounded hlt)
    | .other (cs12 := cs12) (x_body := xbody) (cs115 := cs2) (m152 := m3) (ev14 := ev_w)
        (ld88 := ld) (op149 := op) (hm160 := hm3) (ev117 := ev_rec) (hc180 := hcs) .. =>
      subst hcs
      have hg1 : CoreGood c cs12 := hgood.sub (fun x hx => by simp [hx])
      have hg2 : CoreGood c cs2 := hgood.sub (fun x hx => by simp [hx])
      obtain ⟨E', htr, -, hE'⟩ := Core.GuardData.head_trace hc hg1 hE ev_w
      obtain ⟨T, B, _, rfl, hT, hB, _⟩ := hE'.forallE_of_load ld
      have ext_w := ev_w.heap_extends
      obtain ⟨ext_push, hty', hsc'⟩ := push_binder_types hT (hty.mono ext_w) hsc
      rw [← hm3] at ext_push hty'
      have hB_open : Tm c.κ (d + 1) (Ghost.extend Γ d T) m3 0 (B.instantiate1 (.fvar d T))
          xbody :=
        (hB.open_body (Ghost.extend_at Γ d T) (Ghost.extend_below Γ d T)).mono ext_push
      rw [evalBinOp_sub_succ m op] at ev_rec
      obtain ⟨s, ℓ, hsort, hℓ, hsℓ⟩ := get_result_sort_level_traced hc m (by omega)
        (hrc.mono (ext_w.trans ext_push)) hty' hsc' hg2 hB_open ev_rec
      exact ⟨s, ℓ, .step htr hsort, hℓ, hsℓ⟩

/-! ## The block run's builder -/

theorem PrefixEq.abstract1 (d : Nat) : ∀ (n : Nat) {A B : KExpr} (k : Nat), PrefixEq n A B →
    PrefixEq n (A.abstract1 d k) (B.abstract1 d k)
  | 0, _, _, _, _ => trivial
  | n + 1, A, B, k, h => by
    obtain ⟨T, C, C', bm, rfl, rfl, hr⟩ := h.succ_view
    exact ⟨rfl, rfl, PrefixEq.abstract1 d n (k + 1) hr⟩

/-- Closing a variable keeps a telescope into a sort. -/
theorem stripPis_sort_abstract1 (d : Nat) (s : Level) :
    ∀ (n : Nat) (e : KExpr) (k : Nat), (∃ bs, e.stripPis n = some (bs, .sort s)) →
      ∃ bs, (e.abstract1 d k).stripPis n = some (bs, .sort s) := by
  intro n
  induction n with
  | zero =>
    intro e k ⟨bs, he⟩
    simp only [Ix.Kernel.Expr.stripPis, Option.some.injEq, Prod.mk.injEq] at he
    rw [he.2]
    exact ⟨[], rfl⟩
  | succ n ih =>
    intro e k ⟨bs, he⟩
    cases e <;> simp only [Ix.Kernel.Expr.stripPis, Option.map_eq_some_iff, reduceCtorEq] at he
    rename_i ty b m
    obtain ⟨⟨bs', R'⟩, hr, heq⟩ := he
    obtain ⟨-, rfl⟩ := Prod.mk.inj heq
    obtain ⟨bs'', hr'⟩ := ih b (k + 1) ⟨bs', hr⟩
    exact ⟨(ty.abstract1 d k, m) :: bs'', by
      simp [Ix.Kernel.Expr.abstract1, Ix.Kernel.Expr.stripPis, hr']⟩

/-- Two terms with one binder prefix and one residual after it are equal. -/
theorem PrefixEq.eq_of_stripPis : ∀ {n : Nat} {A B : KExpr}
    {bs bs' : List (KExpr × BinderMeta)} {R : KExpr},
    PrefixEq n A B → A.stripPis n = some (bs, R) → B.stripPis n = some (bs', R) → A = B
  | 0, A, B, bs, bs', R, _, ha, hb => by
    simp only [Ix.Kernel.Expr.stripPis, Option.some.injEq, Prod.mk.injEq] at ha hb
    rw [ha.2, hb.2]
  | n + 1, A, B, bs, bs', R, h, ha, hb => by
    obtain ⟨T, C, C', bm, rfl, rfl, hr⟩ := h.succ_view
    simp only [Ix.Kernel.Expr.stripPis, Option.map_eq_some_iff] at ha hb
    obtain ⟨⟨bs₁, R₁⟩, h₁, e₁⟩ := ha
    obtain ⟨⟨bs₂, R₂⟩, h₂, e₂⟩ := hb
    have hR₁ : R₁ = R := (Prod.mk.inj e₁).2
    have hR₂ : R₂ = R := (Prod.mk.inj e₂).2
    rw [hR₁] at h₁
    rw [hR₂] at h₂
    rw [PrefixEq.eq_of_stripPis hr h₁ h₂]

/-- **`former_tele_at` follows the telescope walk**: on a pointer representing `E`, with the
sort level pointer representing a level semantically equal to `s`, the result represents a
telescope into `Sort s` with `n` leading `∀`s whose binder prefix is the one the walk builds
from `E`. -/
theorem former_tele_at_traced {c : ScopedCtx} (hc : ScopedCoreFacts c) :
    ∀ (n : Nat) {d : Nat} {Γ : Nat → KExpr} {E : KExpr} {s ℓ : KLevel}
      {rc pe types ps r : SourceValue F} {h h' : Heap F} {cs : List (Call F)},
      n < 18446744069414584321 →
      RCRep c.t c.lim h rc → TypesRep c.κ Γ h d types → GhostScoped Γ d →
      CoreGood c cs → Tm c.κ d Γ h 0 E pe → RepKLevel h ℓ ps → LvEq s ℓ →
      ObsFn W "KernelCheck::former_tele_at" [rc, pe, .field (n : F), types, ps] h r h' cs →
      ∃ Z Y, Tm c.κ d Γ h' 0 Z r ∧ (∃ bs, Z.stripPis n = some (bs, .sort s)) ∧
        OpenBinderTrace c.env d n E Y ∧ PrefixEq n Y Z
  | 0, d, Γ, E, s, ℓ, rc, pe, types, ps, r, h, h', cs, _, hrc, hty, hsc, hgood, hE, hℓ, hs,
      ev => by
    match Obs.«KernelCheck::former_tele_at».obs ev with
    | .n0 (he19 := hr) (hm18 := hh) .. =>
      subst hr hh
      have cell : (h ++ [(.construct kexprEnum "Srt" [ps] : SourceValue F)])[h.length]? =
          some (.construct kexprEnum "Srt" [ps]) := by simp
      exact ⟨.sort s, E, .sort cell (hℓ.mono (Heap.Extends.snoc _ _)) hs, ⟨[], rfl⟩, .done,
        trivial⟩
    | .other_Forall (hne32 := hne) .. => exact absurd rfl hne
    | .other_other (hne32 := hne) .. => exact absurd rfl hne
  | n + 1, d, Γ, E, s, ℓ, rc, pe, types, ps, r, h, h', cs, hlt, hrc, hty, hsc, hgood, hE, hℓ,
      hs, ev => by
    match Obs.«KernelCheck::former_tele_at».obs ev with
    | .n0 (hv14 := hv) .. => exact absurd hv (succ_field_ne_zero_bounded hlt)
    | .other_Forall (x_d := xd) (x_b := xb) (x_m := xm) (v79 := vb) (m89 := mb) (cs97 := csb)
        (m135 := m1) (ld47 := ld) (he74 := hr) (hm73 := hh) (op132 := op) (hm143 := hm1)
        (ev99 := evb) (hc177 := hcs) .. =>
      subst hcs hr hh
      have hgb : CoreGood c csb := hgood.sub (fun x hx => by simp [hx])
      obtain ⟨T, B, ℓm, rfl, hT, hB, hℓm⟩ := hE.forallE_of_load ld
      obtain ⟨ext_push, hty', hsc'⟩ := push_binder_types hT hty hsc
      rw [← hm1] at ext_push hty'
      have hB_open : Tm c.κ (d + 1) (Ghost.extend Γ d T) m1 0 (B.instantiate1 (.fvar d T)) xb :=
        (hB.open_body (Ghost.extend_at Γ d T) (Ghost.extend_below Γ d T)).mono ext_push
      rw [evalBinOp_sub_succ n op] at evb
      obtain ⟨Zb, Yb, hZb, hstrip, hYb, hpre⟩ := former_tele_at_traced hc n (by omega)
        (hrc.mono ext_push) hty' hsc' hgb hB_open (hℓ.mono ext_push) hs evb
      have ext_b : Heap.Extends m1 mb := evb.heap_extends
      have ext_f : Heap.Extends mb
          (mb ++ [(.construct kexprEnum "Forall" [xd, vb, xm] : SourceValue F)]) :=
        Heap.Extends.snoc _ _
      have ext_all : Heap.Extends h
          (mb ++ [(.construct kexprEnum "Forall" [xd, vb, xm] : SourceValue F)]) :=
        ext_push.trans (ext_b.trans ext_f)
      have cell : (mb ++ [(.construct kexprEnum "Forall" [xd, vb, xm] : SourceValue F)])[mb.length]?
          = some (.construct kexprEnum "Forall" [xd, vb, xm]) := by simp
      obtain ⟨bs', hstrip'⟩ := stripPis_sort_abstract1 d s n Zb 0 hstrip
      exact ⟨.forallE T (Zb.abstract1 d 0) (bmeta ℓm), .forallE T (Yb.abstract1 d 0) (bmeta ℓm),
        .forallE cell (hT.mono ext_all) ((Tm.close (Ghost.extend_below Γ d T) hZb).mono ext_f)
          (hℓm.mono ext_all),
        ⟨(T, bmeta ℓm) :: bs', by simp [Ix.Kernel.Expr.stripPis, hstrip']⟩,
        .step .refl hYb, ⟨rfl, rfl, PrefixEq.abstract1 d n 0 hpre⟩⟩
    | .other_other (v36 := v0) (x_d := xd) (x_b := xb) (x_m := xm) (v241 := vb) (m251 := mb)
        (cs259 := csb) (cs196 := csw) (m183 := mw) (p190 := pw) (m297 := m1)
        (ld47 := ld) (hne178 := hnf) (ev198 := evw) (ld192 := ldw) (he236 := hr) (hm235 := hh)
        (op294 := op) (hm305 := hm1) (ev261 := evb) (hc339 := hcs) .. =>
      subst hcs hr hh
      have hgw : CoreGood c csw := hgood.sub (fun x hx => by simp [hx])
      have hgb : CoreGood c csb := hgood.sub (fun x hx => by simp [hx])
      obtain ⟨E', htr, -, hE'⟩ := Core.GuardData.head_trace hc hgw hE evw
      obtain ⟨T, B, ℓm, rfl, hT, hB, hℓm⟩ := hE'.forallE_of_load ldw
      have ext_w : Heap.Extends h mw := evw.heap_extends
      obtain ⟨ext_push, hty', hsc'⟩ := push_binder_types hT (hty.mono ext_w) hsc
      rw [← hm1] at ext_push hty'
      have hB_open : Tm c.κ (d + 1) (Ghost.extend Γ d T) m1 0 (B.instantiate1 (.fvar d T)) xb :=
        (hB.open_body (Ghost.extend_at Γ d T) (Ghost.extend_below Γ d T)).mono ext_push
      rw [evalBinOp_sub_succ n op] at evb
      obtain ⟨Zb, Yb, hZb, hstrip, hYb, hpre⟩ := former_tele_at_traced hc n (by omega)
        (hrc.mono (ext_w.trans ext_push)) hty' hsc' hgb hB_open
        (hℓ.mono (ext_w.trans ext_push)) hs evb
      have ext_b : Heap.Extends m1 mb := evb.heap_extends
      have ext_f : Heap.Extends mb
          (mb ++ [(.construct kexprEnum "Forall" [xd, vb, xm] : SourceValue F)]) :=
        Heap.Extends.snoc _ _
      have ext_all : Heap.Extends mw
          (mb ++ [(.construct kexprEnum "Forall" [xd, vb, xm] : SourceValue F)]) :=
        ext_push.trans (ext_b.trans ext_f)
      have cell : (mb ++ [(.construct kexprEnum "Forall" [xd, vb, xm] : SourceValue F)])[mb.length]?
          = some (.construct kexprEnum "Forall" [xd, vb, xm]) := by simp
      obtain ⟨bs', hstrip'⟩ := stripPis_sort_abstract1 d s n Zb 0 hstrip
      exact ⟨.forallE T (Zb.abstract1 d 0) (bmeta ℓm), .forallE T (Yb.abstract1 d 0) (bmeta ℓm),
        .forallE cell (hT.mono ext_all) ((Tm.close (Ghost.extend_below Γ d T) hZb).mono ext_f)
          (hℓm.mono ext_all),
        ⟨(T, bmeta ℓm) :: bs', by simp [Ix.Kernel.Expr.stripPis, hstrip']⟩,
        .step htr hYb, ⟨rfl, rfl, PrefixEq.abstract1 d n 0 hpre⟩⟩

/-- **What a registered family records, from the two runs of the block check.** The result-sort
walk and then the builder, each on a pointer representing the stored former's type `S`: the
builder's output represents a telescope `Z` into `Sort s` that has the traced binders of `S`,
and `s` is the level the result-sort walk reaches from `S`. With `Z` as the type of the
telescope constant and `s` as the family's sort, this is both fields of `FormerOpenTraceAt`. -/
theorem alias_block_runs_traced {c : ScopedCtx} (hc : ScopedCoreFacts c) {n : Nat} {S : KExpr}
    {rc₁ pe₁ types₁ rc₂ pe₂ types₂ ps r : SourceValue F} {h₁ h₁' h₂ h₂' : Heap F}
    {cs₁ cs₂ : List (Call F)} (hn : n < 18446744069414584321)
    (hrc₁ : RCRep c.t c.lim h₁ rc₁) (hty₁ : TypesRep c.κ (fun _ => default) h₁ 0 types₁)
    (hg₁ : CoreGood c cs₁) (hS₁ : Tm c.κ 0 (fun _ => default) h₁ 0 S pe₁)
    (evs : ObsFn W "KernelCheck::get_result_sort_level" [rc₁, pe₁, .field (n : F), types₁]
      h₁ ps h₁' cs₁)
    (hext : Heap.Extends h₁' h₂)
    (hrc₂ : RCRep c.t c.lim h₂ rc₂) (hty₂ : TypesRep c.κ (fun _ => default) h₂ 0 types₂)
    (hg₂ : CoreGood c cs₂) (hS₂ : Tm c.κ 0 (fun _ => default) h₂ 0 S pe₂)
    (evt : ObsFn W "KernelCheck::former_tele_at" [rc₂, pe₂, .field (n : F), types₂, ps]
      h₂ r h₂' cs₂) :
    ∃ (Z : KExpr) (s : KLevel) (bs : List (KExpr × BinderMeta)),
      Tm c.κ 0 (fun _ => default) h₂' 0 Z r ∧ Z.stripPis n = some (bs, .sort s) ∧
      TracedBinders c.env n S Z ∧ OpenSortTrace c.env 0 n S s := by
  obtain ⟨s, ℓ, hsort, hℓ, hsℓ⟩ :=
    get_result_sort_level_traced hc n hn hrc₁ hty₁ (ghostScoped_zero _) hg₁ hS₁ evs
  obtain ⟨Z, Y, hZ, ⟨bs, hstrip⟩, hY, hpre⟩ :=
    former_tele_at_traced hc n hn hrc₂ hty₂ (ghostScoped_zero _) hg₂ hS₂ (hℓ.mono hext) hsℓ evt
  exact ⟨Z, s, bs, hZ, hstrip, .intro hY hpre, hsort⟩

end IxVM.Refinement.Decl
