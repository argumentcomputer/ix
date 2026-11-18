import IxVMRefinement.Decl.NativeRec
import IxVMRefinement.Callees.ProjAddr
import IxVMRefinement.Core.Certs
import IxVMRefinement.Assembly.GuardHeadRep
import Batteries.Tactic.OpenPrivate

/-! # The native recursor's generators at counts in the field's range

The specifications of the generators that `nat_rec_check` runs (`Decl/NativeRec.lean`) take
their counts below `2^32`, and their callers supply that from counts below `2^31`. No accepted
run gives those constants: the loads bound a parameter, index, field or constructor count below
`2^56`, and a telescope the run built below `2^39` (`Typing.RecArmRunBounds`,
`Decl.NatCtorLoadCountT`, `teleRep_length_lt`).

The constants are consumed in four ways only, and this module restates the lemma at each:

* **a natural's cast to the field is the natural**, which holds below the field's modulus
  `18446744069414584321`: the loop counters (`peel_n_foralls_tm_bounded`,
  `peel_n_foralls_rawTm_bounded`, `scoped_nat_former_tele_bounded`, `nat_ps_at_bounded`,
  `nat_replace_pis_bounded`), the member
  and constructor indices of a projection address (`projection_addr_ctor_bounded`), and the
  cut-off of a lift (`expr_lift_local_bounded`, `nat_idx_at_bounded`);
* **a positive counter is not zero in the field** (`succ_field_ne_zero_bounded`), below the
  modulus;
* **a represented bound variable** has an index below `2^63` (`Core.Tm.bvarLocal`;
  `tm_bvarLocal_nat_bounded`), so the binder depth the generators work at is asked below
  `2^63`, not `2^32`;
* **a lift's shift** is below `2^62` (`Subst.GSpec.expr_lift`), unchanged.

One hypothesis of the earlier chain is a fact of the run and not a count read off a record:
the length of the telescope of a recursive field. The run builds that telescope as a list and
passes it to `nat_tele_at`; `teleRep_length_lt` bounds it below `2^39` at that call, by the
bound on the run's memory.

The level-parameter builders (`nat_build_param_lvls_range_spec`, `build_rec_lvls_list_spec`)
keep `2^32`: that bound is the one `Convert::lvls_to_field` asserts.
-/

namespace IxVM.Refinement.Decl

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open IxVM.Refinement.Core
open IxVM.Refinement.KernelLevels (RepKLevel RepKLevelList repKLevel_heapMono₂)
open Ix.Kernel (ConstantInfo ConstantVal Declaration Expr Level LevelParam RecRule)

set_option maxHeartbeats 1600000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

/-! ## A represented bound variable -/

/-- A `BVar` cell holding the cast of a natural below `2^63` represents that local variable:
`tm_bvarLocal_nat` at the bound `Tm.bvarLocal` asks. -/
theorem tm_bvarLocal_nat_bounded {κ : _root_.Address → KKey} {d : Nat} {Γ : Nat → KExpr}
    {h : Heap F} {k addr n : Nat}
    (cell : h[addr]? = some (.construct kexprEnum "BVar" [.field (n : F)]))
    (hsm : n < 9223372036854775808) (hlt : n < k) :
    Tm κ d Γ h k (.bvar n) (.ptr (.enum kexprEnum) addr) := by
  have hval : ZMod.val (n : F) = n :=
    ZMod.val_natCast_of_lt (Nat.lt_trans hsm (by decide))
  rw [← hval]
  exact .bvarLocal cell (by rw [hval]; exact hsm) (by rw [hval]; exact hlt)

/-! ## The loop counters -/

/-- `KernelCheck::peel_n_foralls` on a `Tm` expression strips `n` leading `∀`-binders, for any
count in the field's range (`peel_n_foralls_tm_spec` asks `n < 2^39`). -/
theorem peel_n_foralls_tm_bounded {κ : _root_.Address → KKey} {d : Nat} {Γ : Nat → KExpr} :
    ∀ (n : Nat) {k : Nat} {E : KExpr} {pe r : SourceValue F} {h h' : Heap F} {cs : List (Call F)},
      n < 18446744069414584321 →
      Tm κ d Γ h k E pe →
      ObsFn W "KernelCheck::peel_n_foralls" [pe, .field (n : F)] h r h' cs →
      h' = h ∧ ∃ bs body,
        E.stripPis n = some (bs, body) ∧ bs.length = n ∧ Tm κ d Γ h (k + n) body r
  | 0, k, E, pe, r, h, h', cs, _, hE, ev => by
    rcases Obs.«KernelCheck::peel_n_foralls».obs ev with
      ⟨_, rfl, rfl, _⟩ | ⟨_, _, _, _, _, hne, _, _, _, _⟩
    · exact ⟨rfl, [], E, rfl, rfl, by simpa using hE⟩
    · exact absurd rfl hne
  | m + 1, k, E, pe, r, h, h', cs, hlt, hE, ev => by
    rcases Obs.«KernelCheck::peel_n_foralls».obs ev with
      ⟨hv, _, _, _⟩ | ⟨w42, x_body, w43, cs62, v66, _, ld34, op87, ev64, _⟩
    · exact absurd hv (succ_field_ne_zero_bounded hlt)
    · obtain ⟨T, B, ℓ, rfl, _, hb, _⟩ := hE.forallE_of_load ld34
      rw [evalBinOp_sub_succ m op87] at ev64
      obtain ⟨hh, bs, body, hstrip, hlen, hbody⟩ :=
        peel_n_foralls_tm_bounded m (by omega) hb ev64
      refine ⟨hh, (T, bmeta ℓ) :: bs, body, ?_, by simp [hlen], ?_⟩
      · simp [Expr.stripPis, hstrip]
      · rw [show k + (m + 1) = k + 1 + m by omega]
        exact hbody

/-- `KernelCheck::peel_n_foralls` on a `RawTm` expression, for any count in the field's range
(`peel_n_foralls_rawTm_spec` asks `n < 2^32`). -/
theorem peel_n_foralls_rawTm_bounded {κ : _root_.Address → KKey} {d : Nat} {Γ : Nat → KExpr} :
    ∀ (n : Nat) {k : Nat} {R E : KExpr} {pe r : SourceValue F} {h h' : Heap F}
      {cs : List (Call F)},
      n < 18446744069414584321 →
      RawTm κ d Γ h k R E pe →
      ObsFn W "KernelCheck::peel_n_foralls" [pe, .field (n : F)] h r h' cs →
      h' = h ∧ ∃ rbs ebs rbody ebody,
        R.stripPis n = some (rbs, rbody) ∧
        E.stripPis n = some (ebs, ebody) ∧
        RawTm κ d Γ h (k + n) rbody ebody r
  | 0, k, R, E, pe, r, h, h', cs, _, hRE, ev => by
    match Obs.«KernelCheck::peel_n_foralls».obs ev with
    | .n0 (he16 := hr) (he17 := hh) .. =>
      subst hr hh
      exact ⟨rfl, [], [], R, E, rfl, rfl, by rwa [Nat.add_zero]⟩
    | .other (hne19 := hne) .. =>
      exact absurd rfl hne
  | m + 1, k, R, E, pe, r, h, h', cs, hlt, hRE, ev => by
    match Obs.«KernelCheck::peel_n_foralls».obs ev with
    | .n0 (hv14 := hv) .. =>
      exact absurd hv (succ_field_ne_zero_bounded hlt)
    | .other (ld34 := ld34) (op87 := op87) (ev64 := ev64) .. =>
      obtain ⟨Rt, Rb, mR, T, B, ℓ, rfl, rfl, _, rb, _⟩ := hRE.forallE_of_load' ld34
      rw [evalBinOp_sub_succ m op87] at ev64
      obtain ⟨hh, rbs, ebs, rbody, ebody, hsR, hsE, hbody⟩ :=
        peel_n_foralls_rawTm_bounded m (by omega) rb ev64
      refine ⟨hh, (Rt, mR) :: rbs, (T, bmeta ℓ) :: ebs, rbody, ebody,
        by simp [Expr.stripPis, hsR], by simp [Expr.stripPis, hsE], ?_⟩
      rwa [show k + (m + 1) = k + 1 + m by omega]

/-- `KernelCheck::nat_ps_at(o, n)` builds `Ix.Kernel.structPsAt o n` at any local binder depth
`k` below `2^63` (`nat_ps_at_spec` asks `k < 2^32`). -/
theorem nat_ps_at_bounded {κ : _root_.Address → KKey} {d : Nat} {Γ : Nat → KExpr} :
    ∀ (n o k : Nat) {r : SourceValue F} {h h' : Heap F} {cs : List (Call F)},
      o + n ≤ k → k < 9223372036854775808 →
      ObsFn W "KernelCheck::nat_ps_at" [.field (o : F), .field (n : F)] h r h' cs →
      RepList kexprListEnum (fun h E p => Tm κ d Γ h k E p) h' (Ix.Kernel.structPsAt o n) r
  | 0, o, k, r, h, h', cs, _, _, ev => by
    match Obs.«KernelCheck::nat_ps_at».obs ev with
    | .n0 (he19 := hr) (hm18 := hh) .. =>
      subst hr hh
      exact .nil (by simp)
    | .other (hne24 := hne) .. =>
      exact absurd rfl hne
  | m + 1, o, k, r, h, h', cs, hle, hk, ev => by
    match Obs.«KernelCheck::nat_ps_at».obs ev with
    | .n0 (hv14 := hv) .. =>
      exact absurd hv (succ_field_ne_zero_bounded (by omega))
    | .other (v37 := v37) (m39 := m39) (v51 := v51) (x58 := x58) (m77 := m77) (v89 := v89)
        (he32 := hr) (hm31 := hh) (hm47 := hm47) (op73 := op73) (op65 := op65)
        (op110 := op110) (ev87 := ev87) .. =>
      subst hr hh
      have hx58 : x58 = .field ((o + (m + 1) : Nat) : F) := evalBinOp_add_nat o (m + 1) op73
      rw [hx58, show o + (m + 1) = (o + m) + 1 by omega] at op65
      have hv51 : v51 = .field ((o + m : Nat) : F) := evalBinOp_sub_succ (o + m) op65
      have hv89 : v89 = .field (m : F) := evalBinOp_sub_succ m op110
      rw [hv89] at ev87
      have htl := nat_ps_at_bounded (κ := κ) (d := d) (Γ := Γ) m o k (by omega) hk ev87
      have hhd_m39 : Tm κ d Γ m39 k (.bvar (o + m)) (.ptr (.enum kexprEnum) h.length) := by
        rw [hm47, hv51]
        exact tm_bvarLocal_nat_bounded (by simp) (by omega) (by omega)
      have ext_end : Heap.Extends m77
          (m77 ++ [.construct kexprListEnum "Cons"
            [.ptr (.enum kexprEnum) h.length, v37]]) := Heap.Extends.snoc _ _
      have hstruct : Ix.Kernel.structPsAt (md := .anon) o (m + 1) =
          .bvar (o + m) :: Ix.Kernel.structPsAt o m := by
        simp only [Ix.Kernel.structPsAt, List.range_succ_eq_map, List.map_cons, List.map_map]
        rw [show o + (m + 1) - 1 - 0 = o + m by omega]
        congr 1
        apply List.map_congr_left; intro j _; dsimp only [Function.comp_apply]
        exact congrArg Expr.bvar (by omega)
      rw [hstruct]
      exact .cons (by simp) ((hhd_m39.mono ev87.heap_extends).mono ext_end)
        (tmRepList_mono ext_end htl)

/-- `KernelCheck::nat_replace_pis` computes `Expr.replacePisPw` (`lam = 0`) or
`Expr.pisToLamsPw` (`lam ≠ 0`), for any count in the field's range (`nat_replace_pis_spec` asks
`cnt < 2^32`). -/
theorem nat_replace_pis_bounded {κ : _root_.Address → KKey} {d : Nat} {Γ : Nat → KExpr} :
    ∀ (cnt : Nat) {k : Nat} {ℓ : KLevel} {tele body : KExpr}
      {ppw ptele pb plam r : SourceValue F} {h h' : Heap F} {cs : List (Call F)},
      cnt < 18446744069414584321 →
      RepKLevel h ℓ ppw →
      Tm κ d Γ h k tele ptele →
      Tm κ d Γ h (k + cnt) body pb →
      ObsFn W "KernelCheck::nat_replace_pis"
        [ppw, .field (cnt : F), ptele, pb, plam] h r h' cs →
      ∃ out,
        (if plam = .field 0
         then Expr.replacePisPw ℓ.zeronessOf cnt tele body
         else Expr.pisToLamsPw ℓ.zeronessOf cnt tele body) = some out ∧
        Tm κ d Γ h' k out r
  | 0, k, _, _, body, _, _, pb, plam, r, h, h', cs, _, _, _, hbody, ev => by
    match Obs.«KernelCheck::nat_replace_pis».obs ev with
    | .n0 (he16 := hr) (he17 := hh) .. =>
      subst hr hh
      refine ⟨body, ?_, by rwa [Nat.add_zero] at hbody⟩
      by_cases hl : plam = .field 0 <;> simp [hl, Expr.replacePisPw, Expr.pisToLamsPw]
    | .other_n0 (hne19 := hne) .. => exact absurd rfl hne
    | .other_other (hne19 := hne) .. => exact absurd rfl hne
  | m + 1, k, ℓ, tele, body, ppw, ptele, pb, plam, r, h, h', cs, hlt, hpw, htele, hbody, ev => by
    have hne0 : (.field ((m + 1 : Nat) : F) : SourceValue F) ≠ .field 0 :=
      succ_field_ne_zero_bounded hlt
    match Obs.«KernelCheck::nat_replace_pis».obs ev with
    | .n0 (hv14 := hv) .. => exact absurd hv hne0
    | .other_n0 (x_ty := xty) (v54 := v54) (m55 := m55) (ld33 := ld) (op93 := op) (ev67 := ev')
        (hv129 := hlam0) (he134 := hr) (hm133 := hm) .. =>
      subst hlam0 hr hm
      obtain ⟨T, B, _, rfl, ht, hb, _⟩ := htele.forallE_of_load ld
      rw [evalBinOp_sub_succ m op] at ev'
      have hbody' : Tm κ d Γ h (k + 1 + m) body pb := by
        rwa [show k + 1 + m = k + (m + 1) by omega]
      obtain ⟨out', hout', htm'⟩ := nat_replace_pis_bounded m (by omega) hpw hb hbody' ev'
      simp only [↓reduceIte] at hout' ⊢
      have ext_end : Heap.Extends m55
          (m55 ++ [.construct kexprEnum "Forall" [xty, v54, ppw]]) := Heap.Extends.snoc _ _
      exact ⟨.forallE T out' (bmeta ℓ),
        by simp [Expr.replacePisPw, hout', bmeta],
        .forallE (by simp) ((ht.mono ev'.heap_extends).mono ext_end)
          (htm'.mono ext_end) (repKLevel_heapMono₂ (ev'.heap_extends.trans ext_end) hpw)⟩
    | .other_other (x_ty := xty) (v54 := v54) (m55 := m55) (ld33 := ld) (op93 := op) (ev67 := ev')
        (hne163 := hlam_ne) (he171 := hr) (hm170 := hm) .. =>
      subst hr hm
      obtain ⟨T, B, _, rfl, ht, hb, _⟩ := htele.forallE_of_load ld
      rw [evalBinOp_sub_succ m op] at ev'
      have hbody' : Tm κ d Γ h (k + 1 + m) body pb := by
        rwa [show k + 1 + m = k + (m + 1) by omega]
      obtain ⟨out', hout', htm'⟩ := nat_replace_pis_bounded m (by omega) hpw hb hbody' ev'
      simp only [ite_eq_right hlam_ne] at hout' ⊢
      have ext_end : Heap.Extends m55
          (m55 ++ [.construct kexprEnum "Lam" [xty, v54, ppw]]) := Heap.Extends.snoc _ _
      exact ⟨.lam T out' (bmeta ℓ),
        by simp [Expr.pisToLamsPw, hout', bmeta],
        .lam (by simp) ((ht.mono ev'.heap_extends).mono ext_end)
          (htm'.mono ext_end) (repKLevel_heapMono₂ (ev'.heap_extends.trans ext_end) hpw)⟩

/-- **`nat_former_tele` keeps the term**, for any binder count in the field's range
(`scoped_nat_former_tele_spec` asks `k < 2^32`): at depth `d` with the context `types`, a term
whose first `k` binders are `∀`s is represented by the result, with every head step it takes on
a non-`Forall` node read through the scoped core. -/
theorem scoped_nat_former_tele_bounded {c : ScopedCtx} (hc : ScopedCoreFacts c) :
    ∀ (k : Nat) {d : Nat} {Γ : Nat → KExpr} {E : KExpr}
      {x_rc x_ty x_types r : SourceValue F} {h h' : Heap F} {cs : List (Call F)},
      k < 18446744069414584321 → (E.stripPis k).isSome = true →
      RCRep c.t c.lim h x_rc → TypesRep c.κ Γ h d x_types → GhostScoped Γ d →
      CoreGood c cs → Tm c.κ d Γ h 0 E x_ty →
      ObsFn W "KernelCheck::nat_former_tele" [x_rc, x_ty, .field (k : F), x_types] h r h' cs →
      Heap.Extends h h' ∧ Tm c.κ d Γ h' 0 E r
  | 0, d, Γ, E, x_rc, x_ty, x_types, r, h, h', cs, _, _, _, _, _, _, hE, ev => by
    match Obs.«KernelCheck::nat_former_tele».obs ev with
    | .n0 (he16 := hr) (he17 := hh) .. =>
      subst hr hh
      exact ⟨Heap.Extends.refl _, hE⟩
    | .other_Forall (hne19 := hne) .. => exact absurd rfl hne
    | .other_other (hne19 := hne) .. => exact absurd rfl hne
  | m + 1, d, Γ, E, x_rc, x_ty, x_types, r, h, h', cs, hlt, hs, hrc, hty, hsc, hgood, hE, ev => by
    obtain ⟨T, B, mE, rfl⟩ : ∃ T B mE, E = .forallE T B mE := by
      cases E with
      | forallE T B mE => exact ⟨T, B, mE, rfl⟩
      | bvar _ | fvar _ _ | sort _ | const _ _ | app _ _ | lam _ _ _ | letE _ _ _ _
      | lit _ | proj _ _ _ => simp [Ix.Kernel.Expr.stripPis] at hs
    have hsB : (B.stripPis m).isSome = true := by
      simpa only [Ix.Kernel.Expr.stripPis, Option.isSome_map] using hs
    have hsB' : ((B.instantiate1 (.fvar d T)).stripPis m).isSome = true :=
      Specs.Whnf.stripPis_isSome_instantiate1 _ m B 0 hsB
    match Obs.«KernelCheck::nat_former_tele».obs ev with
    | .n0 (hv14 := hv14) .. => exact absurd hv14 (succ_field_ne_zero_bounded hlt)
    | .other_Forall (x_d := x_d) (x_b := x_b) (x_m := x_m) (v66 := v66) (m76 := m76)
        (cs84 := cs84) (v89 := v89) (ld34 := ld34) (he61 := hr) (hm60 := hh')
        (op118 := op118) (hm129 := hm121) (ev86 := ev_rec) (hc156 := hcs) .. =>
      obtain ⟨T', B', ℓ, hEq, hT, hB, hℓ⟩ := hE.forallE_of_load ld34
      injection hEq with hT_eq hB_eq hm_eq
      subst hT_eq hB_eq hm_eq
      rw [evalBinOp_sub_succ m op118] at ev_rec
      obtain ⟨e_push, htypes', hsc'⟩ := push_binder_types hT hty hsc
      subst hm121
      have hB_open := (hB.mono e_push).open_body (Ghost.extend_at Γ d T)
        (Ghost.extend_below Γ d T)
      have hgood_rec : CoreGood c cs84 := hgood.sub (by rw [hcs]; intro x hx; simp [hx])
      obtain ⟨e_rec, hrec⟩ := scoped_nat_former_tele_bounded hc m (by omega) hsB'
        (hrc.mono e_push) htypes' hsc' hgood_rec hB_open ev_rec
      have hclose := tm_close (Γ' := Γ) (fun j hj => (Ghost.extend_below Γ d T j hj).symm) hrec
      rw [abstract1_instantiate1_cancel T 0 (tm_fvarIdxLt hB) hB.looseBVarsBounded] at hclose
      subst hr hh'
      have e_out : Heap.Extends m76
          (m76 ++ [.construct "KernelTypes::KExprNode" "Forall" [x_d, v66, x_m]]) :=
        Heap.Extends.snoc _ _
      have e_all := e_push.trans (e_rec.trans e_out)
      refine ⟨e_all, ?_⟩
      exact .forallE (by simp) (hT.mono e_all) (hclose.mono e_out) (repKLevel_heapMono₂ e_all hℓ)
    | .other_other (m162 := m162) (p169 := p169) (cs175 := cs175) (x_d := x_d) (x_b := x_b)
        (x_m := x_m) (v220 := v229) (m230 := m239) (cs238 := cs247) (v243 := v252)
        (ld171 := ld171) (ev177 := ev_whnf) (he215 := hr) (hm214 := hh') (op272 := op281)
        (hm283 := hm284) (ev240 := ev_rec) (hc310 := hcs) .. =>
      have hgood_w : CoreGood c cs175 := hgood.sub (by rw [hcs]; intro x hx; simp [hx])
      obtain ⟨te', hte', hrigid⟩ := Core.GuardData.head_rep hc hgood_w hE ev_whnf
      have hte_eq := hrigid rfl
      subst hte_eq
      have e_w := ev_whnf.heap_extends
      obtain ⟨T', B', ℓ, hEq, hT, hB, hℓ⟩ := hte'.forallE_of_load ld171
      injection hEq with hT_eq hB_eq hm_eq
      subst hT_eq hB_eq hm_eq
      rw [evalBinOp_sub_succ m op281] at ev_rec
      obtain ⟨e_push, htypes', hsc'⟩ := push_binder_types hT (hty.mono e_w) hsc
      subst hm284
      have hB_open := (hB.mono e_push).open_body (Ghost.extend_at Γ d T)
        (Ghost.extend_below Γ d T)
      have hgood_rec : CoreGood c cs247 := hgood.sub (by rw [hcs]; intro x hx; simp [hx])
      obtain ⟨e_rec, hrec⟩ := scoped_nat_former_tele_bounded hc m (by omega) hsB'
        ((hrc.mono e_w).mono e_push) htypes' hsc' hgood_rec hB_open ev_rec
      have hclose := tm_close (Γ' := Γ) (fun j hj => (Ghost.extend_below Γ d T j hj).symm) hrec
      rw [abstract1_instantiate1_cancel T 0 (tm_fvarIdxLt hB) hB.looseBVarsBounded] at hclose
      subst hr hh'
      have e_out : Heap.Extends m239
          (m239 ++ [.construct "KernelTypes::KExprNode" "Forall" [x_d, v229, x_m]]) :=
        Heap.Extends.snoc _ _
      have e_all := e_w.trans (e_push.trans (e_rec.trans e_out))
      refine ⟨e_all, ?_⟩
      exact .forallE (by simp) ((hT.mono e_push).mono (e_rec.trans e_out))
        (hclose.mono e_out) (repKLevel_heapMono₂ (e_push.trans (e_rec.trans e_out)) hℓ)

/-! ## The address of a constructor projection -/

/-- `KernelCheck::projection_addr_ctor` at member and constructor indices in the field's range
(`projection_addr_ctor_spec` asks both below `2^32`; the function itself range-checks both
with `UInt64::from_field`). -/
theorem projection_addr_ctor_bounded {c : Ctx} {bp r : SourceValue F} {b : Bytes.Address}
    {idx cidx : Nat} {h h' : Heap F} {cs : List (Call F)}
    (hidx : idx < 18446744069414584321) (hcidx : cidx < 18446744069414584321)
    (hb : Bytes.RepAddressRef addrTy h b bp)
    (hgood : Good c cs)
    (ev : ObsFn W "KernelCheck::projection_addr_ctor"
      [.field (idx : F), .field (cidx : F), bp] h r h' cs) :
    ∃ a : Bytes.Address, Bytes.RepAddressRef addrTy h' a r ∧
      ixAddr a = cprjAddr (ixAddr b) idx cidx := by
  have hval_idx : ZMod.val (idx : F) = idx := ZMod.val_natCast_of_lt hidx
  have hval_cidx : ZMod.val (cidx : F) = cidx := ZMod.val_natCast_of_lt hcidx
  obtain ⟨a, ha, haddr⟩ := projection_addr_ctor_step (ScopedCtx.unrestricted c) ev
    (idx : F) (cidx : F) bp b rfl (CoreGood.unrestricted hgood) hb
  rw [hval_idx, hval_cidx] at haddr
  exact ⟨a, ha, haddr⟩

/-! ## The lift, at a cut-off in the field's range -/

open private openDummies closeDummies tm_openDummies tm_closeDummies closeDummies_openDummies
  from IxVMRefinement.Decl.NativeRec

/-- `KernelSubst::expr_lift(pe, shift, cut)` on a `Tm` term at `d = 0` and local binder depth
`k ≥ cut` produces `E.liftLooseBVars shift cut` at local binder depth `k + shift`, for any
cut-off in the field's range (`expr_lift_local_spec` asks `cut < 2^32`; the circuit's own
comparisons of a variable with the cut-off are read from the run by `Subst.GSpec.expr_lift`). -/
theorem expr_lift_local_bounded {κ : _root_.Address → KKey} {Γ₀ : Nat → KExpr}
    {k shift cut : Nat} {E : KExpr} {pe r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (hcut_le : cut ≤ k)
    (hshift_lt : shift < 4611686018427387904)
    (hcut_lt : cut < 18446744069414584321)
    (hbnd : IxVM.Consistency.Bounded cs)
    (hE : Tm κ 0 Γ₀ h k E pe)
    (ev : ObsFn W "KernelSubst::expr_lift" [pe, .field (shift : F), .field (cut : F)] h r h' cs) :
    Tm κ 0 Γ₀ h' (k + shift) (E.liftLooseBVars shift cut) r := by
  let m := k - cut
  have hk_eq : k = cut + m := by omega
  have hE₀ : Tm κ 0 (fun _ => .sort .zero) h (cut + m) E pe := by
    rw [← hk_eq]
    exact hE.congr_ghost (fun _ hj => by omega)
  have hop : Tm κ m (fun _ => .sort .zero) h cut (openDummies m 0 cut E) pe := by
    simpa using tm_openDummies m 0 cut hE₀
  have hval_s : ZMod.val (shift : F) = shift :=
    ZMod.val_natCast_of_lt (Nat.lt_trans hshift_lt (by decide))
  have hval_c : ZMod.val (cut : F) = cut :=
    ZMod.val_natCast_of_lt hcut_lt
  have hlift := SubstAux.gall κ .expr_lift _ _ _ _ _ ev pe (shift : F) (cut : F) rfl hbnd
    (by rw [hval_s]; exact hshift_lt) shift 0 (by rw [hval_s]; omega) m (fun _ => .sort .zero)
    (openDummies m 0 cut E) (by rwa [hval_c])
  rw [hval_c, Nat.add_zero] at hlift
  have hcl : Tm κ 0 (fun _ => .sort .zero) h' (cut + shift + m)
      (closeDummies m 0 (cut + shift) (openDummies m 0 cut E)) r :=
    tm_closeDummies m 0 (cut + shift) (by simpa using hlift)
  rw [closeDummies_openDummies shift m 0 cut (tm_fvarIdxLt hE₀) hE₀.looseBVarsBounded,
    show cut + shift + m = k + shift by omega] at hcl
  exact hcl.congr_ghost (fun _ hj => by omega)

/-- `KernelCheck::nat_idx_at` computes `Ix.Kernel.structIdxAt nF o i l m E`, moving local binder
depth from `k_base + i + m` to `k_base + o + nF + l + m`, at any target depth below `2^62`
(`nat_idx_at_spec` asks it below `2^32`). -/
theorem nat_idx_at_bounded {κ : _root_.Address → KKey} {Γ₀ : Nat → KExpr}
    {k_base nF o i l m : Nat} {E : KExpr} {pe r : SourceValue F}
    {h h' : Heap F} {cs : List (Call F)}
    (hi : i ≤ nF)
    (hlt : k_base + o + nF + l + m < 4611686018427387904)
    (hbnd : IxVM.Consistency.Bounded cs)
    (hE : Tm κ 0 Γ₀ h (k_base + i + m) E pe)
    (ev : ObsFn W "KernelCheck::nat_idx_at"
      [.field (nF : F), .field (o : F), .field (i : F), .field (l : F), .field (m : F), pe]
      h r h' cs) :
    Tm κ 0 Γ₀ h' (k_base + o + nF + l + m) (Ix.Kernel.structIdxAt nF o i l m E) r := by
  rcases Obs.«KernelCheck::nat_idx_at».obs ev with
    ⟨cs4, v7, v9, m11, cs19, v23, x38, x77, op53, op45, ev21, op92, op84, ev6, hc⟩
  subst hc
  rw [evalBinOp_sub_nat hi op53] at op45
  rw [evalBinOp_add_nat (nF - i) l op45] at ev21
  rw [evalBinOp_add_nat nF l op92] at op84
  rw [evalBinOp_add_nat (nF + l) m op84] at ev6
  have hbnd1 : IxVM.Consistency.Bounded cs19 :=
    RomBound.bounded_mono hbnd (fun x hx => by simp [hx])
  have hbnd2 : IxVM.Consistency.Bounded cs4 :=
    RomBound.bounded_mono hbnd (fun x hx => by simp [hx])
  have h1 := expr_lift_local_bounded (by omega) (by omega) (by omega) hbnd1 hE ev21
  have h1' : Tm κ 0 Γ₀ m11 (k_base + nF + l + m) (E.liftLooseBVars (nF - i + l) m) v7 := by
    rwa [show k_base + nF + l + m = (k_base + i + m) + (nF - i + l) by omega]
  have h2 := expr_lift_local_bounded (by omega) (by omega) (by omega) hbnd2 h1' ev6
  rwa [show k_base + o + nF + l + m = (k_base + nF + l + m) + o by omega]

/-! ## The telescope of a recursive field is a list of the run -/

/-- **A telescope a call of a bounded run takes as an argument has fewer than `2^39`
binders**: the run represents it as a list, and its memory holds fewer than `2^39` cells. This
is the bound on `Ix.Kernel.structFieldTeleOf` that the earlier chain asked of its caller
(`NatCtorInfoWfT.tele_lt`): `nat_field_tele` returns the telescope as a `TeleRep` list
(`nat_field_tele_spec`), and `nat_ih_pis` passes it on to `nat_tele_at`. -/
theorem teleRep_length_lt {calls : List (Call F)} (bounded : IxVM.Consistency.Bounded calls)
    {c : Call F} (called : c ∈ calls) {p : SourceValue F} (argument : p ∈ c.args)
    {κ : _root_.Address → KKey} {d : Nat} {Γ : Nat → KExpr} {k : Nat}
    {tele : List (KExpr × Ix.Kernel.BinderMeta)}
    (rep : TeleRep κ d Γ c.heap k tele p) : tele.length < 549755813888 :=
  RomBound.bounded_length_lt bounded called argument rep.toRepListTrue

end IxVM.Refinement.Decl
