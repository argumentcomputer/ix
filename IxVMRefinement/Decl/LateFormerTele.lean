import IxVMRefinement.Decl.NativeRec
import IxVMRefinement.Core.Certs

/-! # The former's telescope in the native recursor comparison

`KernelCheck::nat_former_tele(rc, ty, k, types)` rebuilds the first `k` binders of the parent's
type as literal `Forall` nodes: at a `Forall` node it keeps the domain and recurses into the
body; at any other node it takes the weak head normal form, which must be a `Forall`. The
legacy specification (`nat_former_tele_syntactic_spec`) covers only a heap term whose first `k`
nodes are already `Forall`s. A stored former's type is a `∀`-telescope after its `let`s are
reduced, but its record may hold a `let` in the telescope; there the circuit calls `whnf`, whose
result reduces from a `∀` and so is that `∀` (`Red.forallE_eq`).

`scoped_nat_former_tele_spec`: under the scoped core facts, at any depth, for a term whose first
`k` binders are `∀`s (`stripPis`), the result represents the same term. -/

namespace IxVM.Refinement.Decl

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open IxVM.Refinement.Core
open IxVM.Refinement.KernelLevels (RepKLevel RepKLevelList repKLevel_heapMono₂)
open Ix.Kernel (Expr Level LevelParam)

set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-- **`nat_former_tele` keeps the term**: at depth `d` with the context `types`, a term whose
first `k` binders are `∀`s is represented by the result, with every `whnf` step it takes on a
non-`Forall` node read through the scoped core. -/
theorem scoped_nat_former_tele_spec {c : ScopedCtx} (hc : ScopedCoreFacts c) :
    ∀ (k : Nat) {d : Nat} {Γ : Nat → KExpr} {E : KExpr}
      {x_rc x_ty x_types r : SourceValue F} {h h' : Heap F} {cs : List (Call F)},
      k < 4294967296 → (E.stripPis k).isSome = true →
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
    | .n0 (hv14 := hv14) .. => exact absurd hv14 (succ_field_ne_zero (by omega))
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
      obtain ⟨e_rec, hrec⟩ := scoped_nat_former_tele_spec hc m (by omega) hsB'
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
        (x_m := x_m) (v229 := v229) (m239 := m239) (cs247 := cs247) (v252 := v252)
        (ld171 := ld171) (ev177 := ev_whnf) (he224 := hr) (hm223 := hh') (op281 := op281)
        (hm292 := hm284) (ev249 := ev_rec) (hc319 := hcs) .. =>
      have hgood_w : CoreGood c cs175 := hgood.sub (by rw [hcs]; intro x hx; simp [hx])
      obtain ⟨te', hte', hred⟩ :=
        scoped_core_whnf hrc hty hsc hc.env hc.loads hgood_w ev_whnf hE
      have hte_eq := Red.forallE_eq hred
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
      obtain ⟨e_rec, hrec⟩ := scoped_nat_former_tele_spec hc m (by omega) hsB'
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

end IxVM.Refinement.Decl
