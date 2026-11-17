import IxVMRefinement.Assembly.NativeAliasTeleWalk

/-! # The head-normalized telescope of an actual late recursor check

`nat_former_tele_open_spec` handles both the syntactic and head-normalizing paths of
`nat_former_tele`. It produces the output reading, its binder-cell spine and the identical
prefix wherever the input already has syntactic binders. The zero case retains the residual;
it does not insert a sort. No equality with a telescope from another run is assumed.
-/

namespace IxVM.Refinement.Decl

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open IxVM.Refinement.Core
open IxVM.Refinement.KernelLevels
open Ix.Kernel (Expr)

set_option maxHeartbeats 3200000
set_option maxRecDepth 100000
set_option linter.unusedVariables false

/-- Actual telescope construction, including its head-normalizing branches. -/
theorem nat_former_tele_open_spec {c : ScopedCtx} :
    ∀ (n : Nat) {d : Nat} {Γ : Nat → KExpr} {E : KExpr}
      {rc pe types r : SourceValue F} {h h' : Heap F} {cs : List (Call F)},
      n < 18446744069414584321 →
      RCRep c.t c.lim h rc →
      TypesRep c.κ Γ h d types →
      GhostScoped Γ d →
      CoreEnvFacts c.toCtx →
      ScopedLoadFacts c →
      CoreGood c cs →
      Tm c.κ d Γ h 0 E pe →
      ObsFn W "KernelCheck::nat_former_tele" [rc, pe, .field (n : F), types] h r h' cs →
      (∃ R, Tm c.κ d Γ h' 0 R r) ∧ ForallCells h' n r ∧
        ∀ (m : Nat) (H : Heap F), m ≤ n → Heap.Extends h' H → ForallCells H m pe →
          TeleCells H m pe r
  | 0, d, Γ, E, rc, pe, types, r, h, h', cs, _, hrc, hty, hsc, hef, hlf, hgood, hE,
      ev => by
    match Obs.«KernelCheck::nat_former_tele».obs ev with
    | .n0 (he16 := hr) (he17 := hh) .. =>
      subst hr hh
      refine ⟨⟨E, hE⟩, trivial, ?_⟩
      intro m H hm _ _
      obtain rfl : m = 0 := by omega
      trivial
    | .other_Forall (hne19 := hne) .. => exact absurd rfl hne
    | .other_other (hne19 := hne) .. => exact absurd rfl hne
  | n + 1, d, Γ, E, rc, pe, types, r, h, h', cs, hlt, hrc, hty, hsc, hef, hlf, hgood, hE,
      ev => by
    match Obs.«KernelCheck::nat_former_tele».obs ev with
    | .n0 (hv14 := hv) .. => exact absurd hv (succ_field_ne_zero_bounded hlt)
    | .other_Forall (x_d := xd) (x_b := xb) (x_m := xm) (v66 := vb) (m76 := mb) (cs84 := csb)
        (m121 := m1) (ld34 := ld) (he61 := hr) (hm60 := hh) (op118 := op) (hm129 := hm1)
        (ev86 := evb) (hc156 := hc) .. =>
      subst hc hr hh
      have hgb : CoreGood c csb := hgood.sub (fun x hx => by simp [hx])
      obtain ⟨T, B, ℓm, rfl, hT, hB, hℓm⟩ := hE.forallE_of_load ld
      obtain ⟨ext_push, hty', hsc'⟩ := push_binder_types hT hty hsc
      rw [← hm1] at ext_push hty'
      have hB_open : Tm c.κ (d + 1) (Ghost.extend Γ d T) m1 0 (B.instantiate1 (.fvar d T)) xb :=
        (hB.open_body (Ghost.extend_at Γ d T) (Ghost.extend_below Γ d T)).mono ext_push
      rw [evalBinOp_sub_succ n op] at evb
      obtain ⟨⟨Rb, hRb⟩, hshape, hcells⟩ := nat_former_tele_open_spec n (by omega)
        (hrc.mono ext_push) hty' hsc' hef hlf hgb hB_open evb
      have ext_b : Heap.Extends m1 mb := evb.heap_extends
      have ext_f : Heap.Extends mb
          (mb ++ [(.construct kexprEnum "Forall" [xd, vb, xm] : SourceValue F)]) :=
        Heap.Extends.snoc _ _
      have ext_all : Heap.Extends h
          (mb ++ [(.construct kexprEnum "Forall" [xd, vb, xm] : SourceValue F)]) :=
        ext_push.trans (ext_b.trans ext_f)
      have cell : (mb ++ [(.construct kexprEnum "Forall" [xd, vb, xm] : SourceValue F)])[mb.length]?
          = some (.construct kexprEnum "Forall" [xd, vb, xm]) := by simp
      refine ⟨⟨.forallE T (Rb.abstract1 d 0) (bmeta ℓm),
          .forallE cell (hT.mono ext_all) ((Tm.close (Ghost.extend_below Γ d T) hRb).mono ext_f)
            (hℓm.mono ext_all)⟩,
        ⟨xd, vb, xm, loadValue_snoc_cell mb "Forall" [xd, vb, xm], hshape.mono ext_f⟩, ?_⟩
      intro m H hm hH hfc
      cases m with
      | zero => trivial
      | succ m =>
        obtain ⟨d', b', bm', hl', hfc'⟩ := hfc
        have hl := (ext_all.trans hH).loadValue_eq ld
        rw [hl] at hl'
        injection hl' with hl''
        injection hl'' with _ _ hargs
        simp only [List.cons.injEq, and_true] at hargs
        obtain ⟨rfl, rfl, rfl⟩ := hargs
        exact ⟨xd, xb, vb, xm, hl, hH.loadValue_eq
          (loadValue_snoc_cell mb "Forall" [xd, vb, xm]),
          hcells m H (by omega) (ext_f.trans hH) hfc'⟩
    | .other_other (v23 := v0) (x_d := xd) (x_b := xb) (x_m := xm) (v229 := vb) (m239 := mb)
        (cs247 := csb) (cs175 := csw) (m162 := mw) (p169 := pw) (m284 := m1)
        (ld34 := ld) (hne157 := hnf) (ev177 := evw) (ld171 := ldw) (he224 := hr) (hm223 := hh)
        (op281 := op) (hm292 := hm1) (ev249 := evb) (hc319 := hc) .. =>
      subst hc hr hh
      have hgw : CoreGood c csw := hgood.sub (fun x hx => by simp [hx])
      have hgb : CoreGood c csb := hgood.sub (fun x hx => by simp [hx])
      obtain ⟨E', hE', hred⟩ := scoped_core_whnf hrc hty hsc hef hlf hgw evw hE
      obtain ⟨T, B, ℓm, rfl, hT, hB, hℓm⟩ := hE'.forallE_of_load ldw
      have ext_w : Heap.Extends h mw := evw.heap_extends
      obtain ⟨ext_push, hty', hsc'⟩ := push_binder_types hT (hty.mono ext_w) hsc
      rw [← hm1] at ext_push hty'
      have hB_open : Tm c.κ (d + 1) (Ghost.extend Γ d T) m1 0 (B.instantiate1 (.fvar d T)) xb :=
        (hB.open_body (Ghost.extend_at Γ d T) (Ghost.extend_below Γ d T)).mono ext_push
      rw [evalBinOp_sub_succ n op] at evb
      obtain ⟨⟨Rb, hRb⟩, hshape, -⟩ := nat_former_tele_open_spec n (by omega)
        (hrc.mono (ext_w.trans ext_push)) hty' hsc' hef hlf hgb hB_open evb
      have ext_b : Heap.Extends m1 mb := evb.heap_extends
      have ext_f : Heap.Extends mb
          (mb ++ [(.construct kexprEnum "Forall" [xd, vb, xm] : SourceValue F)]) :=
        Heap.Extends.snoc _ _
      have ext_all : Heap.Extends mw
          (mb ++ [(.construct kexprEnum "Forall" [xd, vb, xm] : SourceValue F)]) :=
        ext_push.trans (ext_b.trans ext_f)
      have cell : (mb ++ [(.construct kexprEnum "Forall" [xd, vb, xm] : SourceValue F)])[mb.length]?
          = some (.construct kexprEnum "Forall" [xd, vb, xm]) := by simp
      refine ⟨⟨.forallE T (Rb.abstract1 d 0) (bmeta ℓm),
          .forallE cell (hT.mono ext_all) ((Tm.close (Ghost.extend_below Γ d T) hRb).mono ext_f)
            (hℓm.mono ext_all)⟩,
        ⟨xd, vb, xm, loadValue_snoc_cell mb "Forall" [xd, vb, xm], hshape.mono ext_f⟩, ?_⟩
      intro m H hm hH hfc
      cases m with
      | zero => trivial
      | succ m =>
        exfalso
        obtain ⟨d', b', bm', hl', -⟩ := hfc
        have hl := ((ext_w.trans ext_all).trans hH).loadValue_eq ld
        rw [hl] at hl'
        injection hl' with hv
        exact hnf [d', b', bm'] rfl hv


end IxVM.Refinement.Decl
