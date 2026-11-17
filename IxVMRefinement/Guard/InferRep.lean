import IxVMRefinement.Assembly.GuardHeadRep
import IxVMRefinement.Decl.Common
import IxVMRefinement.Infer.Close
import IxVMRefinement.Guard.Levels

/-! # Representation and checked zero-signature evidence for the field classifier

The structural classifier produces represented data in a scoped context. This is not a typing
judgement for its predicted type. The ordinary sort check remains separate and its explicit
signature comparison is what relates the predicted and actually inferred zero-sets.
-/

namespace IxVM.Refinement.Core.GuardData

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library
open IxVM (F)
open IxVM.Refinement.KernelLevels (RepKLevel RepKLevelList)

private theorem infer_shape_rep_go {c : ScopedCtx} (hc : ScopedCoreFacts c) :
    ∀ fuel : Nat, ∀ {d : Nat} {Γ : Nat → KExpr} {E : KExpr}
      {p ctx budget r : SourceValue F} {h h' : Heap F} {cs : List (Call F)},
      cs.length ≤ fuel → CoreGood c cs → c.types Γ h d ctx → Tm c.κ d Γ h 0 E p →
      ObsFn W "KernelGuard::infer_shape" [p, ctx, budget] h r h' cs →
      ∃ T, Tm c.κ d Γ h' 0 T r := by
  intro fuel
  induction fuel using Nat.strong_induction_on with
  | h fuel ih =>
    intro d Γ E p ctx budget r h h' cs hlen hg hctx hE ev
    match Obs.«KernelGuard::infer_shape».obs ev with
    | .n0 (heq40 := he) .. | .other_other (heq732 := he) .. =>
      exact (zero_ne_one (Value.field.inj he)).elim
    | .other_BVar (cs76 := calls) (ld60 := ld) (ev78 := lookup) (hc95 := hall) .. =>
      obtain ⟨i, rfl, _, _⟩ := hE.bvar_of_load ld
      have hsub : ∀ cl ∈ calls, cl ∈ cs := by intro cl hm; rw [hall]; simp [hm]
      have hs := Registry.induction c (scoped_steps c hc) (.infer .types_lookup)
        _ _ _ _ _ lookup
      exact ⟨_, (hs ctx i rfl (hg.sub hsub) d Γ hctx).2⟩
    | .other_Srt (x_u := lp) (ld60 := ld) (he112 := hr) (hm111 := hh) (hm126 := hm) .. =>
      obtain ⟨u, rfl, l, hl, _⟩ := hE.sort_of_load ld
      subst hr hh hm
      have e1 := Heap.Extends.snoc h (.construct klevelEnum "Succ" [lp])
      have hs : RepKLevel (h ++ [.construct klevelEnum "Succ" [lp]]) (.succ l)
          (.ptr (.enum klevelEnum) h.length) :=
        .succ List.getElem?_concat_length (hl.mono e1)
      exact ⟨.sort (.succ l), .sort List.getElem?_concat_length
        (hs.mono (Heap.Extends.snoc _ _)) (LvEq.refl _)⟩
    | .other_Const (cs159 := calls) (ld60 := ld) (ev161 := load) (hc178 := hall) .. =>
      obtain ⟨a, us, rfl, ha, ps, hp, _⟩ := hE.const_of_load ld
      have hsub : ∀ cl ∈ calls, cl ∈ cs := by intro cl hm; rw [hall]; simp [hm]
      exact declared_type_rep hc (hg.sub hsub) ha hE.const_key_ne hp load
    | .other_App (cs207 := first) (cs256 := heads) (cs306 := subs) (ld60 := ld)
        (ev209 := child) (ev258 := norm) (ld252 := ldpi) (ev308 := inst) (hc332 := hall) .. =>
      obtain ⟨f, a, rfl, hf, ha⟩ := hE.app_of_load ld
      have hfsub : ∀ cl ∈ first, cl ∈ cs := by intro cl hm; rw [hall]; simp [hm]
      have hnsub : ∀ cl ∈ heads, cl ∈ cs := by intro cl hm; rw [hall]; simp [hm]
      have hisub : ∀ cl ∈ subs, cl ∈ cs := by intro cl hm; rw [hall]; simp [hm]
      have hlt : first.length < fuel := by
        rw [hall] at hlen; simp only [List.length_cons, List.length_append] at hlen; omega
      obtain ⟨tf, htf⟩ := ih first.length hlt (Nat.le_refl _) (hg.sub hfsub) hctx hf child
      obtain ⟨tn, htn, _⟩ := head_rep hc (hg.sub hnsub) htf norm
      obtain ⟨D, B, level, rfl, _, hB, _⟩ := htn.forallE_of_load ldpi
      have hi := SubstAux.gall c.κ .expr_inst1 _ _ _ _ _ inst _ _ (0 : F) rfl
        (bounded_sub hisub hg.2) d Γ B a
        (by simpa only [ZMod.val_zero, Nat.zero_add] using hB)
        (ha.mono (child.heap_extends.trans norm.heap_extends))
      exact ⟨_, by simpa only [ZMod.val_zero, Nat.zero_add] using hi⟩
    | .other_Forall (x_ty := ty) (m381 := mctx) (cs367 := first)
        (cs438 := heads) (ld60 := ld) (hm389 := hm) (ev369 := child) (ev440 := norm)
        (ld434 := ldsort) (he477 := hr) (hm476 := hh) (hc489 := hall) .. =>
      obtain ⟨D, B, level, rfl, hD, hB, _⟩ := hE.forallE_of_load ld
      subst hm hr hh
      have ectx := Heap.Extends.snoc h (.construct kexprListEnum "Cons" [ty, ctx])
      have hctx' := types_extend hctx hD
      have hb := Tm.open_body (Ghost.extend_at Γ d D) (Ghost.extend_below Γ d D) (hB.mono ectx)
      have hfsub : ∀ cl ∈ first, cl ∈ cs := by intro cl hm; rw [hall]; simp [hm]
      have hnsub : ∀ cl ∈ heads, cl ∈ cs := by intro cl hm; rw [hall]; simp [hm]
      have hlt : first.length < fuel := by
        rw [hall] at hlen; simp only [List.length_cons, List.length_append] at hlen; omega
      obtain ⟨tb, htb⟩ := ih first.length hlt (Nat.le_refl _) (hg.sub hfsub) hctx' hb child
      obtain ⟨tn, htn, _⟩ := head_rep hc (hg.sub hnsub) htb norm
      obtain ⟨u, _, l, hl, _⟩ := htn.sort_of_load ldsort
      exact ⟨.sort l, .sort List.getElem?_concat_length (hl.mono (Heap.Extends.snoc _ _)) (LvEq.refl _)⟩
    | .other_Lam (x_ty := ty) (x_m := data) (cs523 := first) (ld60 := ld)
        (hm545 := hm) (ev525 := child) (he584 := hr) (hm583 := hh) (hc612 := hall) .. =>
      obtain ⟨D, B, level, rfl, hD, hB, hlevel⟩ := hE.lam_of_load ld
      subst hm hr hh
      have ectx := Heap.Extends.snoc h (.construct kexprListEnum "Cons" [ty, ctx])
      have hctx' := types_extend hctx hD
      have hb := Tm.open_body (Ghost.extend_at Γ d D) (Ghost.extend_below Γ d D) (hB.mono ectx)
      have hsub : ∀ cl ∈ first, cl ∈ cs := by intro cl hm; rw [hall]; simp [hm]
      have hlt : first.length < fuel := by
        rw [hall] at hlen; simp only [List.length_cons, List.length_append] at hlen; omega
      obtain ⟨tb, htb⟩ := ih first.length hlt (Nat.le_refl _) (hg.sub hsub) hctx' hb child
      have hcbody := htb.close (Ghost.extend_below Γ d D)
      have ext := ectx.trans (child.heap_extends.trans (Heap.Extends.snoc _ _))
      exact ⟨.forallE D (tb.abstract1 d) (bmeta level),
        .forallE List.getElem?_concat_length (hD.mono ext)
          (hcbody.mono (Heap.Extends.snoc _ _)) (hlevel.mono ext)⟩
    | .other_Let (cs639 := children) (cs654 := subs) (ld60 := ld)
        (ev656 := inst) (ev641 := child) (hc702 := hall) .. =>
      obtain ⟨D, V, B, rfl, _, hV, hB⟩ := hE.letE_of_load ld
      have hisub : ∀ cl ∈ subs, cl ∈ cs := by intro cl hm; rw [hall]; simp [hm]
      have hsub : ∀ cl ∈ children, cl ∈ cs := by intro cl hm; rw [hall]; simp [hm]
      have hlt : children.length < fuel := by
        rw [hall] at hlen; simp only [List.length_cons, List.length_append] at hlen; omega
      have hi := SubstAux.gall c.κ .expr_inst1 _ _ _ _ _ inst _ _ (0 : F) rfl
        (bounded_sub hisub hg.2) d Γ B V
        (by simpa only [ZMod.val_zero, Nat.zero_add] using hB) hV
      simp only [ZMod.val_zero, Nat.zero_add] at hi
      exact ih children.length hlt (Nat.le_refl _) (hg.sub hsub)
        (types_mono inst.heap_extends hctx) hi child

/-- Structural classification retains a represented output, without claiming that output is
an inferred type in the rules tier. -/
theorem infer_shape_rep {c : ScopedCtx} (hc : ScopedCoreFacts c)
    {d : Nat} {Γ : Nat → KExpr} {E : KExpr} {p ctx budget r : SourceValue F}
    {h h' : Heap F} {cs : List (Call F)} (hg : CoreGood c cs) (hctx : c.types Γ h d ctx)
    (hE : Tm c.κ d Γ h 0 E p)
    (ev : ObsFn W "KernelGuard::infer_shape" [p, ctx, budget] h r h' cs) :
    ∃ T, Tm c.κ d Γ h' 0 T r :=
  infer_shape_rep_go hc cs.length (Nat.le_refl _) hg hctx hE ev

/-- The actual classifier signature is represented at its output pointer. -/
theorem sort_signature_rep {c : ScopedCtx} (hc : ScopedCoreFacts c)
    {d : Nat} {Γ : Nat → KExpr} {E : KExpr} {p ctx r : SourceValue F}
    {h h' : Heap F} {cs : List (Call F)} (hg : CoreGood c cs) (hctx : c.types Γ h d ctx)
    (hE : Tm c.κ d Γ h 0 E p)
    (ev : ObsFn W "KernelGuard::sort_signature" [p, ctx] h r h' cs) :
    ∃ s, RepKLevel h' s r := by
  obtain ⟨t, m1, cs1, m2, tp, cs2, u, cs3, infer, norm, ld, sig, hall⟩ :=
    Obs.«KernelGuard::sort_signature».obs ev
  have h1 : ∀ cl ∈ cs1, cl ∈ cs := by intro cl hm; rw [hall]; simp [hm]
  have h2 : ∀ cl ∈ cs2, cl ∈ cs := by intro cl hm; rw [hall]; simp [hm]
  obtain ⟨T, ht⟩ := infer_shape_rep hc (hg.sub h1) hctx hE infer
  obtain ⟨U, hu, _⟩ := head_rep hc (hg.sub h2) ht norm
  obtain ⟨v, _, l, hl, _⟩ := hu.sort_of_load ld
  exact ⟨_, IxVM.Refinement.Guard.signature_level_spec hl sig⟩

end IxVM.Refinement.Core.GuardData
