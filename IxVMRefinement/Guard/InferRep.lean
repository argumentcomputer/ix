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

set_option linter.unusedVariables false in
/-- **`KernelInfer::types_lookup` meets its spec at every derivation**, with no induction
hypothesis: its one callee is `expr_lift`, whose spec holds of every derivation
(`SubstAux.gall`). -/
theorem _root_.IxVM.Refinement.Core.types_lookup_spec (c : ScopedCtx)
    {args : List (SourceValue F)} {h h' : Heap F} {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelInfer::types_lookup" args h r h' calls) :
    Specs.Infer.types_lookup c args h r h' calls := by
  intro types i hargs good
  subst hargs
  obtain ⟨v1, m2, cs12, cs34, v38, ev14, op60, ev36, hc68⟩ :=
    Obs.«KernelInfer::types_lookup».obs ev
  intro d Γ htypes
  subst hc68
  obtain ⟨n, hnd, hl⟩ := htypes.1.toRepList
  obtain ⟨⟨x, hx, hxr⟩, hm⟩ := SubstAux.klookup ev14 hl
  rw [hm] at ev36
  obtain ⟨hlt, rfl⟩ := segEntries_getElem? hx
  have hb : n < 549755813888 := by
    have := RomBound.bounded_length_lt good.2
      (c := ⟨Obs.Names.«Lists::lookup<&KernelTypes::KExprNode>», [types, .field i], h⟩)
      (by simp) (by simp) hl
    simpa [segEntries] using this
  have hv38 : v38 = .field (i + 1) := NatAux.add_ok op60
  subst hv38
  have hi1 : ZMod.val (i + 1) = ZMod.val i + 1 := NatAux.val_add_one (by omega)
  have hE : c.tmk (d - 1 - ZMod.val i) Γ (ZMod.val (0 : F)) h (Γ (d - 1 - ZMod.val i)) v1 := by
    rw [ZMod.val_zero]; exact hxr
  have hlift := SubstAux.gall c.κ .expr_lift _ _ _ _ _ ev36 v1 (i + 1) 0 rfl
    (good.sub fun x hx => by simp [hx]).2 (by rw [hi1]; omega) 0 (ZMod.val i + 1)
    (by rw [hi1]; omega) (d - 1 - ZMod.val i) Γ (Γ (d - 1 - ZMod.val i)) hE
  refine ⟨by omega, ?_⟩
  have e1 : d - 1 - ZMod.val i + (ZMod.val i + 1) = d := by omega
  have e2 : fvIdx d 0 (ZMod.val i) = d - 1 - ZMod.val i := by simp [fvIdx]
  rw [e2]
  rw [e1, ZMod.val_zero] at hlift
  exact hlift

/-- The facts a prefix carries give the registry's induction hypothesis at every call list: the
registry's steps hold of every derivation. -/
theorem _root_.IxVM.Refinement.Core.ScopedCoreFacts.ih {c : ScopedCtx} (hc : ScopedCoreFacts c)
    (cs : List (Call F)) : IH c cs :=
  fun f args h r h' cs' _ ev => Registry.induction c (scoped_steps c hc) f args h r h' cs' ev

private theorem infer_shape_rep_go {c : ScopedCtx} (hc : ScopedCoreBase c) :
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
      have hs := types_lookup_spec c lookup
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
      exact declared_type_rep_base hc (hg.sub hsub) ha hE.const_key_ne hp load
    | .other_App (cs207 := first) (cs256 := heads) (cs306 := subs) (ld60 := ld)
        (ev209 := child) (ev258 := norm) (ld252 := ldpi) (ev308 := inst) (hc332 := hall) .. =>
      obtain ⟨f, a, rfl, hf, ha⟩ := hE.app_of_load ld
      have hfsub : ∀ cl ∈ first, cl ∈ cs := by intro cl hm; rw [hall]; simp [hm]
      have hnsub : ∀ cl ∈ heads, cl ∈ cs := by intro cl hm; rw [hall]; simp [hm]
      have hisub : ∀ cl ∈ subs, cl ∈ cs := by intro cl hm; rw [hall]; simp [hm]
      have hlt : first.length < fuel := by
        rw [hall] at hlen; simp only [List.length_cons, List.length_append] at hlen; omega
      obtain ⟨tf, htf⟩ := ih first.length hlt (Nat.le_refl _) (hg.sub hfsub) hctx hf child
      obtain ⟨tn, htn, _⟩ := head_rep_base hc (hg.sub hnsub) htf norm
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
      have hctx' := ProjAux.types_extend hctx hD
      have hb := Tm.open_body (Ghost.extend_at Γ d D) (Ghost.extend_below Γ d D) (hB.mono ectx)
      have hfsub : ∀ cl ∈ first, cl ∈ cs := by intro cl hm; rw [hall]; simp [hm]
      have hnsub : ∀ cl ∈ heads, cl ∈ cs := by intro cl hm; rw [hall]; simp [hm]
      have hlt : first.length < fuel := by
        rw [hall] at hlen; simp only [List.length_cons, List.length_append] at hlen; omega
      obtain ⟨tb, htb⟩ := ih first.length hlt (Nat.le_refl _) (hg.sub hfsub) hctx' hb child
      obtain ⟨tn, htn, _⟩ := head_rep_base hc (hg.sub hnsub) htb norm
      obtain ⟨u, _, l, hl, _⟩ := htn.sort_of_load ldsort
      exact ⟨.sort l, .sort List.getElem?_concat_length (hl.mono (Heap.Extends.snoc _ _)) (LvEq.refl _)⟩
    | .other_Lam (x_ty := ty) (x_m := data) (v512 := out) (m513 := mout) (cs523 := first) (ld60 := ld)
        (hm545 := hm) (ev525 := child) (he584 := hr) (hm583 := hh) (hc612 := hall) .. =>
      obtain ⟨D, B, level, rfl, hD, hB, hlevel⟩ := hE.lam_of_load ld
      subst hm hr hh
      have ectx := Heap.Extends.snoc h (.construct kexprListEnum "Cons" [ty, ctx])
      have hctx' := ProjAux.types_extend hctx hD
      have hb := Tm.open_body (Ghost.extend_at Γ d D) (Ghost.extend_below Γ d D) (hB.mono ectx)
      have hsub : ∀ cl ∈ first, cl ∈ cs := by intro cl hm; rw [hall]; simp [hm]
      have hlt : first.length < fuel := by
        rw [hall] at hlen; simp only [List.length_cons] at hlen; omega
      obtain ⟨tb, htb⟩ := ih first.length hlt (Nat.le_refl _) (hg.sub hsub) hctx' hb child
      have hcbody := htb.close (Ghost.extend_below Γ d D)
      have eFinal := Heap.Extends.snoc mout (.construct kexprEnum "Forall" [ty, out, data])
      have ext := ectx.trans (child.heap_extends.trans eFinal)
      exact ⟨.forallE D (tb.abstract1 d) (bmeta level),
        .forallE List.getElem?_concat_length (hD.mono ext)
          (hcbody.mono eFinal) (hlevel.mono ext)⟩
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
      simp only [ZMod.val_zero] at hi
      exact ih children.length hlt (Nat.le_refl _) (hg.sub hsub)
        (types_mono inst.heap_extends hctx) hi child

/-- Structural classification retains a represented output, without claiming that output is
an inferred type in the rules tier; from the facts stated before the registry. -/
theorem infer_shape_rep_base {c : ScopedCtx} (hc : ScopedCoreBase c)
    {d : Nat} {Γ : Nat → KExpr} {E : KExpr} {p ctx budget r : SourceValue F}
    {h h' : Heap F} {cs : List (Call F)} (hg : CoreGood c cs) (hctx : c.types Γ h d ctx)
    (hE : Tm c.κ d Γ h 0 E p)
    (ev : ObsFn W "KernelGuard::infer_shape" [p, ctx, budget] h r h' cs) :
    ∃ T, Tm c.κ d Γ h' 0 T r :=
  infer_shape_rep_go hc cs.length (Nat.le_refl _) hg hctx hE ev

/-- Structural classification retains a represented output, without claiming that output is
an inferred type in the rules tier. -/
theorem infer_shape_rep {c : ScopedCtx} (hc : ScopedCoreFacts c)
    {d : Nat} {Γ : Nat → KExpr} {E : KExpr} {p ctx budget r : SourceValue F}
    {h h' : Heap F} {cs : List (Call F)} (hg : CoreGood c cs) (hctx : c.types Γ h d ctx)
    (hE : Tm c.κ d Γ h 0 E p)
    (ev : ObsFn W "KernelGuard::infer_shape" [p, ctx, budget] h r h' cs) :
    ∃ T, Tm c.κ d Γ h' 0 T r :=
  infer_shape_rep_base hc.base hg hctx hE ev

/-- The actual classifier signature is represented at its output pointer; from the facts stated
before the registry. -/
theorem sort_signature_rep_base {c : ScopedCtx} (hc : ScopedCoreBase c)
    {d : Nat} {Γ : Nat → KExpr} {E : KExpr} {p ctx r : SourceValue F}
    {h h' : Heap F} {cs : List (Call F)} (hg : CoreGood c cs) (hctx : c.types Γ h d ctx)
    (hE : Tm c.κ d Γ h 0 E p)
    (ev : ObsFn W "KernelGuard::sort_signature" [p, ctx] h r h' cs) :
    ∃ s, RepKLevel h' s r := by
  obtain ⟨t, m1, cs1, m2, tp, cs2, u, cs3, infer, norm, ld, sig, hall⟩ :=
    Obs.«KernelGuard::sort_signature».obs ev
  have h1 : ∀ cl ∈ cs1, cl ∈ cs := by intro cl hm; rw [hall]; simp [hm]
  have h2 : ∀ cl ∈ cs2, cl ∈ cs := by intro cl hm; rw [hall]; simp [hm]
  obtain ⟨T, ht⟩ := infer_shape_rep_base hc (hg.sub h1) hctx hE infer
  obtain ⟨U, hu, _⟩ := head_rep_base hc (hg.sub h2) ht norm
  obtain ⟨v, _, l, hl, _⟩ := hu.sort_of_load ld
  exact ⟨_, IxVM.Refinement.Guard.signature_level_spec hl sig⟩

/-- The actual classifier signature is represented at its output pointer. -/
theorem sort_signature_rep {c : ScopedCtx} (hc : ScopedCoreFacts c)
    {d : Nat} {Γ : Nat → KExpr} {E : KExpr} {p ctx r : SourceValue F}
    {h h' : Heap F} {cs : List (Call F)} (hg : CoreGood c cs) (hctx : c.types Γ h d ctx)
    (hE : Tm c.κ d Γ h 0 E p)
    (ev : ObsFn W "KernelGuard::sort_signature" [p, ctx] h r h' cs) :
    ∃ s, RepKLevel h' s r :=
  sort_signature_rep_base hc.base hg hctx hE ev

/-- The actual assertion produces agreement of the inferred sort's zero-set with the actual
classifier output, retaining that classifier subcall for the raw-dictionary refinement; from the
facts stated before the registry and the registry's induction hypothesis at the run's own calls
(the sort check `k_ensure_sort` is the one callee read from it). -/
theorem checked_sort_zero_iff_ih {c : ScopedCtx} (hc : ScopedCoreBase c)
    {d : Nat} {Γ : Nat → KExpr} {E : KExpr} {rc p ctx r : SourceValue F}
    {h h' : Heap F} {cs : List (Call F)} (hg : CoreGood c cs) (ih : IH c cs)
    (hrc : c.rc h rc) (hctx : c.types Γ h d ctx) (hE : Tm c.κ d Γ h 0 E p)
    (ev : ObsFn W "KernelGuard::checked_sort" [rc, p, ctx] h r h' cs) :
    ∃ T u actual signature predicted before after inner,
      Ix.Kernel.Rules.Infer c.env .full d E T ∧ Ix.Kernel.Rules.Red c.env d T (.sort u) ∧
      RepKLevel h' actual r ∧ LvEq u actual ∧ Heap.Extends h before ∧
      ObsFn W "KernelGuard::sort_signature" [p, ctx] before predicted after inner ∧
      RepKLevel after signature predicted ∧ (∀ cl ∈ inner, cl ∈ cs) ∧
      ∀ φ, Ix.Kernel.Level.eval φ u = 0 ↔ Ix.Kernel.Level.eval φ signature = 0 := by
  obtain ⟨value, m1, cs1, expected, m2, cs2, answer, m3, cs3, code, m4, cs4,
    infer, predict, encode, compare, hanswer, hr, hh, hall⟩ := Obs.«KernelGuard::checked_sort».obs ev
  subst hr hh
  have h1 : ∀ cl ∈ cs1, cl ∈ cs := by intro cl hm; rw [hall]; simp [hm]
  have h2 : ∀ cl ∈ cs2, cl ∈ cs := by intro cl hm; rw [hall]; simp [hm]
  have h3 : ∀ cl ∈ cs3, cl ∈ cs := by intro cl hm; rw [hall]; simp [hm]
  have hlt1 : cs1.length < cs.length := by
    rw [hall]; simp only [List.length_cons, List.length_append]; omega
  obtain ⟨T, u, hi, hred, actual, ha, heq⟩ :=
    ih.get (.infer .k_ensure_sort) hlt1 infer rc p ctx rfl (hg.sub h1) hrc d Γ hctx E hE
  obtain ⟨signature, hs⟩ := sort_signature_rep_base hc (hg.sub h2)
    (types_mono infer.heap_extends hctx) (hE.mono infer.heap_extends) predict
  have hcoded := IxVM.Refinement.Guard.signature_level_spec (ha.mono predict.heap_extends) encode
  rw [hanswer] at compare
  have hchecked := Decl.levels_equal_one IxVM.Refinement.Levels.levels compare
    (bounded_sub h3 hg.2) hcoded (hs.mono encode.heap_extends)
  refine ⟨T, u, actual, signature, expected, m1, m2, cs2, hi, hred,
    ha.mono (predict.heap_extends.trans (encode.heap_extends.trans compare.heap_extends)),
    heq, infer.heap_extends, predict, hs, h2, ?_⟩
  intro φ
  rw [heq φ, Ix.Kernel.Level.guardSignatureLevel_zero_iff actual φ, hchecked φ]

/-- The actual assertion produces agreement of the inferred sort's zero-set with the actual
classifier output, retaining that classifier subcall for the raw-dictionary refinement. -/
theorem checked_sort_zero_iff {c : ScopedCtx} (hc : ScopedCoreFacts c)
    {d : Nat} {Γ : Nat → KExpr} {E : KExpr} {rc p ctx r : SourceValue F}
    {h h' : Heap F} {cs : List (Call F)} (hg : CoreGood c cs)
    (hrc : c.rc h rc) (hctx : c.types Γ h d ctx) (hE : Tm c.κ d Γ h 0 E p)
    (ev : ObsFn W "KernelGuard::checked_sort" [rc, p, ctx] h r h' cs) :
    ∃ T u actual signature predicted before after inner,
      Ix.Kernel.Rules.Infer c.env .full d E T ∧ Ix.Kernel.Rules.Red c.env d T (.sort u) ∧
      RepKLevel h' actual r ∧ LvEq u actual ∧ Heap.Extends h before ∧
      ObsFn W "KernelGuard::sort_signature" [p, ctx] before predicted after inner ∧
      RepKLevel after signature predicted ∧ (∀ cl ∈ inner, cl ∈ cs) ∧
      ∀ φ, Ix.Kernel.Level.eval φ u = 0 ↔ Ix.Kernel.Level.eval φ signature = 0 :=
  checked_sort_zero_iff_ih hc.base hg (hc.ih cs) hrc hctx hE ev

end IxVM.Refinement.Core.GuardData
