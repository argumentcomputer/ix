import IxVMRefinement.DefEq.Basic

/-! # Step lemmas of `KernelDefEq`: the rescue tier

* `is_prop_type`: the io-inferred type, head-normalized to a sort whose level `level_equal`
  equates with the stored `Zero` level (`levelEqual_eq_true_sound`).
* `leading_foralls`: one syntactic `∀` per unit of the counter (`HasPis`).
* `compare_struct_fields`: from `i` up to `nfields`, the projection `.proj S j t` (the stored
  `Proj` cell) against the argument of the constructor's spine at `nparams + j`
  (`Lists::lookup`); the counter stays below the field count, so `i + 1` does not wrap.
* `de_rescue_tier`: the tiers' answers (proof irrelevance, unit-like types, structure η both
  ways, the second by `DefEq.symm`, then the `Nat` offsets' pair). -/

namespace IxVM.Refinement.Core.DefEqAux

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open IxVM.Refinement.KernelLevels (RepKLevel)

set_option linter.unusedVariables false

private theorem fval_one : ZMod.val (1 : F) = 1 := ZMod.val_one _

private theorem cast_val (x : F) : ((ZMod.val x : Nat) : F) = x := ZMod.natCast_zmod_val x

private theorem evalBinOp_add_field {a b : F} {v : SourceValue F}
    (op : evalBinOp .add (.field a : SourceValue F) (.field b) = .ok v) : v = .field (a + b) := by
  simp only [evalBinOp, Except.ok.injEq] at op
  exact op.symm

/-- A `Zero` level cell stored at the end of the heap. -/
private theorem repKLevel_store_zero (h : Heap F) :
    RepKLevel (h ++ [.construct IxVM.Refinement.KernelLevels.klevelEnum "Zero" []]) .zero
      (.ptr (.enum IxVM.Refinement.KernelLevels.klevelEnum) h.length) :=
  RepKLevel.zero (by simp)

/-- A `Proj` cell of a represented address and term, stored at the end of the heap. -/
private theorem tm_store_proj {c : Ctx} {d : Nat} {Γ : Nat → KExpr} {h : Heap F} {k : Nat}
    {a : Bytes.Address} {i : F} {E : KExpr} {ap ep : SourceValue F} (ha : RepAddr h a ap)
    (hE : c.tmk d Γ k h E ep) :
    c.tmk d Γ k (h ++ [.construct kexprEnum "Proj" [ap, .field i, ep]])
      (.proj (c.κ (ixAddr a)) (ZMod.val i) E) (.ptr (.enum kexprEnum) h.length) := by
  have ext : Heap.Extends h (h ++ [.construct kexprEnum "Proj" [ap, .field i, ep]]) :=
    Heap.Extends.snoc h _
  exact Tm.proj (by simp) (Bytes.repAddressRef_heapMono₂ addrTy ext ha) (Tm.mono ext hE)

/-- `Lists::lookup` on a list of top-level terms: the term at the index; no allocation. -/
private theorem tml_lookup {c : Ctx} {d : Nat} {Γ : Nat → KExpr} {As : List KExpr}
    {l r : SourceValue F} {i : F} {h h' : Heap F} {cs : List (Call F)}
    (ev : ObsFn W Obs.Names.«Lists::lookup<&KernelTypes::KExprNode>» [l, .field i] h r h' cs)
    (hl : c.tml d Γ h As l) :
    (∃ x, As[ZMod.val i]? = some x ∧ c.tm d Γ h x r) ∧ h' = h :=
  Lib.Lists.lookup_spec (t := .ptr (.named "KernelTypes::KExprNode" [])) (R := TmE c.κ d Γ)
    (by rw [Obs.Names.«Lists::lookup<&KernelTypes::KExprNode>».symbol]; exact ev)
    (by rw [Obs.Names.«Lists::Node<&KernelTypes::KExprNode>».symbol]; exact hl)

end IxVM.Refinement.Core.DefEqAux

namespace IxVM.Refinement.Core

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open IxVM.Refinement.KernelLevels (RepKLevel)
open Ix.Kernel.Rules (Red DefEq)
open IxVM.Refinement.Core.DefEqAux

set_option linter.unusedVariables false

/-! ## Propositions -/

/-- `KernelDefEq::is_prop_type`: the io-inferred type (`k_infer_only`) head-normalizes (`whnf`)
to a sort whose level `level_equal` equates with `Zero`, so it is `0` at every assignment. -/
theorem is_prop_type_step (c : Ctx) {args : List (SourceValue F)} {h h' : Heap F}
    {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelDefEq::is_prop_type" args h r h' calls) (ih : IH c calls) :
    Specs.DefEq.is_prop_type c args h r h' calls := by
  intro rc ty types hargs good hrc d Γ htypes T hT hr
  subst hargs
  rcases Obs.«KernelDefEq::is_prop_type».obs ev with
    ⟨v1, m2, cs12, v39, m40, cs50, x_l, cs104, m117, ev14, ev52, ld88, hm125, ev106, hc129⟩ |
    ⟨v1, m2, cs12, v39, m40, cs50, v77, ev14, ev52, ld88, hne130, he134, he135, hc136⟩
  · subst hc129 hm125
    have e1 := ObsFn.heap_extends ev14
    obtain ⟨S, hS, hinf⟩ := ih.get (.infer .k_infer_only) (by lt_calls) ev14 rc ty types rfl
      (good.sub fun x hx => by simp [hx]) hrc d Γ htypes T hT
    obtain ⟨S', hS', hred⟩ := ih.get (.whnf .whnf) (by lt_calls) ev52 rc v1 types rfl
      (good.sub fun x hx => by simp [hx]) (RCRep.mono e1 hrc) d Γ (types_mono e1 htypes) S hS
    obtain ⟨u, rfl, l, hl, hul⟩ := hS'.sort_of_load ld88
    obtain ⟨hr', -⟩ := ih.get (.levelOps .level_equal) (by lt_calls) ev106 x_l _ rfl
      (good.sub fun x hx => by simp [hx]).2 l .zero (hl.mono (Heap.Extends.snoc _ _))
      (repKLevel_store_zero m40)
    have he : IxVM.Refinement.KernelLevels.levelEqual l .zero = true :=
      of_ite_field_ne_zero hr' hr
    exact ⟨S, u, hinf, hred, fun φ =>
      (hul φ).trans (IxVM.Refinement.KernelLevels.levelEqual_eq_true_sound he φ)⟩
  · exact absurd he134 hr

/-! ## Telescopes -/

/-- `KernelDefEq::leading_foralls`: one `∀` node per unit of the counter. -/
theorem leading_foralls_step (c : Ctx) {args : List (SourceValue F)} {h h' : Heap F}
    {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelDefEq::leading_foralls" args h r h' calls) (ih : IH c calls) :
    Specs.DefEq.leading_foralls c args h r h' calls := by
  intro t n hargs good hr d Γ k T hT
  subst hargs
  rcases Obs.«KernelDefEq::leading_foralls».obs ev with
    ⟨hv14, he15, he16, hc17⟩ |
    ⟨w41, x_body, w42, cs61, v65, hne18, ld33, op86, ev63, hc88⟩ |
    ⟨v22, hne18, ld33, hne89, he93, he94, hc95⟩
  · injection hv14 with hn
    subst hn
    simp only [ZMod.val_zero]
    exact True.intro
  · subst hc88
    have hn0 : n ≠ 0 := fun hn => hne18 (by subst hn; rfl)
    obtain rfl := Lib.sub_one_inv op86
    obtain ⟨T1, B1, ℓ1, rfl, -, hB1, -⟩ := hT.forallE_of_load ld33
    have hrec := ih.get (.defEq .leading_foralls) (by lt_calls) ev63 x_body (n - 1) rfl
      (good.sub fun x hx => by simp [hx]) hr d Γ (k + 1) B1 hB1
    rw [← Lib.val_sub_one hn0]
    exact hrec
  · exact absurd he93 hr

/-! ## Structure η: the fields -/

/-- `KernelDefEq::compare_struct_fields`: from `i` up to `nfields`, each projection of `t`
(the stored `Proj` cell) against the argument of `s_args` at `nparams + j` (`Lists::lookup`).
The counter stays below `nfields`, so `i + 1` reads as the next natural. -/
theorem compare_struct_fields_step (c : Ctx) {args : List (SourceValue F)} {h h' : Heap F}
    {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelDefEq::compare_struct_fields" args h r h' calls) (ih : IH c calls) :
    Specs.DefEq.compare_struct_fields c args h r h' calls := by
  intro rc sp np nf t sargs ip types hargs good hrc sa p n i hsa hnp hnf hip hin d Γ htypes T Ss
    hT hSs hr
  subst hargs hnp hnf hip
  rcases Obs.«KernelDefEq::compare_struct_fields».obs ev with
    ⟨op17, he24, he25, hc26⟩ |
    ⟨v1, m32, v70, m71, cs81, v85, m110, cs121, op17, hne27, hm42, op106, ev83, ev123, he160,
      he161, hc162⟩ |
    ⟨v1, m32, v70, m71, cs81, v85, v109, m110, cs121, cs170, v179, op17, hne27, hm42, op106, ev83,
      ev123, hne163, op236, ev172, hc245⟩
  · -- no field left: the range is empty
    intro j hij hjn
    obtain ⟨k, hk1, hk2⟩ := eq_of_sub_field op17
    injection hk1 with hk1
    injection hk2 with hk2
    subst hk1 hk2
    omega
  · exact absurd he160 hr
  · subst hc245 hm42
    obtain ⟨a1, b1, ha1, hb1, rfl⟩ := evalBinOp_sub_inv' op17
    injection ha1 with ha1
    injection hb1 with hb1
    subst ha1 hb1
    have hni : n ≠ i := fun e => hne27 (by rw [e]; simp)
    have hlt : ZMod.val i < ZMod.val n :=
      lt_of_le_of_ne hin fun e => hni (ZMod.val_injective _ e).symm
    have hvi : ZMod.val (i + 1) = ZMod.val i + 1 := by
      have := ZMod.val_lt n
      rw [ZMod.val_add_of_lt (by have := fval_one; omega), fval_one]
    obtain rfl := evalBinOp_add_field op106
    obtain rfl := evalBinOp_add_field op236
    have e0 : Heap.Extends h (h ++ [.construct kexprEnum "Proj" [sp, .field i, t]]) :=
      Heap.Extends.snoc _ _
    -- field `i`: the projection against the spine's argument at `nparams + i`
    obtain ⟨⟨S0, hS0, hS0r⟩, rfl⟩ := tml_lookup ev83 (tml_mono e0 hSs)
    have hde := ih.get (.defEq .k_is_def_eq) (by lt_calls) ev123 rc _ v70 types rfl
      (good.sub fun x hx => by simp [hx]) (RCRep.mono e0 hrc) d Γ (types_mono e0 htypes) _ S0
      (tm_store_proj hsa hT) hS0r hne163
    -- the fields from `i + 1` on
    have E := e0.trans (ObsFn.heap_extends ev123)
    have hrec := ih.get (.defEq .compare_struct_fields) (by lt_calls) ev172 rc sp _ _ t sargs _
      types rfl (good.sub fun x hx => by simp [hx]) (RCRep.mono E hrc) sa p n (i + 1)
      (Bytes.repAddressRef_heapMono₂ addrTy E hsa) rfl rfl rfl (by omega) d Γ
      (types_mono E htypes) T Ss (Tm.mono E hT) (tml_mono E hSs) hr
    intro j hij hjn
    rcases Nat.eq_or_lt_of_le hij with rfl | hj
    · exact ⟨S0, by simpa only [cast_val] using hS0, hde⟩
    · exact hrec j (by omega) hjn

/-! ## The rescue tier -/

/-- `KernelDefEq::de_rescue_tier`: a decided answer `1` is the `DefEq` of the tier that decided
it: proof irrelevance, unit-like types, structure η (`try_eta_struct(bw, aw)` by `DefEq.symm`),
or the `Nat` offsets' pair. -/
theorem de_rescue_tier_step (c : Ctx) {args : List (SourceValue F)} {h h' : Heap F}
    {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelDefEq::de_rescue_tier" args h r h' calls) (ih : IH c calls) :
    Specs.DefEq.de_rescue_tier c args h r h' calls := by
  intro rc a b types hargs good hrc d Γ htypes A B hA hB y hy hy0
  subst hargs
  rcases Obs.«KernelDefEq::de_rescue_tier».obs ev with
    ⟨m2, cs13, ev15, he56, he69, hc70⟩ |
    ⟨v1, m2, cs13, m76, cs87, ev15, hne71, ev89, he130, he143, hc144⟩ |
    ⟨v1, m2, cs13, v75, m76, cs87, m150, cs161, ev15, hne71, ev89, hne145, ev163, he204, he217,
      hc218⟩ |
    ⟨v1, m2, cs13, v75, m76, cs87, v149, m150, cs161, m224, cs235, ev15, hne71, ev89, hne145, ev163,
      hne219, ev237, he278, he291, hc292⟩ |
    ⟨v1, m2, cs13, v75, m76, cs87, v149, m150, cs161, v223, m224, cs235, cs300, ev15, hne71, ev89,
      hne145, ev163, hne219, ev237, hne293, ev302, hc335⟩
  · subst hc70
    exact ih.get (.defEq .try_proof_irrel) (by lt_calls) ev15 rc a b types rfl
      (good.sub fun x hx => by simp [hx]) hrc d Γ htypes A B hA hB field_one_ne_zero
  · subst hc144
    have e := ObsFn.heap_extends ev15
    exact ih.get (.defEq .try_unit_like) (by lt_calls) ev89 rc a b types rfl
      (good.sub fun x hx => by simp [hx]) (RCRep.mono e hrc) d Γ (types_mono e htypes) A B
      (Tm.mono e hA) (Tm.mono e hB) field_one_ne_zero
  · subst hc218
    have e := (ObsFn.heap_extends ev15).trans (ObsFn.heap_extends ev89)
    exact ih.get (.defEq .try_eta_struct) (by lt_calls) ev163 rc a b types rfl
      (good.sub fun x hx => by simp [hx]) (RCRep.mono e hrc) d Γ (types_mono e htypes) A B
      (Tm.mono e hA) (Tm.mono e hB) field_one_ne_zero
  · subst hc292
    have e := (ObsFn.heap_extends ev15).trans
      ((ObsFn.heap_extends ev89).trans (ObsFn.heap_extends ev163))
    exact .symm (ih.get (.defEq .try_eta_struct) (by lt_calls) ev237 rc b a types rfl
      (good.sub fun x hx => by simp [hx]) (RCRep.mono e hrc) d Γ (types_mono e htypes) B A
      (Tm.mono e hB) (Tm.mono e hA) field_one_ne_zero)
  · subst hc335
    have e := (ObsFn.heap_extends ev15).trans ((ObsFn.heap_extends ev89).trans
      ((ObsFn.heap_extends ev163).trans (ObsFn.heap_extends ev237)))
    exact ih.get (.defEq .try_def_eq_nat) (by lt_calls) ev302 rc a b types rfl
      (good.sub fun x hx => by simp [hx]) (RCRep.mono e hrc) d Γ (types_mono e htypes) A B
      (Tm.mono e hA) (Tm.mono e hB) y hy hy0

end IxVM.Refinement.Core
