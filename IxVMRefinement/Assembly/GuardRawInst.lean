import IxVMRefinement.Assembly.GuardRawSubst
import IxCK.Kernel.Inductives.StructParts

/-! # Actual capture-avoiding substitution of retained raw syntax

The source substitutes open de Bruijn arguments with lifting. Its absence shortcut lowers a
variable window; both paths must match instantiate1Lift, without identifying it with the
closed-argument semantic substitution specification.
-/

namespace IxVM.Refinement.Decl

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open IxVM.Refinement.Core
open IxVM.Refinement.Core.Specs.Subst (IdxAll NoIdx)
open Ix.Kernel (Expr)

set_option maxHeartbeats 2400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-- The actual heap exclusion window excludes the corresponding variable from retained lets
as well as every other part of the raw syntax. -/
theorem RawTmExact.raw_absent_of_idx {κ : _root_.Address → KKey} {Γ : Nat → KExpr}
    {h : Heap F} {k : Nat} {R E : KExpr} {p : SourceValue F}
    (rep : RawTmExact κ 0 Γ h k R E p) :
    ∀ {m j}, IdxAll h (fun n i => i.val < j + n ∨ j + 1 + n ≤ i.val) m p →
      R.hasLooseBVar (j + m) = false := by
  induction rep with
  | bvarLocal cell small inside =>
    intro m j indices
    obtain ⟨i, equal, outside⟩ := SubstAux.idxAll_bvar_inv indices (loadValue_enum_cell cell)
    injection equal with equal
    subst equal
    simp only [Expr.hasLooseBVar, beq_eq_false_iff_ne]
    omega
  | bvarFree _ _ _ impossible => omega
  | sort | const | litNat | litStr => intro _ _ _; rfl
  | app cell _ _ left right =>
    intro m j indices
    obtain ⟨func, arg⟩ := SubstAux.idxAll_app_inv indices (loadValue_enum_cell cell)
    simp only [Expr.hasLooseBVar, Bool.or_eq_false_iff]
    exact ⟨left func, right arg⟩
  | lam cell _ _ _ dom body =>
    intro m j indices
    obtain ⟨domain, tail⟩ := SubstAux.idxAll_lam_inv indices (loadValue_enum_cell cell)
    simp only [Expr.hasLooseBVar, Bool.or_eq_false_iff]
    exact ⟨dom domain, by simpa only [Nat.add_assoc] using body tail⟩
  | forallE cell _ _ _ dom body =>
    intro m j indices
    obtain ⟨domain, tail⟩ := SubstAux.idxAll_forallE_inv indices (loadValue_enum_cell cell)
    simp only [Expr.hasLooseBVar, Bool.or_eq_false_iff]
    exact ⟨dom domain, by simpa only [Nat.add_assoc] using body tail⟩
  | letE cell _ _ _ type value body =>
    intro m j indices
    obtain ⟨typeIndices, valueIndices, tail⟩ := SubstAux.idxAll_letE_inv indices (loadValue_enum_cell cell)
    simp only [Expr.hasLooseBVar, Bool.or_eq_false_iff]
    exact ⟨⟨type typeIndices, value valueIndices⟩,
      by simpa only [Nat.add_assoc] using body tail⟩
  | proj cell address _ inner =>
    intro m j indices
    exact inner (SubstAux.idxAll_proj_inv indices (loadValue_enum_cell cell))

/-- The actual occurrence scan produces the raw absence fact used by its lowering branch. -/
theorem RawExprRep.occurs {κ : _root_.Address → KKey} {h h' : Heap F} {k : Nat}
    {R : KExpr} {p r : SourceValue F} {j : F} {calls : List (Call F)}
    (represented : RawExprRep κ h k R p) (bounded : IxVM.Consistency.Bounded calls)
    (observed : ObsFn W "KernelSubst::expr_has_bvar_at" [p, .field j] h r h' calls) :
    h' = h ∧ (r = .field 0 ∨ r = .field 1) ∧
      (r = .field 0 → R.hasLooseBVar j.val = false) := by
  obtain ⟨E, rep⟩ := represented
  obtain ⟨unchanged, binary, absent⟩ :=
    SubstAux.gall κ .expr_has_bvar_at _ _ _ _ _ observed p j rfl bounded
  refine ⟨unchanged, binary, fun zero => ?_⟩
  simpa only [Nat.add_zero] using rep.raw_absent_of_idx
    (absent zero 0 (fun _ => default) k E rep.toTmExact.toTm)

/-- When the substituted variable is absent, capture-avoiding substitution is the same
single-slot lowering used by the actual shortcut. -/
theorem instantiate1Lift_of_absent {R V : KExpr} {j : Nat}
    (absent : R.hasLooseBVar j = false) : R.instantiate1Lift V j = R.lowerBVars 1 j := by
  induction R generalizing j with
  | bvar i =>
    simp only [Expr.hasLooseBVar, beq_eq_false_iff_ne] at absent
    simp only [Expr.instantiate1Lift, Expr.lowerBVars, Ne.symm absent, ↓reduceIte]
    by_cases above : i > j
    · have threshold : i ≥ j + 1 := by omega
      simp only [above, threshold, ↓reduceIte]
    · have below : ¬ i ≥ j + 1 := by omega
      simp only [above, below, ↓reduceIte]
  | _ => simp_all [Expr.instantiate1Lift, Expr.lowerBVars, Expr.hasLooseBVar, Bool.or_eq_false_iff]

private theorem raw_inst1_seg_heap (κ : _root_.Address → KKey) {calls cs_seg : List (Call F)}
    {l e arg r_seg : SourceValue F} {j : F} {h h' : Heap F}
    (bd : IxVM.Consistency.Bounded calls) (hsub : ∀ c ∈ cs_seg, c ∈ calls)
    (sg : Obs.«KernelSubst::expr_inst1».Seg_lwkawbtz l e arg (.field j) h r_seg h' cs_seg) :
    h' = h := by
  cases sg with
  | n0 _ _ _ _ ev _ he _ =>
    obtain ⟨_, _, _, _, _, _, _, rfl⟩ := SubstAux.ltf ev
    exact he
  | n1 _ _ _ _ _ ev1 ev2 hc =>
    obtain ⟨_, _, _, _, _, _, _, rfl⟩ := SubstAux.ltf ev1
    exact (SubstAux.gall κ .expr_has_bvar_at _ _ _ _ _ ev2 _ _ rfl
      (bounded_sub (fun x hx => hsub x (by rw [hc]; simp [hx])) bd)).1

private theorem raw_inst_go (κ : _root_.Address → KKey) :
    ∀ fuel : Nat, ∀ {n : Nat} {B V : KExpr} {depth : F}
      {p arg r : SourceValue F} {h h' : Heap F} {calls : List (Call F)},
      calls.length ≤ fuel → IxVM.Consistency.Bounded calls →
      RawExprRep κ h (n + depth.val + 1) B p → RawExprRep κ h n V arg →
      ObsFn W "KernelSubst::expr_inst1" [p, arg, .field depth] h r h' calls →
      RawExprRep κ h' (n + depth.val + 1) (B.instantiate1Lift V depth.val) r := by
  intro fuel
  induction fuel using Nat.strong_induction_on with
  | h fuel ih =>
    intro n B V depth p arg r h h' calls length bounded represented argument observed
    match Obs.«KernelSubst::expr_inst1».obs observed with
    | .n0 (ev14 := scan) (ev37 := compare) (he59 := result) (he60 := heap) (hc61 := events) .. =>
      obtain ⟨same, limit, readLimit, limitBound, closed⟩ := represented.lbr
        (bounded_sub (fun _ inside => by rw [events]; simp [inside]) bounded) scan
      obtain ⟨d, limitField, hd, hl, _, _, verdict, unchanged⟩ := SubstAux.ltf compare
      injection hd with hd
      subst d same unchanged result heap
      rw [readLimit] at hl
      injection hl with hl
      subst limitField
      have below := SubstAux.ltf_zero verdict.symm
      rw [SubstAux.val_natCast (SubstAux.lt_mod_of_le_idx limitBound)] at below
      rw [Expr.instantiate1Lift_eq_self (SubstAux.lbb_mono (by omega) closed)]
      exact represented
    | .n1_n1_BVar (ev14 := scan) (ev37 := compare) (sg_nijhquyq := sg) (ld_cazaqiwm := loaded)
        (ev_wttpotmn := lifted) (hc_krxqlobb := events) .. =>
      obtain ⟨same, _⟩ := represented.lbr
        (bounded_sub (fun _ inside => by rw [events]; simp [inside]) bounded) scan
      obtain ⟨d, limitField, hd, hl, depthSmall, limitSmall, verdict, unchanged⟩ := SubstAux.ltf compare
      injection hd with hd
      subst d same unchanged
      have below := SubstAux.ltf_one verdict.symm
      have segEq := raw_inst1_seg_heap κ bounded (fun _ inside => by rw [events]; simp [inside]) sg
      subst segEq
      obtain ⟨E, rep⟩ := represented
      obtain ⟨i, rfl, rfl, small, inside⟩ := rep.raw_bvar_view loaded
      obtain ⟨-, hlbr⟩ := SubstAux.expr_lbr_bvar_val loaded scan
      rw [hlbr] at hl
      injection hl with hl
      subst limitField
      obtain ⟨hi1, hdi, _⟩ := SubstAux.bvar_lbr_lt32 below limitSmall
      have sameIdx : i = depth := by
        cases sg with
        | n0 _ _ _ op ev1 _ _ _ =>
          rw [SubstAux.add_ok op] at ev1
          obtain ⟨x1, y1, hx1, hy1, -, -, hr1, -⟩ := SubstAux.ltf ev1
          rw [hlbr] at hy1
          injection hx1 with hx1; injection hy1 with hy1; subst hx1 hy1
          have hge := SubstAux.ltf_zero hr1.symm
          rw [SubstAux.val_succ32 depthSmall, hi1] at hge
          exact ZMod.val_injective _ (by omega)
        | n1 _ _ _ _ _ ev1 ev2 _ =>
          obtain ⟨_, _, _, _, _, _, _, rfl⟩ := SubstAux.ltf ev1
          exact (SubstAux.expr_has_bvar_at_bvar_one loaded ev2).2
      subst i
      have rawLift := argument.lift
        (bounded_sub (fun _ member => by rw [events]; simp [member]) bounded) (by omega) lifted
      simpa only [Expr.instantiate1Lift, ite_true, ZMod.val_zero] using rawLift.weaken (k' := n + depth.val + 1) (by omega)
    | .n1_n1_App (cs_agwraemf := first) (cs_kkfmwgap := second) (ev14 := scan) (ev37 := compare)
        (sg_nijhquyq := sg) (ld_cazaqiwm := loaded) (he_erfbbtpw := result) (hm_fspgjocs := heap)
        (ev_fjvmtqoz := e1) (ev_pqoxngrc := e2) (hc_myvfxkru := events) .. =>
      obtain ⟨same, _⟩ := represented.lbr
        (bounded_sub (fun _ inside => by rw [events]; simp [inside]) bounded) scan
      obtain ⟨d, _, hd, _, _, _, _, unchanged⟩ := SubstAux.ltf compare
      injection hd with hd
      subst d same unchanged
      have segEq := raw_inst1_seg_heap κ bounded (fun _ inside => by rw [events]; simp [inside]) sg
      subst segEq
      obtain ⟨E, rep⟩ := represented
      obtain ⟨RF, RA, EF, EA, rfl, rfl, func, arg⟩ := rep.raw_app_view loaded
      have short1 : first.length < fuel := by rw [events] at length; simp only [List.length_cons, List.length_append] at length; omega
      have short2 : second.length < fuel := by rw [events] at length; simp only [List.length_cons, List.length_append] at length; omega
      obtain ⟨F', hf⟩ := ih first.length short1 (Nat.le_refl _)
        (bounded_sub (fun _ inside => by rw [events]; simp [inside]) bounded)
        ⟨_, func⟩ argument e1
      obtain ⟨A', ha⟩ := ih second.length short2 (Nat.le_refl _)
        (bounded_sub (fun _ inside => by rw [events]; simp [inside]) bounded)
        ⟨_, arg.mono e1.heap_extends⟩ (argument.mono e1.heap_extends) e2
      subst result heap
      exact ⟨_, .app (by simp) (hf.mono (e2.heap_extends.trans (Heap.Extends.snoc _ _)))
        (ha.mono (Heap.Extends.snoc _ _))⟩
    | .n1_n1_Lam (v_pmwnezas := bodyOut) (cs_nevefsnx := first) (cs_xayqcrof := second)
        (ev14 := scan) (ev37 := compare) (sg_nijhquyq := sg) (ld_cazaqiwm := loaded)
        (he_ewqmuvnh := result) (hm_dzcuiuos := heap) (ev_jltiurnn := e1) (op_zuplncpn := added)
        (ev_xiuhqzbf := e2) (hc_cocetlqw := events) .. =>
      obtain ⟨same, _⟩ := represented.lbr
        (bounded_sub (fun _ inside => by rw [events]; simp [inside]) bounded) scan
      obtain ⟨d, _, hd, _, depthSmall, _, _, unchanged⟩ := SubstAux.ltf compare
      injection hd with hd
      subst d same unchanged
      have segEq := raw_inst1_seg_heap κ bounded (fun _ inside => by rw [events]; simp [inside]) sg
      subst segEq
      obtain ⟨E, rep⟩ := represented
      obtain ⟨RD, RB, ED, EB, u, rfl, rfl, dom, body, level⟩ := rep.raw_lam_view loaded
      rw [SubstAux.add_ok added] at e2
      have short1 : first.length < fuel := by rw [events] at length; simp only [List.length_cons, List.length_append] at length; omega
      have short2 : second.length < fuel := by rw [events] at length; simp only [List.length_cons, List.length_append] at length; omega
      obtain ⟨D', hd⟩ := ih first.length short1 (Nat.le_refl _)
        (bounded_sub (fun _ inside => by rw [events]; simp [inside]) bounded)
        ⟨_, dom⟩ argument e1
      obtain ⟨B', hb⟩ := ih second.length short2 (Nat.le_refl _)
        (bounded_sub (fun _ inside => by rw [events]; simp [inside]) bounded)
        (by
          rw [SubstAux.val_succ32 depthSmall]
          exact ⟨EB, by simpa only [Nat.add_assoc] using body.mono e1.heap_extends⟩)
        (argument.mono e1.heap_extends) e2
      rw [SubstAux.val_succ32 depthSmall] at hb
      subst result heap
      refine ⟨.lam D' B' (bmeta u), .lam (bp := bodyOut) (by simp) (hd.mono (e2.heap_extends.trans (Heap.Extends.snoc _ _))) ?_
        (level.mono (e1.heap_extends.trans (e2.heap_extends.trans (Heap.Extends.snoc _ _))))⟩
      simpa only [Nat.add_assoc] using hb.mono (Heap.Extends.snoc _ _)
    | .n1_n1_Forall (v_rczqylfo := bodyOut) (cs_kkroxoht := first) (cs_kbxdamfr := second)
        (ev14 := scan) (ev37 := compare) (sg_nijhquyq := sg) (ld_cazaqiwm := loaded)
        (he_jirdvifw := result) (hm_vlpbdsmi := heap) (ev_bdxhqrii := e1) (op_ygqucktb := added)
        (ev_ozhmrcxq := e2) (hc_qvjuupic := events) .. =>
      obtain ⟨same, _⟩ := represented.lbr
        (bounded_sub (fun _ inside => by rw [events]; simp [inside]) bounded) scan
      obtain ⟨d, _, hd, _, depthSmall, _, _, unchanged⟩ := SubstAux.ltf compare
      injection hd with hd
      subst d same unchanged
      have segEq := raw_inst1_seg_heap κ bounded (fun _ inside => by rw [events]; simp [inside]) sg
      subst segEq
      obtain ⟨E, rep⟩ := represented
      obtain ⟨RD, RB, ED, EB, u, rfl, rfl, dom, body, level⟩ := rep.raw_forallE_view loaded
      rw [SubstAux.add_ok added] at e2
      have short1 : first.length < fuel := by rw [events] at length; simp only [List.length_cons, List.length_append] at length; omega
      have short2 : second.length < fuel := by rw [events] at length; simp only [List.length_cons, List.length_append] at length; omega
      obtain ⟨D', hd⟩ := ih first.length short1 (Nat.le_refl _)
        (bounded_sub (fun _ inside => by rw [events]; simp [inside]) bounded)
        ⟨_, dom⟩ argument e1
      obtain ⟨B', hb⟩ := ih second.length short2 (Nat.le_refl _)
        (bounded_sub (fun _ inside => by rw [events]; simp [inside]) bounded)
        (by
          rw [SubstAux.val_succ32 depthSmall]
          exact ⟨EB, by simpa only [Nat.add_assoc] using body.mono e1.heap_extends⟩)
        (argument.mono e1.heap_extends) e2
      rw [SubstAux.val_succ32 depthSmall] at hb
      subst result heap
      refine ⟨.forallE D' B' (bmeta u), .forallE (bp := bodyOut) (by simp) (hd.mono (e2.heap_extends.trans (Heap.Extends.snoc _ _))) ?_
        (level.mono (e1.heap_extends.trans (e2.heap_extends.trans (Heap.Extends.snoc _ _))))⟩
      simpa only [Nat.add_assoc] using hb.mono (Heap.Extends.snoc _ _)
    | .n1_n1_Let (ev14 := scan) (ev37 := compare) (sg_nijhquyq := sg) (ld_cazaqiwm := loaded)
        (ev_rhrekngq := helper) (hc_icdctvkp := events) .. =>
      obtain ⟨same, _⟩ := represented.lbr
        (bounded_sub (fun _ inside => by rw [events]; simp [inside]) bounded) scan
      obtain ⟨d, _, hd, _, depthSmall, _, _, unchanged⟩ := SubstAux.ltf compare
      injection hd with hd
      subst d same unchanged
      have segEq := raw_inst1_seg_heap κ bounded (fun _ inside => by rw [events]; simp [inside]) sg
      subst segEq
      obtain ⟨E, rep⟩ := represented
      obtain ⟨RT, RV, RB, ET, EV, EB, rfl, rfl, type, value, body⟩ := rep.raw_let_view loaded
      match Obs.«KernelSubst::expr_inst1_let».obs helper with
      | .run (v11 := bodyOut) (cs21 := first) (cs57 := second) (cs93 := third) (he5 := result) (hm4 := heap)
          (ev23 := e1) (ev59 := e2) (op126 := added) (ev95 := e3) (hc128 := nested) .. =>
        rw [SubstAux.add_ok added] at e3
        have short1 : first.length < fuel := by rw [events, nested] at length; simp only [List.length_cons, List.length_append] at length; omega
        have short2 : second.length < fuel := by rw [events, nested] at length; simp only [List.length_cons, List.length_append] at length; omega
        have short3 : third.length < fuel := by rw [events, nested] at length; simp only [List.length_cons, List.length_append] at length; omega
        obtain ⟨T', ht⟩ := ih first.length short1 (Nat.le_refl _)
          (bounded_sub (fun _ inside => by rw [events, nested]; simp [inside]) bounded)
          ⟨_, type⟩ argument e1
        obtain ⟨V', hv⟩ := ih second.length short2 (Nat.le_refl _)
          (bounded_sub (fun _ inside => by rw [events, nested]; simp [inside]) bounded)
          ⟨_, value.mono e1.heap_extends⟩ (argument.mono e1.heap_extends) e2
        obtain ⟨B', hb⟩ := ih third.length short3 (Nat.le_refl _)
          (bounded_sub (fun _ inside => by rw [events, nested]; simp [inside]) bounded)
          (by
            rw [SubstAux.val_succ32 depthSmall]
            exact ⟨EB, by simpa only [Nat.add_assoc] using body.mono (e1.heap_extends.trans e2.heap_extends)⟩)
          (argument.mono (e1.heap_extends.trans e2.heap_extends)) e3
        rw [SubstAux.val_succ32 depthSmall] at hb
        subst result heap
        refine ⟨instShift V' 0 B', .letE (bp := bodyOut) (by simp)
          (ht.mono (e2.heap_extends.trans (e3.heap_extends.trans (Heap.Extends.snoc _ _))))
          (hv.mono (e3.heap_extends.trans (Heap.Extends.snoc _ _))) ?_⟩
        simpa only [Nat.add_assoc] using hb.mono (Heap.Extends.snoc _ _)
    | .n1_n1_Proj (cs_fvvlxsib := children) (ev14 := scan) (ev37 := compare) (sg_nijhquyq := sg)
        (ld_cazaqiwm := loaded) (he_vyjrbsci := result) (hm_iywlmnii := heap)
        (ev_dwrkbatj := child) (hc_dhrzqlmk := events) .. =>
      obtain ⟨same, _⟩ := represented.lbr
        (bounded_sub (fun _ inside => by rw [events]; simp [inside]) bounded) scan
      obtain ⟨d, _, hd, _, _, _, _, unchanged⟩ := SubstAux.ltf compare
      injection hd with hd
      subst d same unchanged
      have segEq := raw_inst1_seg_heap κ bounded (fun _ inside => by rw [events]; simp [inside]) sg
      subst segEq
      obtain ⟨E, rep⟩ := represented
      have semantic := rep.toTmExact.toTm
      obtain ⟨a, index, RI, EI, rfl, rfl, rfl, address, inner⟩ := rep.raw_proj_view loaded
      have : Resolved (κ (ixAddr a)) := ⟨semantic.proj_key_ne⟩
      have : ProjPermitted κ (ixAddr a) := semantic.proj_permitted loaded address
      have shorter : children.length < fuel := by rw [events] at length; simp only [List.length_cons, List.length_append] at length; omega
      obtain ⟨I', hi⟩ := ih children.length shorter (Nat.le_refl _)
        (bounded_sub (fun _ inside => by rw [events]; simp [inside]) bounded)
        ⟨_, inner⟩ argument child
      subst result heap
      exact ⟨_, .proj (by simp)
        (Bytes.repAddressRef_heapMono₂ addrTy (child.heap_extends.trans (Heap.Extends.snoc _ _)) address)
        (hi.mono (Heap.Extends.snoc _ _))⟩
    | .n1_n1_other (ev14 := scan) (ev37 := compare) (sg_nijhquyq := sg) (ld_cazaqiwm := loaded)
        (hne_mrzdkzct := n1) (hne_oicewdsa := n2) (hne_vdmlyytd := n3) (hne_wsfwgpgb := n4)
        (hne_tasugfar := n5) (hne_otxnyqsa := n6) (hc_aynotxpb := events) .. =>
      obtain ⟨same, _⟩ := represented.lbr
        (bounded_sub (fun _ inside => by rw [events]; simp [inside]) bounded) scan
      obtain ⟨d, limitField, hd, hl, _, _, verdict, unchanged⟩ := SubstAux.ltf compare
      injection hd with hd
      subst d same unchanged
      have segEq := raw_inst1_seg_heap κ bounded (fun _ inside => by rw [events]; simp [inside]) sg
      subst segEq
      obtain ⟨-, hlbr⟩ := SubstAux.expr_lbr_other_zero loaded n1 n2 n3 n4 n5 n6 scan
      rw [hlbr] at hl
      injection hl with hl
      subst limitField
      have below := SubstAux.ltf_one verdict.symm
      rw [ZMod.val_zero] at below; omega
    | .n1_other (ev14 := scan) (ev37 := compare) (sg_nijhquyq := sg)
        (hne133 := notOne) (op172 := added) (ev142 := lowered) (hc174 := events) .. =>
      obtain ⟨same, _⟩ := represented.lbr
        (bounded_sub (fun _ inside => by rw [events]; simp [inside]) bounded) scan
      obtain ⟨d, _, hd, _, small, _, _, unchanged⟩ := SubstAux.ltf compare
      injection hd with hd
      subst d same unchanged
      cases sg with
      | n0 _ _ _ _ _ hr0 _ _ => exact absurd hr0 notOne
      | n1 _ _ _ _ _ ev1 occurrence hc_sg =>
        obtain ⟨_, _, _, _, _, _, _, rfl⟩ := SubstAux.ltf ev1
        obtain ⟨sameOccurrence, binary, noVar⟩ := represented.occurs
          (bounded_sub (fun _ inside => by rw [events, hc_sg]; simp [inside]) bounded) occurrence
        subst sameOccurrence
        have zero := SubstAux.zero_of_ne_one binary notOne
        have absent := noVar zero
        rw [SubstAux.add_ok added] at lowered
        have result := represented.lower
          (bounded_sub (fun _ inside => by rw [events]; simp [inside]) bounded)
          (by rw [SubstAux.val_one, SubstAux.val_succ32 small]; omega) lowered
        rw [SubstAux.val_one, SubstAux.val_succ32 small, Nat.add_sub_cancel] at result
        rw [instantiate1Lift_of_absent absent]
        exact result

/-- Actual capture-avoiding substitution preserves all raw syntax and metadata. The output
retains the body's old variable bound as a conservative upper bound; it does not add a binder
to the expression or assume a semantic reduction certificate. -/
theorem RawExprRep.inst1 {κ : _root_.Address → KKey} {h h' : Heap F} {n : Nat}
    {B V : KExpr} {p arg r : SourceValue F} {depth : F} {calls : List (Call F)}
    (body : RawExprRep κ h (n + depth.val + 1) B p)
    (argument : RawExprRep κ h n V arg) (bounded : IxVM.Consistency.Bounded calls)
    (observed : ObsFn W "KernelSubst::expr_inst1" [p, arg, .field depth] h r h' calls) :
    RawExprRep κ h' (n + depth.val + 1) (B.instantiate1Lift V depth.val) r :=
  raw_inst_go κ calls.length (Nat.le_refl _) bounded body argument observed


end IxVM.Refinement.Decl
