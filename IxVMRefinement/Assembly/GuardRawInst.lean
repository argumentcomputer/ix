import IxVMRefinement.Assembly.GuardRawSubst
import IxC.Kernel.Inductives.StructParts

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

/-- The actual variable substitution primitive lifts an open argument under the consumed
binders and preserves the complete raw result. The retained bound is an upper bound only. -/
theorem raw_inst1_bvar_exact {κ : _root_.Address → KKey} {h h' : Heap F}
    {n : Nat} {R : KExpr} {i depth : F} {arg r : SourceValue F} {calls : List (Call F)}
    (small : i.val < 9223372036854775808) (inside : i.val < n + depth.val + 1)
    (argument : RawExprRep κ h n R arg) (bounded : IxVM.Consistency.Bounded calls)
    (observed : ObsFn W "KernelSubst::expr_inst1_bvar"
      [.field i, arg, .field depth] h r h' calls) :
    RawExprRep κ h' (n + depth.val + 1) ((.bvar i.val : KExpr).instantiate1Lift R depth.val) r := by
  match Obs.«KernelSubst::expr_inst1_bvar».obs observed with
  | .n1 (m2 := after) (ev15 := comparison) (he40 := result) (hm39 := heap) .. =>
    obtain ⟨i', depth', hi, hd, _, _, verdict, unchanged⟩ := SubstAux.ltf comparison
    injection hi with hi; injection hd with hd
    subst i' depth' unchanged result heap
    have below := SubstAux.ltf_one verdict.symm
    have rep : RawExprRep κ (after ++ [.construct kexprEnum "BVar" [.field i]])
        (n + depth.val + 1) (.bvar i.val) (.ptr (.enum kexprEnum) after.length) :=
      ⟨_, .bvarLocal (by simp) small inside⟩
    simpa [Expr.instantiate1Lift, show i.val ≠ depth.val by omega, show ¬ depth.val < i.val by omega] using rep
  | .n0_n0 (ev15 := comparison) (op74 := subtracted) (ev86 := lifted) (hc110 := events) .. =>
    obtain ⟨i', depth', hi, hd, _, depthBound, _, unchanged⟩ := SubstAux.ltf comparison
    injection hi with hi; injection hd with hd
    subst i' depth' unchanged
    have same : i = depth := by
      have equal := SubstAux.sub_ok subtracted
      injection equal with zero
      exact sub_eq_zero.mp zero.symm
    subst i
    have rawLift := argument.lift
      (bounded_sub (fun _ member => by rw [events]; simp [member]) bounded) (by omega) lifted
    simpa only [Expr.instantiate1Lift, ite_true, ZMod.val_zero] using rawLift.weaken (k' := n + depth.val + 1) (by omega)
  | .n0_other (m2 := after) (ev15 := comparison) (op74 := subtracted) (hne111 := different)
      (he119 := result) (hm118 := heap) (op137 := lowered) .. =>
    obtain ⟨i', depth', hi, hd, _, _, verdict, unchanged⟩ := SubstAux.ltf comparison
    injection hi with hi; injection hd with hd
    subst i' depth' unchanged result heap
    have above := SubstAux.ltf_zero verdict.symm
    have distinct : i ≠ depth := fun equal => different (by rw [SubstAux.sub_ok subtracted, equal, sub_self])
    have valuesDistinct : i.val ≠ depth.val := fun equal => distinct (ZMod.val_injective _ equal)
    rw [SubstAux.sub_ok lowered]
    have difference : (i - 1).val = i.val - 1 := by
      rw [SubstAux.val_sub (by rw [SubstAux.val_one]; omega), SubstAux.val_one]
    have rep : RawExprRep κ (after ++ [.construct kexprEnum "BVar" [.field (i - 1)]])
        (n + depth.val + 1) (.bvar (i - 1).val) (.ptr (.enum kexprEnum) after.length) :=
      ⟨_, .bvarLocal (by simp) (by rw [difference]; omega) (by rw [difference]; omega)⟩
    simpa [Expr.instantiate1Lift, valuesDistinct, show depth.val < i.val by omega, difference] using rep

private def rawInstName (walk : Bool) : String :=
  if walk then "KernelSubst::expr_inst1_walk" else "KernelSubst::expr_inst1"

private theorem raw_inst_go (κ : _root_.Address → KKey) :
    ∀ fuel : Nat, ∀ (walk : Bool) {n : Nat} {B V : KExpr} {depth : F}
      {p arg r : SourceValue F} {h h' : Heap F} {calls : List (Call F)},
      calls.length ≤ fuel → IxVM.Consistency.Bounded calls →
      (walk = true → depth.val < 4294967296) →
      RawExprRep κ h (n + depth.val + 1) B p → RawExprRep κ h n V arg →
      ObsFn W (rawInstName walk) [p, arg, .field depth] h r h' calls →
      RawExprRep κ h' (n + depth.val + 1) (B.instantiate1Lift V depth.val) r := by
  intro fuel
  induction fuel using Nat.strong_induction_on with
  | h fuel ih =>
    intro walk n B V depth p arg r h h' calls length bounded depthBound represented argument observed
    cases walk with
    | false =>
      change ObsFn W "KernelSubst::expr_inst1" [p, arg, .field depth] h r h' calls at observed
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
      | .n1_n1 (cs105 := children) (ev14 := scan) (ev37 := compare)
          (ev81 := occurrence) (ev107 := child) (hc132 := events) .. =>
        obtain ⟨same, _⟩ := represented.lbr
          (bounded_sub (fun _ inside => by rw [events]; simp [inside]) bounded) scan
        obtain ⟨d, limit, hd, _, small, _, _, unchanged⟩ := SubstAux.ltf compare
        injection hd with hd
        subst d same unchanged
        obtain ⟨sameOccurrence, _⟩ := represented.occurs
          (bounded_sub (fun _ inside => by rw [events]; simp [inside]) bounded) occurrence
        subst sameOccurrence
        have shorter : children.length < fuel := by
          rw [events] at length; simp only [List.length_cons, List.length_append] at length; omega
        exact ih children.length shorter true (Nat.le_refl _)
          (bounded_sub (fun _ inside => by rw [events]; simp [inside]) bounded)
          (fun _ => small) represented argument child
      | .n1_other (ev14 := scan) (ev37 := compare) (ev81 := occurrence)
          (hne133 := notOne) (op172 := added) (ev142 := lowered) (hc174 := events) .. =>
        obtain ⟨same, _⟩ := represented.lbr
          (bounded_sub (fun _ inside => by rw [events]; simp [inside]) bounded) scan
        obtain ⟨d, limit, hd, _, small, _, _, unchanged⟩ := SubstAux.ltf compare
        injection hd with hd
        subst d same unchanged
        obtain ⟨sameOccurrence, binary, noVar⟩ := represented.occurs
          (bounded_sub (fun _ inside => by rw [events]; simp [inside]) bounded) occurrence
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
    | true =>
      change ObsFn W "KernelSubst::expr_inst1_walk" [p, arg, .field depth] h r h' calls at observed
      have depthSmall := depthBound rfl
      obtain ⟨E, rep⟩ := represented
      match Obs.«KernelSubst::expr_inst1_walk».obs observed with
      | .BVar (ld12 := loaded) (ev30 := child) (hc55 := events) .. =>
        obtain ⟨i, rfl, rfl, small, inside⟩ := rep.raw_bvar_view loaded
        exact raw_inst1_bvar_exact small inside argument
          (bounded_sub (fun _ member => by rw [events]; simp [member]) bounded) child
      | .Srt (ld12 := loaded) (he72 := result) (hm71 := heap) .. =>
        obtain ⟨u, rfl, rfl, level⟩ := rep.raw_sort_view loaded
        subst result heap
        exact ⟨_, .sort (by simp) (level.mono (Heap.Extends.snoc _ _))⟩
      | .Const (ld12 := loaded) (he106 := result) (hm105 := heap) .. =>
        have semantic := rep.toTmExact.toTm
        obtain ⟨a, levels, rfl, rfl, address, levelsRep⟩ := rep.raw_const_view loaded
        have : Resolved (κ (ixAddr a)) := ⟨semantic.const_key_ne⟩
        subst result heap
        exact ⟨_, .const (by simp)
          (Bytes.repAddressRef_heapMono₂ addrTy (Heap.Extends.snoc _ _) address)
          (levelsRep.mono (Heap.Extends.snoc _ _))⟩
      | .Lit (ld12 := loaded) (he554 := result) (hm553 := heap) .. =>
        subst result heap
        cases rep with
        | litNat cell limbs canonical =>
          obtain ⟨_, fields⟩ := load_cell cell loaded
          injection fields with same
          subst same
          exact ⟨_, .litNat (by simp) (repList_heapMono₂ limbListEnum repU64_heapMono₂ (Heap.Extends.snoc _ _) limbs) canonical⟩
        | litStr cell bytes string =>
          obtain ⟨_, fields⟩ := load_cell cell loaded
          injection fields with same
          subst same
          exact ⟨_, .litStr (by simp)
            (Bytes.repByteStream_heapMono₂ _ (Heap.Extends.snoc _ _) bytes) string⟩
        | bvarLocal cell _ _ | bvarFree cell _ _ _ | sort cell _ | const cell _ _
        | app cell _ _ | lam cell _ _ _ | forallE cell _ _ _ | letE cell _ _ _ | proj cell _ _ =>
          exact (load_cell_ne cell loaded (by decide)).elim
      | .App (cs163 := first) (cs199 := second) (ld12 := loaded) (he148 := result) (hm147 := heap)
          (ev165 := e1) (ev201 := e2) (hc226 := events) .. =>
        obtain ⟨RF, RA, EF, EA, rfl, rfl, func, arg⟩ := rep.raw_app_view loaded
        have short1 : first.length < fuel := by rw [events] at length; simp only [List.length_cons, List.length_append] at length; omega
        have short2 : second.length < fuel := by rw [events] at length; simp only [List.length_cons, List.length_append] at length; omega
        obtain ⟨F', hf⟩ := ih first.length short1 false (Nat.le_refl _)
          (bounded_sub (fun _ inside => by rw [events]; simp [inside]) bounded)
          (by intro impossible; cases impossible) ⟨_, func⟩ argument e1
        obtain ⟨A', ha⟩ := ih second.length short2 false (Nat.le_refl _)
          (bounded_sub (fun _ inside => by rw [events]; simp [inside]) bounded)
          (by intro impossible; cases impossible) ⟨_, arg.mono e1.heap_extends⟩ (argument.mono e1.heap_extends) e2
        subst result heap
        exact ⟨_, .app (by simp) (hf.mono (e2.heap_extends.trans (Heap.Extends.snoc _ _)))
          (ha.mono (Heap.Extends.snoc _ _))⟩
      | .Lam (v258 := bodyOut) (cs269 := first) (cs305 := second) (ld12 := loaded) (he253 := result) (hm252 := heap)
          (ev271 := e1) (op338 := added) (ev307 := e2) (hc347 := events) .. =>
        obtain ⟨RD, RB, ED, EB, u, rfl, rfl, dom, body, level⟩ := rep.raw_lam_view loaded
        rw [SubstAux.add_ok added] at e2
        have short1 : first.length < fuel := by rw [events] at length; simp only [List.length_cons, List.length_append] at length; omega
        have short2 : second.length < fuel := by rw [events] at length; simp only [List.length_cons, List.length_append] at length; omega
        obtain ⟨D', hd⟩ := ih first.length short1 false (Nat.le_refl _)
          (bounded_sub (fun _ inside => by rw [events]; simp [inside]) bounded)
          (by intro impossible; cases impossible) ⟨_, dom⟩ argument e1
        obtain ⟨B', hb⟩ := ih second.length short2 false (Nat.le_refl _)
          (bounded_sub (fun _ inside => by rw [events]; simp [inside]) bounded)
          (by intro impossible; cases impossible) (by
            rw [SubstAux.val_succ32 depthSmall]
            exact ⟨EB, by simpa only [Nat.add_assoc] using body.mono e1.heap_extends⟩)
          (argument.mono e1.heap_extends) e2
        rw [SubstAux.val_succ32 depthSmall] at hb
        subst result heap
        refine ⟨.lam D' B' (bmeta u), .lam (bp := bodyOut) (by simp) (hd.mono (e2.heap_extends.trans (Heap.Extends.snoc _ _))) ?_
          (level.mono (e1.heap_extends.trans (e2.heap_extends.trans (Heap.Extends.snoc _ _))))⟩
        simpa only [Nat.add_assoc] using hb.mono (Heap.Extends.snoc _ _)
      | .Forall (v379 := bodyOut) (cs390 := first) (cs426 := second) (ld12 := loaded) (he374 := result) (hm373 := heap)
          (ev392 := e1) (op459 := added) (ev428 := e2) (hc468 := events) .. =>
        obtain ⟨RD, RB, ED, EB, u, rfl, rfl, dom, body, level⟩ := rep.raw_forallE_view loaded
        rw [SubstAux.add_ok added] at e2
        have short1 : first.length < fuel := by rw [events] at length; simp only [List.length_cons, List.length_append] at length; omega
        have short2 : second.length < fuel := by rw [events] at length; simp only [List.length_cons, List.length_append] at length; omega
        obtain ⟨D', hd⟩ := ih first.length short1 false (Nat.le_refl _)
          (bounded_sub (fun _ inside => by rw [events]; simp [inside]) bounded)
          (by intro impossible; cases impossible) ⟨_, dom⟩ argument e1
        obtain ⟨B', hb⟩ := ih second.length short2 false (Nat.le_refl _)
          (bounded_sub (fun _ inside => by rw [events]; simp [inside]) bounded)
          (by intro impossible; cases impossible) (by
            rw [SubstAux.val_succ32 depthSmall]
            exact ⟨EB, by simpa only [Nat.add_assoc] using body.mono e1.heap_extends⟩)
          (argument.mono e1.heap_extends) e2
        rw [SubstAux.val_succ32 depthSmall] at hb
        subst result heap
        refine ⟨.forallE D' B' (bmeta u), .forallE (bp := bodyOut) (by simp) (hd.mono (e2.heap_extends.trans (Heap.Extends.snoc _ _))) ?_
          (level.mono (e1.heap_extends.trans (e2.heap_extends.trans (Heap.Extends.snoc _ _))))⟩
        simpa only [Nat.add_assoc] using hb.mono (Heap.Extends.snoc _ _)
      | .Let (ld12 := loaded) (ev496 := helper) (hc537 := events) .. =>
        obtain ⟨RT, RV, RB, ET, EV, EB, rfl, rfl, type, value, body⟩ := rep.raw_let_view loaded
        match Obs.«KernelSubst::expr_inst1_let».obs helper with
        | .run (v11 := bodyOut) (cs21 := first) (cs57 := second) (cs93 := third) (he5 := result) (hm4 := heap)
            (ev23 := e1) (ev59 := e2) (op126 := added) (ev95 := e3) (hc128 := nested) .. =>
          rw [SubstAux.add_ok added] at e3
          have short1 : first.length < fuel := by rw [events, nested] at length; simp only [List.length_cons, List.length_append] at length; omega
          have short2 : second.length < fuel := by rw [events, nested] at length; simp only [List.length_cons, List.length_append] at length; omega
          have short3 : third.length < fuel := by rw [events, nested] at length; simp only [List.length_cons, List.length_append] at length; omega
          obtain ⟨T', ht⟩ := ih first.length short1 false (Nat.le_refl _)
            (bounded_sub (fun _ inside => by rw [events, nested]; simp [inside]) bounded)
            (by intro impossible; cases impossible) ⟨_, type⟩ argument e1
          obtain ⟨V', hv⟩ := ih second.length short2 false (Nat.le_refl _)
            (bounded_sub (fun _ inside => by rw [events, nested]; simp [inside]) bounded)
            (by intro impossible; cases impossible) ⟨_, value.mono e1.heap_extends⟩ (argument.mono e1.heap_extends) e2
          obtain ⟨B', hb⟩ := ih third.length short3 false (Nat.le_refl _)
            (bounded_sub (fun _ inside => by rw [events, nested]; simp [inside]) bounded)
            (by intro impossible; cases impossible)
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
      | .Proj (cs623 := children) (ld12 := loaded) (he593 := result) (hm592 := heap)
          (ev625 := child) (hc650 := events) .. =>
        have semantic := rep.toTmExact.toTm
        obtain ⟨a, index, RI, EI, rfl, rfl, rfl, address, inner⟩ := rep.raw_proj_view loaded
        have : Resolved (κ (ixAddr a)) := ⟨semantic.proj_key_ne⟩
        have : ProjPermitted κ (ixAddr a) := semantic.proj_permitted loaded address
        have shorter : children.length < fuel := by rw [events] at length; simp only [List.length_cons] at length; omega
        obtain ⟨I', hi⟩ := ih children.length shorter false (Nat.le_refl _)
          (bounded_sub (fun _ inside => by rw [events]; simp [inside]) bounded)
          (by intro impossible; cases impossible) ⟨_, inner⟩ argument child
        subst result heap
        exact ⟨_, .proj (by simp)
          (Bytes.repAddressRef_heapMono₂ addrTy (child.heap_extends.trans (Heap.Extends.snoc _ _)) address)
          (hi.mono (Heap.Extends.snoc _ _))⟩

/-- Actual capture-avoiding substitution preserves all raw syntax and metadata. The output
retains the body's old variable bound as a conservative upper bound; it does not add a binder
to the expression or assume a semantic reduction certificate. -/
theorem RawExprRep.inst1 {κ : _root_.Address → KKey} {h h' : Heap F} {n : Nat}
    {B V : KExpr} {p arg r : SourceValue F} {depth : F} {calls : List (Call F)}
    (body : RawExprRep κ h (n + depth.val + 1) B p)
    (argument : RawExprRep κ h n V arg) (bounded : IxVM.Consistency.Bounded calls)
    (observed : ObsFn W "KernelSubst::expr_inst1" [p, arg, .field depth] h r h' calls) :
    RawExprRep κ h' (n + depth.val + 1) (B.instantiate1Lift V depth.val) r :=
  raw_inst_go κ calls.length false (Nat.le_refl _) bounded
    (by intro impossible; cases impossible) body argument observed


end IxVM.Refinement.Decl
