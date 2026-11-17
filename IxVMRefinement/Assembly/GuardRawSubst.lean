import IxVMRefinement.Assembly.GuardRawExact

/-! # Exact raw syntax for capture-avoiding binder substitution

The raw expression keeps its let cells and binder metadata. The semantic reading is retained
existentially because raw head computation does not need a licensed reduction judgement.
-/

namespace IxVM.Refinement.Decl

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open IxVM.Refinement.Core
open IxVM.Refinement.Core.Specs.Subst (IdxAll IdxLt)
open IxVM.Refinement.KernelLevels (RepKLevel RepKLevelList)
open Ix.Kernel (Expr)

set_option maxHeartbeats 2400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-- A completely specified raw expression with a bound on its ambient de Bruijn variables. -/
def RawExprRep (κ : _root_.Address → KKey) (h : Heap F) (k : Nat) (R : KExpr)
    (p : SourceValue F) : Prop :=
  ∃ E, RawTmExact κ 0 (fun _ => default) h k R E p

/-- A successful scoped reading supplies an exact physical raw expression. No equality with
the original semantic expression is claimed: its universe syntax may have been weakened. -/
theorem RawExprRep.ofOpenTm {κ : _root_.Address → KKey} {Γ : Nat → KExpr}
    {h : Heap F} {d k : Nat} {E : KExpr} {p : SourceValue F}
    (represented : Tm κ d Γ h k E p) : ∃ R, RawExprRep κ h (k + d) R p := by
  induction represented with
  | bvarLocal cell small inside => exact ⟨_, _, .bvarLocal cell small (by omega)⟩
  | bvarFree cell small lower upper => exact ⟨_, _, .bvarLocal cell small (by omega)⟩
  | sort cell level _ => exact ⟨_, _, .sort cell level⟩
  | const cell address levels _ => exact ⟨_, _, .const cell address levels⟩
  | app cell _ _ left right =>
    obtain ⟨RF, EF, func⟩ := left
    obtain ⟨RA, EA, arg⟩ := right
    exact ⟨_, _, .app cell func arg⟩
  | lam cell _ _ level dom body =>
    obtain ⟨RD, ED, domain⟩ := dom
    obtain ⟨RB, EB, tail⟩ := body
    exact ⟨_, _, .lam cell domain (by simpa only [Nat.add_right_comm] using tail) level⟩
  | forallE cell _ _ level dom body =>
    obtain ⟨RD, ED, domain⟩ := dom
    obtain ⟨RB, EB, tail⟩ := body
    exact ⟨_, _, .forallE cell domain (by simpa only [Nat.add_right_comm] using tail) level⟩
  | letE cell _ _ _ type value body =>
    obtain ⟨RT, ET, typeRep⟩ := type
    obtain ⟨RV, EV, valueRep⟩ := value
    obtain ⟨RB, EB, tail⟩ := body
    exact ⟨_, _, .letE cell typeRep valueRep (by simpa only [Nat.add_right_comm] using tail)⟩
  | litNat cell limbs canonical => exact ⟨_, _, .litNat cell limbs canonical⟩
  | litStr cell bytes string => exact ⟨_, _, .litStr cell bytes string⟩
  | proj cell address _ inner =>
    obtain ⟨RI, EI, rep⟩ := inner
    exact ⟨_, _, .proj cell address rep⟩

/-- The depth-zero specialization keeps its original local bound. -/
theorem RawExprRep.ofTm {κ : _root_.Address → KKey} {Γ : Nat → KExpr}
    {h : Heap F} {k : Nat} {E : KExpr} {p : SourceValue F}
    (represented : Tm κ 0 Γ h k E p) : ∃ R, RawExprRep κ h k R p := by
  simpa only [Nat.add_zero] using RawExprRep.ofOpenTm represented

/-- The actual raw universe operation preserves this physical syntax with exact metadata. -/
theorem RawExprRep.instLevels {κ : _root_.Address → KKey} {h h' : Heap F} {k : Nat}
    {R : KExpr} {p params r : SourceValue F} {levels : List Ix.Kernel.Level}
    {calls : List (Call F)} (represented : RawExprRep κ h k R p)
    (parameters : RepKLevelList h levels params)
    (observed : ObsFn W "KernelGuard::expr_inst_raw" [p, params] h r h' calls) :
    RawExprRep κ h' k (R.instantiateLevelParams (List.range levels.length) levels) r := by
  obtain ⟨E, rep⟩ := represented
  exact ⟨_, expr_inst_raw_exact rep parameters observed⟩

/-- Enlarging the ambient variable bound preserves both exact readings. -/
theorem RawTmExact.weaken_bound {κ : _root_.Address → KKey} {Γ : Nat → KExpr}
    {h : Heap F} {k : Nat} {R E : KExpr} {p : SourceValue F}
    (rep : RawTmExact κ 0 Γ h k R E p) :
    ∀ {k'}, k ≤ k' → RawTmExact κ 0 Γ h k' R E p := by
  induction rep with
  | bvarLocal cell small inside => intro k' bound; exact .bvarLocal cell small (by omega)
  | bvarFree _ _ _ impossible => omega
  | sort cell level => intro k' _; exact .sort cell level
  | const cell address levels => intro k' _; exact .const cell address levels
  | app cell _ _ left right => intro k' bound; exact .app cell (left bound) (right bound)
  | lam cell _ _ level dom body =>
    intro k' bound; exact .lam cell (dom bound) (body (by omega)) level
  | forallE cell _ _ level dom body =>
    intro k' bound; exact .forallE cell (dom bound) (body (by omega)) level
  | letE cell _ _ _ type value body =>
    intro k' bound; exact .letE cell (type bound) (value bound) (body (by omega))
  | litNat cell limbs canonical => intro k' _; exact .litNat cell limbs canonical
  | litStr cell bytes string => intro k' _; exact .litStr cell bytes string
  | proj cell address _ inner => intro k' bound; exact .proj cell address (inner bound)

theorem RawExprRep.mono {κ : _root_.Address → KKey} {h h' : Heap F} {k : Nat}
    {R : KExpr} {p : SourceValue F} (represented : RawExprRep κ h k R p)
    (extension : Heap.Extends h h') : RawExprRep κ h' k R p := by
  obtain ⟨E, rep⟩ := represented
  exact ⟨E, rep.mono extension⟩

theorem RawExprRep.weaken {κ : _root_.Address → KKey} {h : Heap F} {k k' : Nat}
    {R : KExpr} {p : SourceValue F} (represented : RawExprRep κ h k R p)
    (bound : k ≤ k') : RawExprRep κ h k' R p := by
  obtain ⟨E, rep⟩ := represented
  exact ⟨E, rep.weaken_bound bound⟩

/-- Heap index bounds apply to all raw syntax, including the type and value of every let. -/
theorem RawTmExact.raw_bounded_of_idx {κ : _root_.Address → KKey} {Γ : Nat → KExpr}
    {h : Heap F} {k : Nat} {R E : KExpr} {p : SourceValue F}
    (rep : RawTmExact κ 0 Γ h k R E p) :
    ∀ {m bound}, IdxAll h (fun n i => i.val < bound + n) m p →
      R.looseBVarsBounded (bound + m) = true := by
  induction rep with
  | bvarLocal cell small inside =>
    intro m bound indices
    obtain ⟨i, equal, below⟩ := SubstAux.idxAll_bvar_inv indices (loadValue_enum_cell cell)
    injection equal with equal
    subst equal
    exact decide_eq_true below
  | bvarFree _ _ _ impossible => omega
  | sort | const | litNat | litStr => intro _ _ _; rfl
  | app cell _ _ left right =>
    intro m bound indices
    obtain ⟨func, arg⟩ := SubstAux.idxAll_app_inv indices (loadValue_enum_cell cell)
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true]
    exact ⟨left func, right arg⟩
  | lam cell _ _ _ dom body =>
    intro m bound indices
    obtain ⟨domain, tail⟩ := SubstAux.idxAll_lam_inv indices (loadValue_enum_cell cell)
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true]
    exact ⟨dom domain, by simpa only [Nat.add_assoc] using body tail⟩
  | forallE cell _ _ _ dom body =>
    intro m bound indices
    obtain ⟨domain, tail⟩ := SubstAux.idxAll_forallE_inv indices (loadValue_enum_cell cell)
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true]
    exact ⟨dom domain, by simpa only [Nat.add_assoc] using body tail⟩
  | letE cell _ _ _ type value body =>
    intro m bound indices
    obtain ⟨typeIndices, valueIndices, tail⟩ := SubstAux.idxAll_letE_inv indices (loadValue_enum_cell cell)
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true]
    exact ⟨⟨type typeIndices, value valueIndices⟩,
      by simpa only [Nat.add_assoc] using body tail⟩
  | proj cell address _ inner =>
    intro m bound indices
    exact inner (SubstAux.idxAll_proj_inv indices (loadValue_enum_cell cell))

/-- The actual loose-bound scan gives a bound on the retained raw syntax, not only its
let-erased semantic image. -/
theorem RawExprRep.lbr {κ : _root_.Address → KKey} {h h' : Heap F} {k : Nat}
    {R : KExpr} {p r : SourceValue F} {calls : List (Call F)}
    (represented : RawExprRep κ h k R p) (bounded : IxVM.Consistency.Bounded calls)
    (observed : ObsFn W "KernelSubst::expr_lbr" [p] h r h' calls) :
    h' = h ∧ ∃ (bound : Nat), r = .field (bound : F) ∧ bound ≤ 9223372036854775808 ∧
      R.looseBVarsBounded bound = true := by
  obtain ⟨E, rep⟩ := represented
  obtain ⟨unchanged, scan⟩ := SubstAux.gall κ .expr_lbr _ _ _ _ _ observed p rfl bounded
  obtain ⟨bound, result, small, _, indices, _⟩ := scan 0 (fun _ => default) k E rep.toTmExact.toTm
  refine ⟨unchanged, bound, result, small, ?_⟩
  simpa only [Nat.add_zero] using rep.raw_bounded_of_idx indices

/-- The actual lifted-variable primitive preserves the exact de Bruijn index. The successful
comparison bounds the input by 2^32; the explicit shift bound prevents field wraparound. -/
theorem raw_lift_bvar_exact {κ : _root_.Address → KKey} {h h' : Heap F}
    {k : Nat} {i shift cutoff : F} {r : SourceValue F} {calls : List (Call F)}
    (small : i.val < 9223372036854775808) (inside : i.val < k)
    (shiftBound : shift.val < 4611686018427387904)
    (observed : ObsFn W "KernelSubst::expr_lift_bvar"
      [.field i, .field shift, .field cutoff] h r h' calls) :
    RawExprRep κ h' (k + shift.val)
      ((.bvar i.val : KExpr).liftLooseBVars shift.val cutoff.val) r := by
  cases Obs.«KernelSubst::expr_lift_bvar».obs observed with
  | n1 m2 childCalls comparison result heap events =>
    obtain ⟨i', cutoff', hi, hc, _, _, verdict, rfl⟩ := SubstAux.ltf comparison
    injection hi with hi; injection hc with hc
    subst hi hc result heap
    have below := SubstAux.ltf_one verdict.symm
    have rep : RawExprRep κ (m2 ++ [.construct kexprEnum "BVar" [.field i]])
        (k + shift.val) (.bvar i.val) (.ptr (.enum kexprEnum) m2.length) :=
      ⟨_, .bvarLocal (by simp) small (by omega)⟩
    simpa [Expr.liftLooseBVars, show ¬ cutoff.val ≤ i.val by omega] using rep
  | n0 m2 childCalls value comparison result heap added events =>
    obtain ⟨i', cutoff', hi, hc, inputBound, _, verdict, rfl⟩ := SubstAux.ltf comparison
    injection hi with hi; injection hc with hc
    subst hi hc result heap
    have above := SubstAux.ltf_zero verdict.symm
    rw [SubstAux.add_ok added]
    have sumValue : (i + shift).val = i.val + shift.val :=
      SubstAux.val_add (by
        have : Aiur.Library.U32.Goldilocks.modulus = 18446744069414584321 := rfl
        omega)
    have rep : RawExprRep κ (m2 ++ [.construct kexprEnum "BVar" [.field (i + shift)]])
        (k + shift.val) (.bvar (i + shift).val) (.ptr (.enum kexprEnum) m2.length) :=
      ⟨_, .bvarLocal (by simp) (by rw [sumValue]; omega) (by rw [sumValue]; omega)⟩
    simpa [Expr.liftLooseBVars, show cutoff.val ≤ i.val by omega, sumValue] using rep


theorem RawTmExact.raw_bvar_view {κ : _root_.Address → KKey} {Γ : Nat → KExpr}
    {h : Heap F} {k : Nat} {R E : KExpr} {p value : SourceValue F}
    (rep : RawTmExact κ 0 Γ h k R E p)
    (loaded : loadValue h p = .ok (.construct kexprEnum "BVar" [value])) :
    ∃ (i : F), value = .field i ∧ R = .bvar i.val ∧
      i.val < 9223372036854775808 ∧ i.val < k := by
  cases rep with
  | bvarLocal cell small inside =>
    obtain ⟨_, fields⟩ := load_cell cell loaded
    injection fields with equal
    subst equal
    exact ⟨_, rfl, rfl, small, inside⟩
  | bvarFree _ _ _ impossible => omega
  | sort cell _ | const cell _ _ | app cell _ _ | lam cell _ _ _
  | forallE cell _ _ _ | letE cell _ _ _ | litNat cell _ _
  | litStr cell _ _ | proj cell _ _ => exact (load_cell_ne cell loaded (by decide)).elim

private theorem lift_zero (R : KExpr) (cutoff : Nat) : R.liftLooseBVars 0 cutoff = R := by
  induction R generalizing cutoff <;> simp_all [Expr.liftLooseBVars]

private def rawLiftName (walk : Bool) : String :=
  if walk then "KernelSubst::expr_lift_walk" else "KernelSubst::expr_lift"

private theorem raw_lift_go (κ : _root_.Address → KKey) :
    ∀ fuel : Nat, ∀ (walk : Bool) {k : Nat} {R : KExpr} {shift cutoff : F}
      {p r : SourceValue F} {h h' : Heap F} {calls : List (Call F)},
      calls.length ≤ fuel → IxVM.Consistency.Bounded calls →
      shift.val < 4611686018427387904 →
      (walk = true → cutoff.val < 4294967296) →
      RawExprRep κ h k R p →
      ObsFn W (rawLiftName walk) [p, .field shift, .field cutoff] h r h' calls →
      RawExprRep κ h' (k + shift.val) (R.liftLooseBVars shift.val cutoff.val) r := by
  intro fuel
  induction fuel using Nat.strong_induction_on with
  | h fuel ih =>
    intro walk k R shift cutoff p r h h' calls length bounded shiftBound cutoffBound represented observed
    cases walk with
    | false =>
      change ObsFn W "KernelSubst::expr_lift" [p, .field shift, .field cutoff] h r h' calls at observed
      match Obs.«KernelSubst::expr_lift».obs observed with
      | .n0 (hv14 := zero) (he16 := result) (he17 := heap) .. =>
        injection zero with zero
        subst shift result heap
        simpa only [ZMod.val_zero, Nat.add_zero, lift_zero] using represented
      | .other_n0 (ev36 := scan) (ev59 := compare) (he81 := result) (he82 := heap) (hc83 := events) .. =>
        obtain ⟨same, limit, readLimit, limitBound, closed⟩ := represented.lbr
          (bounded_sub (fun _ inside => by rw [events]; simp [inside]) bounded) scan
        obtain ⟨c, limitField, hc, hl, _, _, verdict, unchanged⟩ := SubstAux.ltf compare
        injection hc with hc
        subst c same unchanged result heap
        rw [readLimit] at hl
        injection hl with hl
        subst limitField
        have below := SubstAux.ltf_zero verdict.symm
        rw [SubstAux.val_natCast (SubstAux.lt_mod_of_le_idx limitBound)] at below
        rw [Expr.liftLooseBVars_eq_self (SubstAux.lbb_mono (by omega) closed)]
        exact represented.weaken (by omega)
      | .other_n1 (cs92 := children) (ev36 := scan) (ev59 := compare) (ev94 := child) (hc119 := events) .. =>
        obtain ⟨same, _⟩ := represented.lbr
          (bounded_sub (fun _ inside => by rw [events]; simp [inside]) bounded) scan
        obtain ⟨c, limit, hc, _, small, _, _, unchanged⟩ := SubstAux.ltf compare
        injection hc with hc
        subst c same unchanged
        have shorter : children.length < fuel := by
          rw [events] at length; simp only [List.length_cons, List.length_append] at length; omega
        exact ih children.length shorter true (Nat.le_refl _)
          (bounded_sub (fun _ inside => by rw [events]; simp [inside]) bounded)
          shiftBound (fun _ => small) represented child
    | true =>
      change ObsFn W "KernelSubst::expr_lift_walk" [p, .field shift, .field cutoff] h r h' calls at observed
      have cutoffSmall := cutoffBound rfl
      obtain ⟨E, rep⟩ := represented
      match Obs.«KernelSubst::expr_lift_walk».obs observed with
      | .BVar (ld12 := loaded) (ev30 := child) .. =>
        obtain ⟨i, rfl, rfl, small, inside⟩ := rep.raw_bvar_view loaded
        exact raw_lift_bvar_exact small inside shiftBound child
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
          shiftBound (by intro impossible; cases impossible) ⟨_, func⟩ e1
        obtain ⟨A', ha⟩ := ih second.length short2 false (Nat.le_refl _)
          (bounded_sub (fun _ inside => by rw [events]; simp [inside]) bounded)
          shiftBound (by intro impossible; cases impossible) ⟨_, arg.mono e1.heap_extends⟩ e2
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
          shiftBound (by intro impossible; cases impossible) ⟨_, dom⟩ e1
        obtain ⟨B', hb⟩ := ih second.length short2 false (Nat.le_refl _)
          (bounded_sub (fun _ inside => by rw [events]; simp [inside]) bounded)
          shiftBound (by intro impossible; cases impossible) ⟨_, body.mono e1.heap_extends⟩ e2
        rw [SubstAux.val_succ32 cutoffSmall] at hb
        subst result heap
        refine ⟨.lam D' B' (bmeta u), .lam (bp := bodyOut) (by simp) (hd.mono (e2.heap_extends.trans (Heap.Extends.snoc _ _))) ?_
          (level.mono (e1.heap_extends.trans (e2.heap_extends.trans (Heap.Extends.snoc _ _))))⟩
        simpa only [Nat.add_right_comm] using hb.mono (Heap.Extends.snoc _ _)
      | .Forall (v379 := bodyOut) (cs390 := first) (cs426 := second) (ld12 := loaded) (he374 := result) (hm373 := heap)
          (ev392 := e1) (op459 := added) (ev428 := e2) (hc468 := events) .. =>
        obtain ⟨RD, RB, ED, EB, u, rfl, rfl, dom, body, level⟩ := rep.raw_forallE_view loaded
        rw [SubstAux.add_ok added] at e2
        have short1 : first.length < fuel := by rw [events] at length; simp only [List.length_cons, List.length_append] at length; omega
        have short2 : second.length < fuel := by rw [events] at length; simp only [List.length_cons, List.length_append] at length; omega
        obtain ⟨D', hd⟩ := ih first.length short1 false (Nat.le_refl _)
          (bounded_sub (fun _ inside => by rw [events]; simp [inside]) bounded)
          shiftBound (by intro impossible; cases impossible) ⟨_, dom⟩ e1
        obtain ⟨B', hb⟩ := ih second.length short2 false (Nat.le_refl _)
          (bounded_sub (fun _ inside => by rw [events]; simp [inside]) bounded)
          shiftBound (by intro impossible; cases impossible) ⟨_, body.mono e1.heap_extends⟩ e2
        rw [SubstAux.val_succ32 cutoffSmall] at hb
        subst result heap
        refine ⟨.forallE D' B' (bmeta u), .forallE (bp := bodyOut) (by simp) (hd.mono (e2.heap_extends.trans (Heap.Extends.snoc _ _))) ?_
          (level.mono (e1.heap_extends.trans (e2.heap_extends.trans (Heap.Extends.snoc _ _))))⟩
        simpa only [Nat.add_right_comm] using hb.mono (Heap.Extends.snoc _ _)
      | .Let (ld12 := loaded) (ev496 := helper) (hc537 := events) .. =>
        obtain ⟨RT, RV, RB, ET, EV, EB, rfl, rfl, type, value, body⟩ := rep.raw_let_view loaded
        match Obs.«KernelSubst::expr_lift_let».obs helper with
        | .run (v11 := bodyOut) (cs21 := first) (cs57 := second) (cs93 := third) (he5 := result) (hm4 := heap)
            (ev23 := e1) (ev59 := e2) (op126 := added) (ev95 := e3) (hc128 := nested) .. =>
          rw [SubstAux.add_ok added] at e3
          have short1 : first.length < fuel := by rw [events, nested] at length; simp only [List.length_cons, List.length_append] at length; omega
          have short2 : second.length < fuel := by rw [events, nested] at length; simp only [List.length_cons, List.length_append] at length; omega
          have short3 : third.length < fuel := by rw [events, nested] at length; simp only [List.length_cons, List.length_append] at length; omega
          obtain ⟨T', ht⟩ := ih first.length short1 false (Nat.le_refl _)
            (bounded_sub (fun _ inside => by rw [events, nested]; simp [inside]) bounded)
            shiftBound (by intro impossible; cases impossible) ⟨_, type⟩ e1
          obtain ⟨V', hv⟩ := ih second.length short2 false (Nat.le_refl _)
            (bounded_sub (fun _ inside => by rw [events, nested]; simp [inside]) bounded)
            shiftBound (by intro impossible; cases impossible) ⟨_, value.mono e1.heap_extends⟩ e2
          obtain ⟨B', hb⟩ := ih third.length short3 false (Nat.le_refl _)
            (bounded_sub (fun _ inside => by rw [events, nested]; simp [inside]) bounded)
            shiftBound (by intro impossible; cases impossible)
            ⟨_, body.mono (e1.heap_extends.trans e2.heap_extends)⟩ e3
          rw [SubstAux.val_succ32 cutoffSmall] at hb
          subst result heap
          refine ⟨instShift V' 0 B', .letE (bp := bodyOut) (by simp)
            (ht.mono (e2.heap_extends.trans (e3.heap_extends.trans (Heap.Extends.snoc _ _))))
            (hv.mono (e3.heap_extends.trans (Heap.Extends.snoc _ _))) ?_⟩
          simpa only [Nat.add_right_comm] using hb.mono (Heap.Extends.snoc _ _)
      | .Proj (cs623 := children) (ld12 := loaded) (he593 := result) (hm592 := heap)
          (ev625 := child) (hc650 := events) .. =>
        have semantic := rep.toTmExact.toTm
        obtain ⟨a, index, RI, EI, rfl, rfl, rfl, address, inner⟩ := rep.raw_proj_view loaded
        have : Resolved (κ (ixAddr a)) := ⟨semantic.proj_key_ne⟩
        have : ProjPermitted κ (ixAddr a) := semantic.proj_permitted loaded address
        have shorter : children.length < fuel := by rw [events] at length; simp only [List.length_cons] at length; omega
        obtain ⟨I', hi⟩ := ih children.length shorter false (Nat.le_refl _)
          (bounded_sub (fun _ inside => by rw [events]; simp [inside]) bounded)
          shiftBound (by intro impossible; cases impossible) ⟨_, inner⟩ child
        subst result heap
        exact ⟨_, .proj (by simp)
          (Bytes.repAddressRef_heapMono₂ addrTy (child.heap_extends.trans (Heap.Extends.snoc _ _)) address)
          (hi.mono (Heap.Extends.snoc _ _))⟩

/-- Actual lifting keeps the whole raw expression and binder metadata. The shift bound is
explicit; substitution callers obtain it from the actual 32-bit depth comparison. -/
theorem RawExprRep.lift {κ : _root_.Address → KKey} {h h' : Heap F} {k : Nat}
    {R : KExpr} {p r : SourceValue F} {shift cutoff : F} {calls : List (Call F)}
    (represented : RawExprRep κ h k R p) (bounded : IxVM.Consistency.Bounded calls)
    (shiftBound : shift.val < 4611686018427387904)
    (observed : ObsFn W "KernelSubst::expr_lift" [p, .field shift, .field cutoff] h r h' calls) :
    RawExprRep κ h' (k + shift.val) (R.liftLooseBVars shift.val cutoff.val) r :=
  raw_lift_go κ calls.length false (Nat.le_refl _) bounded shiftBound
    (by intro impossible; cases impossible) represented observed


private theorem lower_eq_self {R : KExpr} {cutoff shift : Nat}
    (closed : R.looseBVarsBounded (cutoff + shift) = true) : R.lowerBVars shift cutoff = R := by
  induction R generalizing cutoff with
  | bvar i =>
    simp only [Expr.looseBVarsBounded, decide_eq_true_eq] at closed
    simp [Expr.lowerBVars, show ¬ cutoff + shift ≤ i by omega]
  | _ => simp_all [Expr.lowerBVars, Expr.looseBVarsBounded, Bool.and_eq_true, Nat.add_right_comm]

private theorem lower_zero (R : KExpr) (cutoff : Nat) : R.lowerBVars 0 cutoff = R := by
  induction R generalizing cutoff <;> simp_all [Expr.lowerBVars]

private def rawLowerName (walk : Bool) : String :=
  if walk then "KernelSubst::expr_lower_walk" else "KernelSubst::expr_lower"

private theorem raw_lower_go (κ : _root_.Address → KKey) :
    ∀ fuel : Nat, ∀ (walk : Bool) {k : Nat} {R : KExpr} {shift cutoff : F}
      {p r : SourceValue F} {h h' : Heap F} {calls : List (Call F)},
      calls.length ≤ fuel → IxVM.Consistency.Bounded calls →
      shift.val ≤ cutoff.val →
      (walk = true → cutoff.val < 4294967296 ∧ ¬ IdxLt h cutoff.val p) →
      RawExprRep κ h k R p →
      ObsFn W (rawLowerName walk) [p, .field shift, .field cutoff] h r h' calls →
      RawExprRep κ h' k (R.lowerBVars shift.val (cutoff.val - shift.val)) r := by
  intro fuel
  induction fuel using Nat.strong_induction_on with
  | h fuel ih =>
    intro walk k R shift cutoff p r h h' calls length bounded shiftBound cutoffBound represented observed
    cases walk with
    | false =>
      change ObsFn W "KernelSubst::expr_lower" [p, .field shift, .field cutoff] h r h' calls at observed
      match Obs.«KernelSubst::expr_lower».obs observed with
      | .n0 (hv14 := zero) (he16 := result) (he17 := heap) .. =>
        injection zero with zero
        subst shift result heap
        simpa only [ZMod.val_zero, Nat.add_zero, Nat.sub_zero, lower_zero] using represented
      | .other_n0 (ev36 := scan) (ev59 := compare) (he81 := result) (he82 := heap) (hc83 := events) .. =>
        obtain ⟨same, limit, readLimit, limitBound, closed⟩ := represented.lbr
          (bounded_sub (fun _ inside => by rw [events]; simp [inside]) bounded) scan
        obtain ⟨c, limitField, hc, hl, _, _, verdict, unchanged⟩ := SubstAux.ltf compare
        injection hc with hc
        subst c same unchanged result heap
        rw [readLimit] at hl
        injection hl with hl
        subst limitField
        have below := SubstAux.ltf_zero verdict.symm
        rw [SubstAux.val_natCast (SubstAux.lt_mod_of_le_idx limitBound)] at below
        rw [lower_eq_self (SubstAux.lbb_mono (by omega) closed)]
        exact represented.weaken (by omega)
      | .other_n1 (cs92 := children) (ev36 := scan) (ev59 := compare) (ev94 := child) (hc119 := events) .. =>
        obtain ⟨E, rep⟩ := represented
        obtain ⟨same, specification⟩ := SubstAux.gall κ .expr_lbr _ _ _ _ _ scan p rfl
          (bounded_sub (fun _ inside => by rw [events]; simp [inside]) bounded)
        obtain ⟨limit, readLimit, limitBound, _, _, minimal, _⟩ :=
          specification 0 (fun _ => default) k E rep.toTmExact.toTm
        obtain ⟨c, limitField, hc, hl, small, _, verdict, unchanged⟩ := SubstAux.ltf compare
        injection hc with hc
        subst c same unchanged
        rw [readLimit] at hl
        injection hl with hl
        subst limitField
        have inside := SubstAux.ltf_one verdict.symm
        rw [SubstAux.val_natCast (SubstAux.lt_mod_of_le_idx limitBound)] at inside
        have shorter : children.length < fuel := by
          rw [events] at length; simp only [List.length_cons, List.length_append] at length; omega
        exact ih children.length shorter true (Nat.le_refl _)
          (bounded_sub (fun _ inside => by rw [events]; simp [inside]) bounded)
          shiftBound (fun _ => ⟨small, minimal _ inside⟩) ⟨_, rep⟩ child
    | true =>
      change ObsFn W "KernelSubst::expr_lower_walk" [p, .field shift, .field cutoff] h r h' calls at observed
      have cutoffSmall := (cutoffBound rfl).1
      have notBelow := (cutoffBound rfl).2
      obtain ⟨E, rep⟩ := represented
      match Obs.«KernelSubst::expr_lower_walk».obs observed with
      | .BVar (ld12 := loaded) (he29 := result) (hm28 := heap) (op47 := subtracted) .. =>
        obtain ⟨i, rfl, rfl, small, inside⟩ := rep.raw_bvar_view loaded
        have above : cutoff.val ≤ i.val := by
          apply Nat.le_of_not_lt
          intro below
          exact notBelow (SubstAux.idxAll_bvar_of_load loaded (by simpa using below))
        subst result heap
        rw [SubstAux.sub_ok subtracted]
        have difference : (i - shift).val = i.val - shift.val := SubstAux.val_sub (by omega)
        have resultRep : RawExprRep κ (h ++ [.construct kexprEnum "BVar" [.field (i - shift)]])
            k (.bvar (i - shift).val) (.ptr (.enum kexprEnum) h.length) :=
          ⟨_, .bvarLocal (by simp) (by rw [difference]; omega) (by rw [difference]; omega)⟩
        simpa [Expr.lowerBVars, Nat.sub_add_cancel shiftBound, above, difference] using resultRep
      | .Srt (ld12 := loaded) (he67 := result) (hm66 := heap) .. =>
        obtain ⟨u, rfl, rfl, level⟩ := rep.raw_sort_view loaded
        subst result heap
        exact ⟨_, .sort (by simp) (level.mono (Heap.Extends.snoc _ _))⟩
      | .Const (ld12 := loaded) (he101 := result) (hm100 := heap) .. =>
        have semantic := rep.toTmExact.toTm
        obtain ⟨a, levels, rfl, rfl, address, levelsRep⟩ := rep.raw_const_view loaded
        have : Resolved (κ (ixAddr a)) := ⟨semantic.const_key_ne⟩
        subst result heap
        exact ⟨_, .const (by simp)
          (Bytes.repAddressRef_heapMono₂ addrTy (Heap.Extends.snoc _ _) address)
          (levelsRep.mono (Heap.Extends.snoc _ _))⟩
      | .Lit (ld12 := loaded) (he549 := result) (hm548 := heap) .. =>
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
      | .App (cs158 := first) (cs194 := second) (ld12 := loaded) (he143 := result) (hm142 := heap)
          (ev160 := e1) (ev196 := e2) (hc221 := events) .. =>
        obtain ⟨RF, RA, EF, EA, rfl, rfl, func, arg⟩ := rep.raw_app_view loaded
        have short1 : first.length < fuel := by rw [events] at length; simp only [List.length_cons, List.length_append] at length; omega
        have short2 : second.length < fuel := by rw [events] at length; simp only [List.length_cons, List.length_append] at length; omega
        obtain ⟨F', hf⟩ := ih first.length short1 false (Nat.le_refl _)
          (bounded_sub (fun _ inside => by rw [events]; simp [inside]) bounded)
          shiftBound (by intro impossible; cases impossible) ⟨_, func⟩ e1
        obtain ⟨A', ha⟩ := ih second.length short2 false (Nat.le_refl _)
          (bounded_sub (fun _ inside => by rw [events]; simp [inside]) bounded)
          shiftBound (by intro impossible; cases impossible) ⟨_, arg.mono e1.heap_extends⟩ e2
        subst result heap
        exact ⟨_, .app (by simp) (hf.mono (e2.heap_extends.trans (Heap.Extends.snoc _ _)))
          (ha.mono (Heap.Extends.snoc _ _))⟩
      | .Lam (v253 := bodyOut) (cs264 := first) (cs300 := second) (ld12 := loaded) (he248 := result) (hm247 := heap)
          (ev266 := e1) (op333 := added) (ev302 := e2) (hc342 := events) .. =>
        obtain ⟨RD, RB, ED, EB, u, rfl, rfl, dom, body, level⟩ := rep.raw_lam_view loaded
        rw [SubstAux.add_ok added] at e2
        have short1 : first.length < fuel := by rw [events] at length; simp only [List.length_cons, List.length_append] at length; omega
        have short2 : second.length < fuel := by rw [events] at length; simp only [List.length_cons, List.length_append] at length; omega
        obtain ⟨D', hd⟩ := ih first.length short1 false (Nat.le_refl _)
          (bounded_sub (fun _ inside => by rw [events]; simp [inside]) bounded)
          shiftBound (by intro impossible; cases impossible) ⟨_, dom⟩ e1
        obtain ⟨B', hb⟩ := ih second.length short2 false (Nat.le_refl _)
          (bounded_sub (fun _ inside => by rw [events]; simp [inside]) bounded)
          (by rw [SubstAux.val_succ32 cutoffSmall]; omega) (by intro impossible; cases impossible) ⟨_, body.mono e1.heap_extends⟩ e2
        rw [SubstAux.val_succ32 cutoffSmall] at hb
        have cut : cutoff.val + 1 - shift.val = cutoff.val - shift.val + 1 := by omega
        rw [cut] at hb
        subst result heap
        refine ⟨.lam D' B' (bmeta u), .lam (bp := bodyOut) (by simp) (hd.mono (e2.heap_extends.trans (Heap.Extends.snoc _ _))) ?_
          (level.mono (e1.heap_extends.trans (e2.heap_extends.trans (Heap.Extends.snoc _ _))))⟩
        simpa only [Nat.add_right_comm] using hb.mono (Heap.Extends.snoc _ _)
      | .Forall (v374 := bodyOut) (cs385 := first) (cs421 := second) (ld12 := loaded) (he369 := result) (hm368 := heap)
          (ev387 := e1) (op454 := added) (ev423 := e2) (hc463 := events) .. =>
        obtain ⟨RD, RB, ED, EB, u, rfl, rfl, dom, body, level⟩ := rep.raw_forallE_view loaded
        rw [SubstAux.add_ok added] at e2
        have short1 : first.length < fuel := by rw [events] at length; simp only [List.length_cons, List.length_append] at length; omega
        have short2 : second.length < fuel := by rw [events] at length; simp only [List.length_cons, List.length_append] at length; omega
        obtain ⟨D', hd⟩ := ih first.length short1 false (Nat.le_refl _)
          (bounded_sub (fun _ inside => by rw [events]; simp [inside]) bounded)
          shiftBound (by intro impossible; cases impossible) ⟨_, dom⟩ e1
        obtain ⟨B', hb⟩ := ih second.length short2 false (Nat.le_refl _)
          (bounded_sub (fun _ inside => by rw [events]; simp [inside]) bounded)
          (by rw [SubstAux.val_succ32 cutoffSmall]; omega) (by intro impossible; cases impossible) ⟨_, body.mono e1.heap_extends⟩ e2
        rw [SubstAux.val_succ32 cutoffSmall] at hb
        have cut : cutoff.val + 1 - shift.val = cutoff.val - shift.val + 1 := by omega
        rw [cut] at hb
        subst result heap
        refine ⟨.forallE D' B' (bmeta u), .forallE (bp := bodyOut) (by simp) (hd.mono (e2.heap_extends.trans (Heap.Extends.snoc _ _))) ?_
          (level.mono (e1.heap_extends.trans (e2.heap_extends.trans (Heap.Extends.snoc _ _))))⟩
        simpa only [Nat.add_right_comm] using hb.mono (Heap.Extends.snoc _ _)
      | .Let (ld12 := loaded) (ev491 := helper) (hc532 := events) .. =>
        obtain ⟨RT, RV, RB, ET, EV, EB, rfl, rfl, type, value, body⟩ := rep.raw_let_view loaded
        match Obs.«KernelSubst::expr_lower_let».obs helper with
        | .run (v11 := bodyOut) (cs21 := first) (cs57 := second) (cs93 := third) (he5 := result) (hm4 := heap)
            (ev23 := e1) (ev59 := e2) (op126 := added) (ev95 := e3) (hc128 := nested) .. =>
          rw [SubstAux.add_ok added] at e3
          have short1 : first.length < fuel := by rw [events, nested] at length; simp only [List.length_cons, List.length_append] at length; omega
          have short2 : second.length < fuel := by rw [events, nested] at length; simp only [List.length_cons, List.length_append] at length; omega
          have short3 : third.length < fuel := by rw [events, nested] at length; simp only [List.length_cons, List.length_append] at length; omega
          obtain ⟨T', ht⟩ := ih first.length short1 false (Nat.le_refl _)
            (bounded_sub (fun _ inside => by rw [events, nested]; simp [inside]) bounded)
            shiftBound (by intro impossible; cases impossible) ⟨_, type⟩ e1
          obtain ⟨V', hv⟩ := ih second.length short2 false (Nat.le_refl _)
            (bounded_sub (fun _ inside => by rw [events, nested]; simp [inside]) bounded)
            shiftBound (by intro impossible; cases impossible) ⟨_, value.mono e1.heap_extends⟩ e2
          obtain ⟨B', hb⟩ := ih third.length short3 false (Nat.le_refl _)
            (bounded_sub (fun _ inside => by rw [events, nested]; simp [inside]) bounded)
            (by rw [SubstAux.val_succ32 cutoffSmall]; omega) (by intro impossible; cases impossible)
            ⟨_, body.mono (e1.heap_extends.trans e2.heap_extends)⟩ e3
          rw [SubstAux.val_succ32 cutoffSmall] at hb
          have cut : cutoff.val + 1 - shift.val = cutoff.val - shift.val + 1 := by omega
          rw [cut] at hb
          subst result heap
          refine ⟨instShift V' 0 B', .letE (bp := bodyOut) (by simp)
            (ht.mono (e2.heap_extends.trans (e3.heap_extends.trans (Heap.Extends.snoc _ _))))
            (hv.mono (e3.heap_extends.trans (Heap.Extends.snoc _ _))) ?_⟩
          simpa only [Nat.add_right_comm] using hb.mono (Heap.Extends.snoc _ _)
      | .Proj (cs618 := children) (ld12 := loaded) (he588 := result) (hm587 := heap)
          (ev620 := child) (hc645 := events) .. =>
        have semantic := rep.toTmExact.toTm
        obtain ⟨a, index, RI, EI, rfl, rfl, rfl, address, inner⟩ := rep.raw_proj_view loaded
        have : Resolved (κ (ixAddr a)) := ⟨semantic.proj_key_ne⟩
        have : ProjPermitted κ (ixAddr a) := semantic.proj_permitted loaded address
        have shorter : children.length < fuel := by rw [events] at length; simp only [List.length_cons] at length; omega
        obtain ⟨I', hi⟩ := ih children.length shorter false (Nat.le_refl _)
          (bounded_sub (fun _ inside => by rw [events]; simp [inside]) bounded)
          shiftBound (by intro impossible; cases impossible) ⟨_, inner⟩ child
        subst result heap
        exact ⟨_, .proj (by simp)
          (Bytes.repAddressRef_heapMono₂ addrTy (child.heap_extends.trans (Heap.Extends.snoc _ _)) address)
          (hi.mono (Heap.Extends.snoc _ _))⟩

/-- Actual lowering preserves the retained raw syntax. The shift lies below the cutoff,
so every subtraction selected by the actual loose-bound scan avoids field wraparound. -/
theorem RawExprRep.lower {κ : _root_.Address → KKey} {h h' : Heap F} {k : Nat}
    {R : KExpr} {p r : SourceValue F} {shift cutoff : F} {calls : List (Call F)}
    (represented : RawExprRep κ h k R p) (bounded : IxVM.Consistency.Bounded calls)
    (shiftBound : shift.val ≤ cutoff.val)
    (observed : ObsFn W "KernelSubst::expr_lower" [p, .field shift, .field cutoff] h r h' calls) :
    RawExprRep κ h' k (R.lowerBVars shift.val (cutoff.val - shift.val)) r :=
  raw_lower_go κ calls.length false (Nat.le_refl _) bounded shiftBound
    (by intro impossible; cases impossible) represented observed


end IxVM.Refinement.Decl
