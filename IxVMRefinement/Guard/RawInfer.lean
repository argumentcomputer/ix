import IxVMRefinement.Guard.RawContext

/-! # Actual structural classifier traces with physical declaration origins

The classifier predicts raw type data. Its traces retain actual declared-type and definition
loads, and do not assert a Rules.Infer judgement for that prediction. Cross-run agreement is a
separate consequence of agreement of those actual raw roots.
-/

namespace IxVM.Refinement.Decl

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library
open IxVM.Refinement.Core
open Ix.Kernel (Expr ConstantInfo BinderMeta)

/-- One declared-type answer retains its actual load and physical type root. -/
def RawTypeAt (c : ScopedCtx) (κ : _root_.Address → KKey) (rootCalls : List (Call F))
    (key : KKey) (parameters : List KLevel) (output : KExpr) : Prop :=
  ∃ (address : Bytes.Address) (ci : ConstantInfo .anon) (raw : KExpr)
    (ap ptr value typePtr : SourceValue F) (before loaded beforeType beforeInst : Heap F)
    (loadCalls typeCalls : List (Call F)),
    key = κ (ixAddr address) ∧ c.env.find? (c.κ (ixAddr address)) = some ci ∧
    parameters.length = ci.toConstantVal.levelParams.length ∧
    Bytes.RepAddressRef addrTy before address ap ∧
    ObsFn W "Ingress::get_ci" [ap] before ptr loaded loadCalls ∧
    (⟨"Ingress::get_ci", [ap], before⟩ : Call F) ∈ rootCalls ∧
    loadValue loaded ptr = .ok value ∧
    ObsFn W "KernelInfer::const_type_of" [value] beforeType typePtr beforeInst typeCalls ∧
    Heap.Extends loaded beforeInst ∧ RawExprRep κ beforeInst 0 raw typePtr ∧
    (∀ call ∈ loadCalls, call ∈ rootCalls) ∧ (∀ call ∈ typeCalls, call ∈ rootCalls) ∧
    output = raw.instantiateLevelParams (List.range parameters.length) parameters

/-- The successful data strategy implemented by infer_shape, independently of its fuel. -/
inductive RawInferTrace (types delta : KKey → List KLevel → KExpr → Prop) :
    List KExpr → KExpr → KExpr → Prop where
  | bvar {context : List KExpr} {index : Nat} {type : KExpr} :
      context[index]? = some type →
      RawInferTrace types delta context (.bvar index) (type.liftLooseBVars (index + 1) 0)
  | sort (context : List KExpr) (level : KLevel) :
      RawInferTrace types delta context (.sort level) (.sort (.succ level))
  | const {context : List KExpr} {key : KKey} {parameters : List KLevel} {type : KExpr} :
      types key parameters type → RawInferTrace types delta context (.const key parameters) type
  | app {context : List KExpr} {func arg type dom body : KExpr} {metadata : BinderMeta} :
      RawInferTrace types delta context func type →
      RawHeadTrace delta type (.forallE dom body metadata) →
      RawInferTrace types delta context (.app func arg) (body.instantiate1Lift arg)
  | forallE {context : List KExpr} {dom body type : KExpr} {metadata : BinderMeta} {level : KLevel} :
      RawInferTrace types delta (dom :: context) body type → RawHeadTrace delta type (.sort level) →
      RawInferTrace types delta context (.forallE dom body metadata) (.sort level)
  | lam {context : List KExpr} {dom body type : KExpr} {metadata : BinderMeta} :
      RawInferTrace types delta (dom :: context) body type →
      RawInferTrace types delta context (.lam dom body metadata) (.forallE dom type metadata)
  | letE {context : List KExpr} {ty value body type : KExpr} {metadata : Ix.Kernel.LetMeta} :
      RawInferTrace types delta context (body.instantiate1Lift value) type →
      RawInferTrace types delta context (.letE ty value body metadata) type

/-- The data strategy is functional once actual declared-type and delta answers agree. -/
theorem RawInferTrace.unique {types delta otherTypes otherDelta : KKey → List KLevel → KExpr → Prop}
    (typeAnswers : ∀ key parameters first second,
      types key parameters first → otherTypes key parameters second → first = second)
    (deltaAnswers : ∀ key parameters first second,
      delta key parameters first → otherDelta key parameters second → first = second)
    {context : List KExpr} {input first second : KExpr}
    (left : RawInferTrace types delta context input first)
    (right : RawInferTrace otherTypes otherDelta context input second) : first = second := by
  induction left generalizing second with
  | bvar selected =>
    cases right with
    | bvar selected' =>
      have same := Option.some.inj (selected.symm.trans selected')
      subst same
      rfl
  | sort context level => cases right; rfl
  | const loaded => cases right with | const loaded' => exact typeAnswers _ _ _ _ loaded loaded'
  | app inferred headed ih =>
    cases right with
    | app inferred' headed' =>
      have same := ih inferred'
      subst same
      obtain ⟨rfl, rfl, rfl⟩ := Expr.forallE.inj (headed.unique deltaAnswers headed')
      rfl
  | forallE inferred headed ih =>
    cases right with
    | forallE inferred' headed' =>
      have same := ih inferred'
      subst same
      exact headed.unique deltaAnswers headed'
  | lam inferred ih =>
    cases right with
    | lam inferred' => rw [ih inferred']
  | letE inferred ih => cases right with | letE inferred' => exact ih inferred'

end IxVM.Refinement.Decl

namespace IxVM.Refinement.Core.GuardData

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open IxVM.Refinement.Decl (RawExprRep RawContext RawAny RawTypeAt RawDeltaAt RawInferTrace RawHeadTrace)
open IxVM.Refinement.KernelLevels (RepKLevel)

set_option maxHeartbeats 2400000

private theorem infer_raw_go (rawKey : _root_.Address → KKey) [∀ a, Resolved (rawKey a)]
    {c : ScopedCtx} (facts : ScopedCoreFacts c) (rootCalls : List (Call F)) :
    ∀ fuel : Nat, ∀ {d k : Nat} {Γ : Nat → KExpr} {R E : KExpr} {context : List KExpr}
      {p ctx budget r : SourceValue F} {h h' : Heap F} {calls : List (Call F)},
      calls.length ≤ fuel → CoreGood c calls → (∀ call ∈ calls, call ∈ rootCalls) →
      c.types Γ h d ctx → Tm c.κ d Γ h 0 E p → RawContext rawKey h context ctx →
      RawExprRep rawKey h k R p →
      ObsFn W "KernelGuard::infer_shape" [p, ctx, budget] h r h' calls →
      ∃ bound result, RawExprRep rawKey h' bound result r ∧
        RawInferTrace (RawTypeAt c rawKey rootCalls) (RawDeltaAt c rawKey rootCalls) context R result := by
  intro fuel
  induction fuel using Nat.strong_induction_on with
  | h fuel ih =>
    intro d k Γ R E context p ctx budget r h h' calls length good subset types scoped rawCtx physical observed
    obtain ⟨image, raw⟩ := physical
    match Obs.«KernelGuard::infer_shape».obs observed with
    | .n0 (heq40 := impossible) .. | .other_other (heq732 := impossible) .. =>
      exact (zero_ne_one (Value.field.inj impossible)).elim
    | .other_BVar (cs76 := children) (ld60 := loaded) (ev78 := lookup) (hc95 := events) .. =>
      obtain ⟨index, rfl, rfl, _, _⟩ := raw.raw_bvar_view loaded
      obtain ⟨entry, selected, bound, represented⟩ := rawCtx.lookup
        (bounded_sub (fun _ inside => by rw [events]; simp [inside]) good.2) lookup
      exact ⟨bound, _, represented, .bvar selected⟩
    | .other_Srt (x_u := lp) (ld60 := loaded) (he112 := result) (hm111 := heap) (hm126 := allocated) .. =>
      obtain ⟨level, rfl, rfl, represented⟩ := raw.raw_sort_view loaded
      subst result heap allocated
      have extension := Heap.Extends.snoc h (.construct klevelEnum "Succ" [lp])
      have successor : RepKLevel (h ++ [.construct klevelEnum "Succ" [lp]]) (.succ level)
          (.ptr (.enum klevelEnum) h.length) := .succ List.getElem?_concat_length (represented.mono extension)
      exact ⟨0, .sort (.succ level), ⟨_, .sort List.getElem?_concat_length
        (successor.mono (Heap.Extends.snoc _ _))⟩, .sort context level⟩
    | .other_Const (cs159 := children) (ld60 := loaded) (ev161 := declared) (hc178 := events) .. =>
      obtain ⟨address, parameters, rfl, rfl, addressRep, paramsRep⟩ := raw.raw_const_view loaded
      obtain ⟨scopedAddress, _, rfl, scopedAddressRep, _, _, _⟩ := scoped.const_of_load loaded
      have same := addr_det addressRep scopedAddressRep
      subst scopedAddress
      have inside : ∀ call ∈ children, call ∈ calls := by intro call member; rw [events]; simp [member]
      obtain ⟨ci, origin, ptr, value, typePtr, loadedHeap, beforeType, beforeInst, loadCalls,
        typeCalls, instCalls, found, arity, load, member, node, getType, originRep, extension,
        inst, loadSubset, typeSubset, _, resultRep⟩ := declared_type_keyed_raw_origin rawKey facts
          (good.sub inside) addressRep scoped.const_key_ne paramsRep declared
      have typeOrigin : RawTypeAt c rawKey rootCalls (rawKey (ixAddr address)) parameters
          (origin.instantiateLevelParams (List.range parameters.length) parameters) := by
        exact ⟨address, ci, origin, _, ptr, value, typePtr, h, loadedHeap, beforeType, beforeInst,
          loadCalls, typeCalls, rfl, found, arity, addressRep, load, subset _ (inside _ member),
          node, getType, extension, originRep,
          fun call member => subset call (inside call (loadSubset call member)),
          fun call member => subset call (inside call (typeSubset call member)), rfl⟩
      exact ⟨0, _, resultRep, .const typeOrigin⟩
    | .other_App (cs207 := first) (cs256 := heads) (cs306 := instCalls) (ld60 := loaded)
        (ev209 := child) (ev258 := norm) (ld252 := forallNode) (ev308 := inst) (hc332 := events) .. =>
      obtain ⟨RF, RA, EF, EA, rfl, rfl, rawFunc, rawArg⟩ := raw.raw_app_view loaded
      obtain ⟨func, arg, rfl, scopedFunc, scopedArg⟩ := scoped.app_of_load loaded
      have firstInside : ∀ call ∈ first, call ∈ calls := by intro call member; rw [events]; simp [member]
      have headInside : ∀ call ∈ heads, call ∈ calls := by intro call member; rw [events]; simp [member]
      have instInside : ∀ call ∈ instCalls, call ∈ calls := by intro call member; rw [events]; simp [member]
      have shorter : first.length < fuel := by
        rw [events] at length; simp only [List.length_cons, List.length_append] at length; omega
      obtain ⟨typeBound, typeRaw, typeRep, inferred⟩ := ih first.length shorter (Nat.le_refl _)
        (good.sub firstInside) (fun call member => subset call (firstInside call member))
        types scopedFunc rawCtx ⟨_, rawFunc⟩ child
      obtain ⟨type, typeScoped⟩ := infer_shape_rep facts (good.sub firstInside) types scopedFunc child
      obtain ⟨headBound, headed, headRep, headedTrace⟩ := head_raw_trace rawKey facts
        (good.sub headInside) (fun call member => subset call (headInside call member)) typeScoped typeRep norm
      let common := max k headBound
      obtain ⟨headImage, headExact⟩ := headRep.weaken (show headBound ≤ common from Nat.le_max_right _ _)
      obtain ⟨RD, RB, ED, EB, level, rfl, rfl, _, rawBody, _⟩ := headExact.raw_forallE_view forallNode
      have argument : RawExprRep rawKey _ common RA _ :=
        (show RawExprRep rawKey h k RA _ from ⟨_, rawArg⟩).mono
          (child.heap_extends.trans norm.heap_extends) |>.weaken (Nat.le_max_left _ _)
      have output := RawExprRep.inst1
        (by simpa only [ZMod.val_zero, Nat.add_zero] using
          (show RawExprRep rawKey _ (common + 1) RB _ from ⟨_, rawBody⟩))
        argument (bounded_sub instInside good.2) inst
      simp only [ZMod.val_zero, Nat.add_zero] at output
      exact ⟨common + 1, _, output, .app inferred headedTrace⟩
    | .other_Forall (x_ty := ty) (cs367 := first) (cs438 := heads) (ld60 := loaded)
        (hm389 := allocated) (ev369 := child) (ev440 := norm) (ld434 := sortNode)
        (he477 := result) (hm476 := heap) (hc489 := events) .. =>
      obtain ⟨RD, RB, ED, EB, metadata, rfl, rfl, rawDom, rawBody, _⟩ := raw.raw_forallE_view loaded
      obtain ⟨D, B, level, rfl, scopedDom, scopedBody, _⟩ := scoped.forallE_of_load loaded
      subst allocated result heap
      have extension := Heap.Extends.snoc h (.construct kexprListEnum "Cons" [ty, ctx])
      have newTypes := ProjAux.types_extend types scopedDom
      have newBody := Tm.open_body (Ghost.extend_at Γ d D) (Ghost.extend_below Γ d D) (scopedBody.mono extension)
      have newContext : RawContext rawKey _ (RD :: context) (.ptr (.enum kexprListEnum) h.length) :=
        .cons List.getElem?_concat_length ⟨k, ⟨_, rawDom.mono extension⟩⟩ (rawCtx.mono extension)
      have firstInside : ∀ call ∈ first, call ∈ calls := by intro call member; rw [events]; simp [member]
      have headInside : ∀ call ∈ heads, call ∈ calls := by intro call member; rw [events]; simp [member]
      have shorter : first.length < fuel := by
        rw [events] at length; simp only [List.length_cons, List.length_append] at length; omega
      obtain ⟨typeBound, typeRaw, typeRep, inferred⟩ := ih first.length shorter (Nat.le_refl _)
        (good.sub firstInside) (fun call member => subset call (firstInside call member))
        newTypes newBody newContext ⟨_, rawBody.mono extension⟩ child
      obtain ⟨type, typeScoped⟩ := infer_shape_rep facts (good.sub firstInside) newTypes newBody child
      obtain ⟨headBound, headed, headRep, headedTrace⟩ := head_raw_trace rawKey facts
        (good.sub headInside) (fun call member => subset call (headInside call member)) typeScoped typeRep norm
      obtain ⟨headImage, headExact⟩ := headRep
      obtain ⟨u, rfl, rfl, levelRep⟩ := headExact.raw_sort_view sortNode
      exact ⟨0, .sort u, ⟨_, .sort List.getElem?_concat_length (levelRep.mono (Heap.Extends.snoc _ _))⟩,
        .forallE inferred headedTrace⟩
    | .other_Lam (x_ty := ty) (x_m := data) (v512 := out) (m513 := mout) (cs523 := first)
        (ld60 := loaded) (hm545 := allocated) (ev525 := child) (he584 := result)
        (hm583 := heap) (hc612 := events) .. =>
      obtain ⟨RD, RB, ED, EB, level, rfl, rfl, rawDom, rawBody, rawLevel⟩ := raw.raw_lam_view loaded
      obtain ⟨D, B, metadata, rfl, scopedDom, scopedBody, _⟩ := scoped.lam_of_load loaded
      subst allocated result heap
      have extension := Heap.Extends.snoc h (.construct kexprListEnum "Cons" [ty, ctx])
      have newTypes := ProjAux.types_extend types scopedDom
      have newBody := Tm.open_body (Ghost.extend_at Γ d D) (Ghost.extend_below Γ d D) (scopedBody.mono extension)
      have newContext : RawContext rawKey _ (RD :: context) (.ptr (.enum kexprListEnum) h.length) :=
        .cons List.getElem?_concat_length ⟨k, ⟨_, rawDom.mono extension⟩⟩ (rawCtx.mono extension)
      have inside : ∀ call ∈ first, call ∈ calls := by intro call member; rw [events]; simp [member]
      have shorter : first.length < fuel := by
        rw [events] at length; simp only [List.length_cons] at length; omega
      obtain ⟨typeBound, typeRaw, typeRep, inferred⟩ := ih first.length shorter (Nat.le_refl _)
        (good.sub inside) (fun call member => subset call (inside call member))
        newTypes newBody newContext ⟨_, rawBody.mono extension⟩ child
      let common := max k typeBound
      have finalExtension := Heap.Extends.snoc mout (.construct kexprEnum "Forall" [ty, out, data])
      have allExtension := extension.trans (child.heap_extends.trans finalExtension)
      obtain ⟨domImage, domExact⟩ :=
        (show RawExprRep rawKey h k RD ty from ⟨_, rawDom⟩).mono allExtension |>.weaken (Nat.le_max_left _ _)
      obtain ⟨bodyImage, bodyExact⟩ := (typeRep.mono finalExtension).weaken
        (show typeBound ≤ common + 1 by dsimp [common]; omega)
      exact ⟨common, .forallE RD typeRaw (bmeta level),
        ⟨_, .forallE List.getElem?_concat_length domExact bodyExact (rawLevel.mono allExtension)⟩,
        .lam inferred⟩
    | .other_Let (cs639 := children) (cs654 := instCalls) (ld60 := loaded)
        (ev656 := inst) (ev641 := child) (hc702 := events) .. =>
      obtain ⟨RT, RV, RB, ET, EV, EB, rfl, rfl, _, rawValue, rawBody⟩ := raw.raw_let_view loaded
      obtain ⟨D, V, B, rfl, _, scopedValue, scopedBody⟩ := scoped.letE_of_load loaded
      have instInside : ∀ call ∈ instCalls, call ∈ calls := by intro call member; rw [events]; simp [member]
      have childInside : ∀ call ∈ children, call ∈ calls := by intro call member; rw [events]; simp [member]
      have shorter : children.length < fuel := by
        rw [events] at length; simp only [List.length_cons, List.length_append] at length; omega
      have rawBeta := RawExprRep.inst1
        (by simpa only [ZMod.val_zero, Nat.add_zero] using
          (show RawExprRep rawKey h (k + 1) RB _ from ⟨_, rawBody⟩))
        (show RawExprRep rawKey h k RV _ from ⟨_, rawValue⟩) (bounded_sub instInside good.2) inst
      simp only [ZMod.val_zero, Nat.add_zero] at rawBeta
      have scopedBeta := SubstAux.gall c.κ .expr_inst1 _ _ _ _ _ inst _ _ (0 : F) rfl
        (bounded_sub instInside good.2) d Γ B V
        (by simpa only [ZMod.val_zero, Nat.zero_add] using scopedBody) scopedValue
      simp only [ZMod.val_zero] at scopedBeta
      obtain ⟨bound, result, resultRep, inferred⟩ := ih children.length shorter (Nat.le_refl _)
        (good.sub childInside) (fun call member => subset call (childInside call member))
        (types_mono inst.heap_extends types) scopedBeta (rawCtx.mono inst.heap_extends) rawBeta child
      exact ⟨bound, result, resultRep, .letE inferred⟩

/-- Actual structural classification produces an exact raw trace of its prediction, with all
constant answers tied to actual load origins. -/
theorem infer_raw_trace (rawKey : _root_.Address → KKey) [∀ a, Resolved (rawKey a)]
    {c : ScopedCtx} (facts : ScopedCoreFacts c) {rootCalls : List (Call F)}
    {d k : Nat} {Γ : Nat → KExpr} {R E : KExpr} {context : List KExpr}
    {p ctx budget r : SourceValue F} {h h' : Heap F} {calls : List (Call F)}
    (good : CoreGood c calls) (subset : ∀ call ∈ calls, call ∈ rootCalls)
    (types : c.types Γ h d ctx) (scoped : Tm c.κ d Γ h 0 E p)
    (rawCtx : RawContext rawKey h context ctx) (physical : RawExprRep rawKey h k R p)
    (observed : ObsFn W "KernelGuard::infer_shape" [p, ctx, budget] h r h' calls) :
    ∃ bound result, RawExprRep rawKey h' bound result r ∧
      RawInferTrace (RawTypeAt c rawKey rootCalls) (RawDeltaAt c rawKey rootCalls) context R result :=
  infer_raw_go rawKey facts rootCalls calls.length (Nat.le_refl _) good subset types scoped rawCtx physical observed

end IxVM.Refinement.Core.GuardData
