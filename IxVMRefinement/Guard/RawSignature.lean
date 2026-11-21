import IxVMRefinement.Guard.RawInfer
import IxVMRefinement.Guard.Fields

/-! # Actual classifier signatures and checked field witnesses

Every successful sort_signature has a raw inference/head trace of its exact signature. Every
checked field therefore retains a real raw trace agreeing with its ordinarily inferred sort's
zero-set. Comparison still requires canonical agreement of the traces' actual load origins.
-/

namespace IxVM.Refinement.Decl

open IxVM.Refinement.Core

/-- A signature produced by raw structural inference, head normalization and zero-signature
encoding, in exactly that order. -/
def RawSignatureTrace (types delta : KKey → List KLevel → KExpr → Prop)
    (context : List KExpr) (input : KExpr) (signature : KLevel) : Prop :=
  ∃ type level, RawInferTrace types delta context input type ∧ RawHeadTrace delta type (.sort level) ∧
    signature = Ix.Kernel.Level.guardSignatureLevel level

theorem RawSignatureTrace.unique {types delta otherTypes otherDelta : KKey → List KLevel → KExpr → Prop}
    (typeAnswers : ∀ key parameters first second,
      types key parameters first → otherTypes key parameters second → first = second)
    (deltaAnswers : ∀ key parameters first second,
      delta key parameters first → otherDelta key parameters second → first = second)
    {context : List KExpr} {input : KExpr} {first second : KLevel}
    (left : RawSignatureTrace types delta context input first)
    (right : RawSignatureTrace otherTypes otherDelta context input second) : first = second := by
  obtain ⟨type, level, inferred, headed, rfl⟩ := left
  obtain ⟨otherType, otherLevel, inferred', headed', rfl⟩ := right
  have sameType := inferred.unique typeAnswers deltaAnswers inferred'
  subst sameType
  have sameLevel := Ix.Kernel.Expr.sort.inj (headed.unique deltaAnswers headed')
  rw [sameLevel]

end IxVM.Refinement.Decl

namespace IxVM.Refinement.Core.GuardData

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open IxVM.Refinement.Decl (RawExprRep RawContext RawTypeAt RawDeltaAt RawSignatureTrace)
open IxVM.Refinement.KernelLevels (RepKLevel)

/-- Actual sort classification produces a trace of its exact represented signature, from the
facts stated before the registry. -/
theorem sort_signature_raw_trace_base (rawKey : _root_.Address → KKey) [∀ a, Resolved (rawKey a)]
    {c : ScopedCtx} (facts : ScopedCoreBase c) {rootCalls : List (Call F)}
    {d k : Nat} {Γ : Nat → KExpr} {R E : KExpr} {context : List KExpr}
    {p ctx r : SourceValue F} {h h' : Heap F} {calls : List (Call F)}
    (good : CoreGood c calls) (subset : ∀ call ∈ calls, call ∈ rootCalls)
    (types : c.types Γ h d ctx) (scopedRep : Tm c.κ d Γ h 0 E p)
    (rawCtx : RawContext rawKey h context ctx) (physical : RawExprRep rawKey h k R p)
    (observed : ObsFn W "KernelGuard::sort_signature" [p, ctx] h r h' calls) :
    ∃ signature, RepKLevel h' signature r ∧
      RawSignatureTrace (RawTypeAt c rawKey rootCalls) (RawDeltaAt c rawKey rootCalls) context R signature := by
  obtain ⟨typePtr, firstHeap, first, headHeap, headPtr, heads, levelPtr, encoding,
    infer, norm, loaded, encode, events⟩ := Obs.«KernelGuard::sort_signature».obs observed
  have firstInside : ∀ call ∈ first, call ∈ calls := by intro call member; rw [events]; simp [member]
  have headInside : ∀ call ∈ heads, call ∈ calls := by intro call member; rw [events]; simp [member]
  obtain ⟨typeBound, typeRaw, typeRep, inferred⟩ := infer_raw_trace_base rawKey facts
    (good.sub firstInside) (fun call member => subset call (firstInside call member))
    types scopedRep rawCtx physical infer
  obtain ⟨type, typeScoped⟩ := infer_shape_rep_base facts (good.sub firstInside) types scopedRep infer
  obtain ⟨headBound, result, resultRep, headed⟩ := head_raw_trace_base rawKey facts
    (good.sub headInside) (fun call member => subset call (headInside call member)) typeScoped typeRep norm
  obtain ⟨image, raw⟩ := resultRep
  obtain ⟨u, rfl, rfl, represented⟩ := raw.raw_sort_view loaded
  exact ⟨Ix.Kernel.Level.guardSignatureLevel u,
    IxVM.Refinement.Guard.signature_level_spec represented encode,
    typeRaw, u, inferred, headed, rfl⟩

/-- Actual sort classification produces a trace of its exact represented signature. -/
theorem sort_signature_raw_trace (rawKey : _root_.Address → KKey) [∀ a, Resolved (rawKey a)]
    {c : ScopedCtx} (facts : ScopedCoreFacts c) {rootCalls : List (Call F)}
    {d k : Nat} {Γ : Nat → KExpr} {R E : KExpr} {context : List KExpr}
    {p ctx r : SourceValue F} {h h' : Heap F} {calls : List (Call F)}
    (good : CoreGood c calls) (subset : ∀ call ∈ calls, call ∈ rootCalls)
    (types : c.types Γ h d ctx) (scopedRep : Tm c.κ d Γ h 0 E p)
    (rawCtx : RawContext rawKey h context ctx) (physical : RawExprRep rawKey h k R p)
    (observed : ObsFn W "KernelGuard::sort_signature" [p, ctx] h r h' calls) :
    ∃ signature, RepKLevel h' signature r ∧
      RawSignatureTrace (RawTypeAt c rawKey rootCalls) (RawDeltaAt c rawKey rootCalls) context R signature :=
  sort_signature_raw_trace_base rawKey facts.base good subset types scopedRep rawCtx physical observed

/-- An actual checked field chooses raw input/context data and produces a classifier trace
whose signature has exactly the inferred sort's zero-set. All raw premises have producers here. -/
theorem CheckedSortAt.raw_trace (rawKey : _root_.Address → KKey) [∀ a, Resolved (rawKey a)]
    {c : ScopedCtx} (facts : ScopedCoreFacts c) {start : Heap F} {calls : List (Call F)}
    {depth : Nat} {domain : KExpr} {sort : KLevel}
    (good : CoreGood c calls) (checked : CheckedSortAt c start calls depth domain sort) :
    ∃ (context : List KExpr) (input : KExpr) (signature : KLevel)
      (before : Heap F) (p ctx : SourceValue F),
      Heap.Extends start before ∧ RawContext rawKey before context ctx ∧
      RawExprRep rawKey before depth input p ∧
      RawSignatureTrace (RawTypeAt c rawKey calls) (RawDeltaAt c rawKey calls) context input signature ∧
      ∀ φ, Ix.Kernel.Level.eval φ sort = 0 ↔ Ix.Kernel.Level.eval φ signature = 0 := by
  obtain ⟨type, signature, Γ, p, ctx, predicted, before, after, inner,
    _, _, extension, types, represented, observed, level, included, zero⟩ := checked
  obtain ⟨context, rawCtx⟩ := RawContext.ofTypes rawKey types.1
  obtain ⟨input, physical⟩ := RawExprRep.ofOpenTm_keyed rawKey represented
  rw [Nat.zero_add] at physical
  obtain ⟨rawSignature, rawLevel, trace⟩ := sort_signature_raw_trace rawKey facts
    (good.sub included) included types represented rawCtx physical observed
  have same := level.det rawLevel
  subst same
  exact ⟨context, input, signature, before, p, ctx, extension, rawCtx, physical, trace, zero⟩

end IxVM.Refinement.Core.GuardData
