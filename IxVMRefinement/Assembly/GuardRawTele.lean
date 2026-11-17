import IxVMRefinement.Assembly.GuardRawHead
import IxVMRefinement.Core.PrefixEq
import IxVMRefinement.Decl.NativeFront

/-! # Actual raw telescope builders share one binder-prefix contract

The block builder inserts its supplied sort at the end; the recursor builder retains the
residual term. Their actual raw traces record only the consumed binders, so comparing them
does not require the residuals to be identical.
-/

namespace IxVM.Refinement.Decl

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library
open IxVM.Refinement.Core
open IxVM.Refinement.KernelLevels (RepKLevel)
open Ix.Kernel (Expr BinderMeta)

set_option maxHeartbeats 2400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-- A raw telescope consumes deterministic heads and retains their domains and binder data. -/
inductive RawBinderTrace (delta : KKey → List KLevel → KExpr → Prop) :
    Nat → KExpr → KExpr → Prop
  | done (input result : KExpr) : RawBinderTrace delta 0 input result
  | step {n : Nat} {input dom body tail : KExpr} {binderData : BinderMeta} :
      RawHeadTrace delta input (.forallE dom body binderData) →
      RawBinderTrace delta n body tail →
      RawBinderTrace delta (n + 1) input (.forallE dom tail binderData)

/-- Actual sort extraction follows the same raw heads as the telescope builders. -/
inductive RawSortTrace (delta : KKey → List KLevel → KExpr → Prop) :
    Nat → KExpr → KLevel → Prop
  | done {input : KExpr} {level : KLevel} :
      RawHeadTrace delta input (.sort level) → RawSortTrace delta 0 input level
  | step {n : Nat} {input dom body : KExpr} {binderData : BinderMeta} {level : KLevel} :
      RawHeadTrace delta input (.forallE dom body binderData) →
      RawSortTrace delta n body level → RawSortTrace delta (n + 1) input level

theorem RawBinderTrace.prefix {delta other : KKey → List KLevel → KExpr → Prop}
    (answers : ∀ key parameters first second,
      delta key parameters first → other key parameters second → first = second)
    {n : Nat} {input first second : KExpr} (left : RawBinderTrace delta n input first)
    (right : RawBinderTrace other n input second) : PrefixEq n first second := by
  induction left generalizing second with
  | done => trivial
  | step head tail ih =>
    cases right with
    | step head' tail' =>
      obtain ⟨rfl, rfl, rfl⟩ := Expr.forallE.inj (head.unique answers head')
      exact ⟨rfl, rfl, ih tail'⟩

theorem RawSortTrace.unique {delta other : KKey → List KLevel → KExpr → Prop}
    (answers : ∀ key parameters first second,
      delta key parameters first → other key parameters second → first = second)
    {n : Nat} {input : KExpr} {first second : KLevel} (left : RawSortTrace delta n input first)
    (right : RawSortTrace other n input second) : first = second := by
  induction left generalizing second with
  | done head => cases right with | done head' => exact Expr.sort.inj (head.unique answers head')
  | step head tail ih =>
    cases right with
    | step head' tail' =>
      obtain ⟨rfl, rfl, rfl⟩ := Expr.forallE.inj (head.unique answers head')
      exact ih tail'

/-- Raw binder equality descends through deterministic let erasure to the existing semantic
PrefixEq interface used by native recursor generation. -/
theorem PrefixEq.rawMeaning : ∀ {n : Nat} {R S : KExpr}, PrefixEq n R S →
    PrefixEq n (rawMeaning R) (rawMeaning S)
  | 0, _, _, _ => trivial
  | n + 1, R, S, prefix => by
    cases R <;> cases S <;> simp only [PrefixEq] at prefix
    rename_i D B binderData D' B' binderData'
    obtain ⟨rfl, rfl, tail⟩ := prefix
    exact ⟨rfl, rfl, PrefixEq.rawMeaning tail⟩

theorem PrefixEq.of_raw_readings {κ κ' : _root_.Address → KKey} {d d' k k' n : Nat}
    {Γ Γ' : Nat → KExpr} {h h' : Heap F} {R S E E' : KExpr} {p p' : SourceValue F}
    (first : RawTmExact κ d Γ h k R E p) (second : RawTmExact κ' d' Γ' h' k' S E' p')
    (prefix : PrefixEq n R S) : PrefixEq n E E' := by
  rw [first.meaning, second.meaning]
  exact prefix.rawMeaning

private theorem store_raw_forall {κ : _root_.Address → KKey} {h : Heap F} {kd kb : Nat}
    {D B : KExpr} {dom body levelPtr : SourceValue F} {level : KLevel}
    (domain : RawExprRep κ h kd D dom) (tail : RawExprRep κ h kb B body)
    (datum : RepKLevel h level levelPtr) :
    ∃ bound, RawExprRep κ (h ++ [.construct kexprEnum "Forall" [dom, body, levelPtr]]) bound
      (.forallE D B (bmeta level)) (.ptr (.enum kexprEnum) h.length) := by
  obtain ⟨ED, hd⟩ := domain
  obtain ⟨EB, hb⟩ := tail
  refine ⟨max kd kb, .forallE ED EB (bmeta level), .forallE (by simp)
    ((hd.weaken_bound (Nat.le_max_left _ _)).mono (Heap.Extends.snoc _ _))
    ((hb.weaken_bound (by omega : kb ≤ max kd kb + 1)).mono (Heap.Extends.snoc _ _))
    (datum.mono (Heap.Extends.snoc _ _))⟩

/-- The block's actual builder produces the raw binder trace, including every alias head.
Its context-list and role-pointer inputs are passed through by the source; scoped term evidence
supplies exactly the load licensing needed by the structural head producer. -/
theorem former_tele_at_raw (rawKey : _root_.Address → KKey) [∀ a, Resolved (rawKey a)]
    {c : ScopedCtx} (facts : ScopedCoreFacts c) {rootCalls : List (Call F)} :
    ∀ n {d k : Nat} {Γ : Nat → KExpr} {R E : KExpr} {level : KLevel}
      {rc p types levelPtr r : SourceValue F} {h h' : Heap F} {calls : List (Call F)},
      n < 18446744069414584321 → CoreGood c calls → (∀ call ∈ calls, call ∈ rootCalls) →
      Tm c.κ d Γ h 0 E p → RawExprRep rawKey h k R p → RepKLevel h level levelPtr →
      ObsFn W "KernelCheck::former_tele_at" [rc, p, .field (n : F), types, levelPtr] h r h' calls →
      ∃ bound result, RawExprRep rawKey h' bound result r ∧
        RawBinderTrace (RawDeltaAt c rawKey rootCalls) n R result
  | 0, d, k, Γ, R, E, level, rc, p, types, levelPtr, r, h, h', calls,
      _, good, subset, scopedRep, physical, datum, observed => by
    match Obs.«KernelCheck::former_tele_at».obs observed with
    | .n0 (he19 := result) (hm18 := heap) .. =>
      subst result heap
      exact ⟨0, .sort level, ⟨_, .sort (by simp) (datum.mono (Heap.Extends.snoc _ _))⟩, .done _ _⟩
    | .other_Forall (hne32 := nonzero) .. | .other_other (hne32 := nonzero) .. =>
      exact (nonzero rfl).elim
  | n + 1, d, k, Γ, R, E, level, rc, p, types, levelPtr, r, h, h', calls,
      bound, good, subset, scopedRep, physical, datum, observed => by
    match Obs.«KernelCheck::former_tele_at».obs observed with
    | .n0 (hv14 := zero) .. => exact (succ_field_ne_zero_bounded bound zero).elim
    | .other_Forall (x_d := dom) (x_b := body) (x_m := metadata)
        (v79 := tailPtr) (m89 := after) (cs97 := children) (m135 := pushed)
        (ld47 := loaded) (he74 := result) (hm73 := heap) (op132 := subtracted)
        (hm143 := push) (ev99 := child) (hc177 := events) .. =>
      obtain ⟨semantic, raw⟩ := physical
      obtain ⟨RD, RB, ED, EB, u, rfl, rfl, rawDom, rawBody, rawLevel⟩ := raw.raw_forallE_view loaded
      obtain ⟨D, B, _, rfl, _, scopedBody, _⟩ := scopedRep.forallE_of_load loaded
      have extension : Heap.Extends h pushed := by rw [push]; exact Heap.Extends.snoc _ _
      have opened := (scopedBody.open_body (Ghost.extend_at Γ d D) (Ghost.extend_below Γ d D)).mono extension
      rw [evalBinOp_sub_succ n subtracted] at child
      have childInside : ∀ call ∈ children, call ∈ calls := by intro call member; rw [events]; simp [member]
      obtain ⟨tailBound, tailRaw, tailRep, tailTrace⟩ := former_tele_at_raw rawKey facts n (by omega)
        (good.sub childInside) (fun call member => subset call (childInside call member))
        opened ⟨_, rawBody.mono extension⟩ (datum.mono extension) child
      subst result heap
      have allExtended := extension.trans child.heap_extends
      obtain ⟨outBound, outRep⟩ := store_raw_forall
        (show RawExprRep rawKey after k RD dom from ⟨_, rawDom.mono allExtended⟩)
        tailRep (rawLevel.mono allExtended)
      exact ⟨outBound, _, outRep, .step (.forallE RD RB (bmeta u)) tailTrace⟩
    | .other_other (x_d := dom) (x_b := body) (x_m := metadata)
        (v241 := tailPtr) (m251 := after) (cs259 := children) (cs196 := heads)
        (m183 := headHeap) (p190 := headPtr) (m297 := pushed)
        (ev198 := headCall) (ld192 := loaded) (he236 := result) (hm235 := heap)
        (op294 := subtracted) (hm305 := push) (ev261 := child) (hc339 := events) .. =>
      have headInside : ∀ call ∈ heads, call ∈ calls := by intro call member; rw [events]; simp [member]
      have childInside : ∀ call ∈ children, call ∈ calls := by intro call member; rw [events]; simp [member]
      obtain ⟨headBound, headRaw, headRep, headTrace⟩ := Core.GuardData.head_raw_trace rawKey facts
        (good.sub headInside) (fun call member => subset call (headInside call member)) scopedRep physical headCall
      obtain ⟨headSemantic, headScoped, _⟩ := Core.GuardData.head_rep facts (good.sub headInside) scopedRep headCall
      obtain ⟨semantic, raw⟩ := headRep
      obtain ⟨RD, RB, ED, EB, u, rfl, rfl, rawDom, rawBody, rawLevel⟩ := raw.raw_forallE_view loaded
      obtain ⟨D, B, _, rfl, _, scopedBody, _⟩ := headScoped.forallE_of_load loaded
      have extension : Heap.Extends headHeap pushed := by rw [push]; exact Heap.Extends.snoc _ _
      have opened := (scopedBody.open_body (Ghost.extend_at Γ d D) (Ghost.extend_below Γ d D)).mono extension
      rw [evalBinOp_sub_succ n subtracted] at child
      obtain ⟨tailBound, tailRaw, tailRep, tailTrace⟩ := former_tele_at_raw rawKey facts n (by omega)
        (good.sub childInside) (fun call member => subset call (childInside call member)) opened
        ⟨_, rawBody.mono extension⟩ (datum.mono (headCall.heap_extends.trans extension)) child
      subst result heap
      have allExtended := extension.trans child.heap_extends
      obtain ⟨outBound, outRep⟩ := store_raw_forall
        (show RawExprRep rawKey after headBound RD dom from ⟨_, rawDom.mono allExtended⟩)
        tailRep (rawLevel.mono allExtended)
      exact ⟨outBound, _, outRep, .step headTrace tailTrace⟩

/-- The actual recursor builder produces the same consumed-prefix trace while retaining
its residual input at zero binders. -/
theorem nat_former_tele_raw (rawKey : _root_.Address → KKey) [∀ a, Resolved (rawKey a)]
    {c : ScopedCtx} (facts : ScopedCoreFacts c) {rootCalls : List (Call F)} :
    ∀ n {d k : Nat} {Γ : Nat → KExpr} {R E : KExpr}
      {rc p types r : SourceValue F} {h h' : Heap F} {calls : List (Call F)},
      n < 18446744069414584321 → CoreGood c calls → (∀ call ∈ calls, call ∈ rootCalls) →
      Tm c.κ d Γ h 0 E p → RawExprRep rawKey h k R p →
      ObsFn W "KernelCheck::nat_former_tele" [rc, p, .field (n : F), types] h r h' calls →
      ∃ bound result, RawExprRep rawKey h' bound result r ∧
        RawBinderTrace (RawDeltaAt c rawKey rootCalls) n R result
  | 0, d, k, Γ, R, E, rc, p, types, r, h, h', calls,
      _, good, subset, scopedRep, physical, observed => by
    match Obs.«KernelCheck::nat_former_tele».obs observed with
    | .n0 (he16 := result) (he17 := heap) .. =>
      subst result heap
      exact ⟨k, R, physical, .done _ _⟩
    | .other_Forall (hne19 := nonzero) .. | .other_other (hne19 := nonzero) .. =>
      exact (nonzero rfl).elim
  | n + 1, d, k, Γ, R, E, rc, p, types, r, h, h', calls,
      bound, good, subset, scopedRep, physical, observed => by
    match Obs.«KernelCheck::nat_former_tele».obs observed with
    | .n0 (hv14 := zero) .. => exact (succ_field_ne_zero_bounded bound zero).elim
    | .other_Forall (x_d := dom) (x_b := body) (x_m := metadata)
        (v66 := tailPtr) (m76 := after) (cs84 := children) (m121 := pushed)
        (ld34 := loaded) (he61 := result) (hm60 := heap) (op118 := subtracted)
        (hm129 := push) (ev86 := child) (hc156 := events) .. =>
      obtain ⟨semantic, raw⟩ := physical
      obtain ⟨RD, RB, ED, EB, u, rfl, rfl, rawDom, rawBody, rawLevel⟩ := raw.raw_forallE_view loaded
      obtain ⟨D, B, _, rfl, _, scopedBody, _⟩ := scopedRep.forallE_of_load loaded
      have extension : Heap.Extends h pushed := by rw [push]; exact Heap.Extends.snoc _ _
      have opened := (scopedBody.open_body (Ghost.extend_at Γ d D) (Ghost.extend_below Γ d D)).mono extension
      rw [evalBinOp_sub_succ n subtracted] at child
      have childInside : ∀ call ∈ children, call ∈ calls := by intro call member; rw [events]; simp [member]
      obtain ⟨tailBound, tailRaw, tailRep, tailTrace⟩ := nat_former_tele_raw rawKey facts n (by omega)
        (good.sub childInside) (fun call member => subset call (childInside call member))
        opened ⟨_, rawBody.mono extension⟩ child
      subst result heap
      have allExtended := extension.trans child.heap_extends
      obtain ⟨outBound, outRep⟩ := store_raw_forall
        (show RawExprRep rawKey after k RD dom from ⟨_, rawDom.mono allExtended⟩)
        tailRep (rawLevel.mono allExtended)
      exact ⟨outBound, _, outRep, .step (.forallE RD RB (bmeta u)) tailTrace⟩
    | .other_other (x_d := dom) (x_b := body) (x_m := metadata)
        (v220 := tailPtr) (m230 := after) (cs238 := children) (cs175 := heads)
        (m162 := headHeap) (p169 := headPtr) (m275 := pushed)
        (ev177 := headCall) (ld171 := loaded) (he215 := result) (hm214 := heap)
        (op272 := subtracted) (hm283 := push) (ev240 := child) (hc310 := events) .. =>
      have headInside : ∀ call ∈ heads, call ∈ calls := by intro call member; rw [events]; simp [member]
      have childInside : ∀ call ∈ children, call ∈ calls := by intro call member; rw [events]; simp [member]
      obtain ⟨headBound, headRaw, headRep, headTrace⟩ := Core.GuardData.head_raw_trace rawKey facts
        (good.sub headInside) (fun call member => subset call (headInside call member)) scopedRep physical headCall
      obtain ⟨headSemantic, headScoped, _⟩ := Core.GuardData.head_rep facts (good.sub headInside) scopedRep headCall
      obtain ⟨semantic, raw⟩ := headRep
      obtain ⟨RD, RB, ED, EB, u, rfl, rfl, rawDom, rawBody, rawLevel⟩ := raw.raw_forallE_view loaded
      obtain ⟨D, B, _, rfl, _, scopedBody, _⟩ := headScoped.forallE_of_load loaded
      have extension : Heap.Extends headHeap pushed := by rw [push]; exact Heap.Extends.snoc _ _
      have opened := (scopedBody.open_body (Ghost.extend_at Γ d D) (Ghost.extend_below Γ d D)).mono extension
      rw [evalBinOp_sub_succ n subtracted] at child
      obtain ⟨tailBound, tailRaw, tailRep, tailTrace⟩ := nat_former_tele_raw rawKey facts n (by omega)
        (good.sub childInside) (fun call member => subset call (childInside call member)) opened
        ⟨_, rawBody.mono extension⟩ child
      subst result heap
      have allExtended := extension.trans child.heap_extends
      obtain ⟨outBound, outRep⟩ := store_raw_forall
        (show RawExprRep rawKey after headBound RD dom from ⟨_, rawDom.mono allExtended⟩)
        tailRep (rawLevel.mono allExtended)
      exact ⟨outBound, _, outRep, .step headTrace tailTrace⟩

end IxVM.Refinement.Decl
