/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.Verify.Consistency.Inductive.Block

/-!
# Production recursor checks as execution traces

A stored recursor is checked in two passes over its block: its untouched
stored type is inferred and sort-checked, then `checkRecursorMemberImpl`
freezes the complete stored declaration, validates the major family and the
constructive K flag, populates canonical rules, selects the generated
candidate, and compares every header field, the complete closed type, and
every rule (field count and right-hand side) with the stored declaration by
definitional equality. For a singleton family the recursor block has one
member and one motive, so the exhaustive comparison path is the only success
path: there is no coherence escape.
-/

namespace Ix.Kernel.Consistency.Inductive

open Theory

private theorem bind_success {α β : Type} {x : TcM .anon α} {k : α → TcM .anon β}
    {before after : TcState .anon} {value : β}
    (accepted : EStateM.bind x k before = .ok value after) :
    ∃ intermediate state, x before = .ok intermediate state ∧
      k intermediate state = .ok value after := by
  rw [EStateM.bind] at accepted
  cases run : x before with
  | error err state => rw [run] at accepted; contradiction
  | ok intermediate state =>
      rw [run] at accepted
      exact ⟨intermediate, state, rfl, accepted⟩

/-! ### The stored declaration snapshot -/

/-- The frozen stored declaration comes from production lookup, with its
major-position sum computed from the stored arities. -/
theorem snapshot_success {id : KId .anon} {methods : Methods .anon} {before after : TcState .anon}
    {snapshot : RecM.RecursorMemberDeclarationSnapshot .anon}
    (h : (RecM.snapshotRecursorMemberDeclaration id).run methods before = .ok snapshot after) :
    ∃ name levelParams k isUnsafe lvls params indices motives minors block memberIdx ty rules leanAll
      loaded,
      TcM.getConst id before = .ok (KConst.recr name levelParams k isUnsafe lvls params indices motives
        minors block memberIdx ty rules leanAll) loaded ∧
      (RecM.checkedMetadataSum "recursor major index" #[params, motives, minors, indices]).run methods
        loaded = .ok snapshot.majorSkip after ∧
      snapshot.recBlock = block ∧ snapshot.ty = ty ∧ snapshot.declaredK = k ∧
      snapshot.declaredLvls = lvls ∧ snapshot.declaredIsUnsafe = isUnsafe ∧
      snapshot.params = params ∧ snapshot.motives = motives ∧ snapshot.minors = minors ∧
      snapshot.indices = indices ∧ snapshot.storedRules = rules := by
  unfold RecM.snapshotRecursorMemberDeclaration at h
  simp only [ReaderT.run_bind, ReaderT.run_monadLift] at h
  change EStateM.bind (TcM.getConst id) _ before = _ at h
  obtain ⟨concrete, loaded, getRun, h⟩ := bind_success h
  revert h
  cases concrete
  case recr name levelParams k isUnsafe lvls params indices motives minors block memberIdx ty rules
      leanAll =>
    intro h
    simp only [ReaderT.run_bind] at h
    change EStateM.bind (pure _) _ loaded = _ at h
    obtain ⟨_, _, hpure, h⟩ := bind_success h
    change EStateM.Result.ok _ loaded = _ at hpure
    cases hpure
    change EStateM.bind ((RecM.checkedMetadataSum "recursor major index"
      #[params, motives, minors, indices]).run methods) _ loaded = _ at h
    obtain ⟨majorSkip, skipState, skipRun, h⟩ := bind_success h
    change EStateM.Result.ok _ skipState = _ at h
    cases h
    exact ⟨name, levelParams, k, isUnsafe, lvls, params, indices, motives, minors, block, memberIdx, ty,
      rules, leanAll, loaded, getRun, skipRun, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  all_goals
    intro h
    change EStateM.Result.error _ loaded = _ at h
    cases h

/-- The constructive K flag is recomputed from the major family and compared
with the stored flag. -/
theorem kTarget_success {snapshot : RecM.RecursorMemberDeclarationSnapshot .anon} {indId : KId .anon}
    {methods : Methods .anon} {before after : TcState .anon} {computedK : Bool}
    (h : (RecM.validateRecursorMemberKTarget snapshot indId).run methods before = .ok computedK after) :
    (RecM.computeKTarget indId).run methods before = .ok computedK after ∧
      snapshot.declaredK = computedK := by
  unfold RecM.validateRecursorMemberKTarget at h
  simp only [ReaderT.run_bind] at h
  change EStateM.bind ((RecM.computeKTarget indId).run methods) _ before = _ at h
  obtain ⟨computed, state, kRun, h⟩ := bind_success h
  by_cases hk : (snapshot.declaredK != computed) = true
  · simp only [hk, if_true] at h
    change EStateM.Result.error _ state = _ at h
    cases h
  · simp only [hk, Bool.false_eq_true, if_false] at h
    change EStateM.Result.ok computed state = _ at h
    cases h
    exact ⟨kRun, by simpa using Bool.eq_false_iff.mpr hk⟩

/-! ### The exhaustive candidate comparison -/

/-- Every stored rule is compared with the generated rule at the same index:
equal field counts and definitionally equal right-hand sides. -/
inductive RulesTrace (generatedRules storedRules : Array (Kernel.RecRule .anon)) (methods : Methods .anon) :
    Nat → Nat → TcState .anon → TcState .anon → Type
  | nil (index : Nat) (state : TcState .anon) : RulesTrace generatedRules storedRules methods index 0 state state
  | cons {index fuel : Nat} {before middle after : TcState .anon}
      (fields : generatedRules[index]!.fields = storedRules[index]!.fields)
      (defEqRun : (RecM.isDefEq generatedRules[index]!.rhs storedRules[index]!.rhs).run methods before =
        .ok true middle)
      (tail : RulesTrace generatedRules storedRules methods (index + 1) fuel middle after) :
      RulesTrace generatedRules storedRules methods index (fuel + 1) before after

theorem rules_trace {generatedRules storedRules : Array (Kernel.RecRule .anon)} {methods : Methods .anon} :
    ∀ {index fuel : Nat} {before after : TcState .anon},
      (RecM.checkGeneratedRecursorRules generatedRules storedRules index fuel).run methods before =
        .ok () after →
      Nonempty (RulesTrace generatedRules storedRules methods index fuel before after)
  | index, 0, before, after, h => by
      simp only [RecM.checkGeneratedRecursorRules, ReaderT.run_pure] at h
      change EStateM.Result.ok () before = _ at h
      cases h
      exact ⟨.nil index before⟩
  | index, fuel + 1, before, after, h => by
      unfold RecM.checkGeneratedRecursorRules at h
      by_cases hfields : (generatedRules[index]!.fields != storedRules[index]!.fields) = true
      · simp only [hfields, if_true, ReaderT.run_bind] at h
        change EStateM.Result.error _ before = _ at h
        cases h
      · simp only [hfields, Bool.false_eq_true, if_false, ReaderT.run_bind] at h
        change EStateM.bind ((RecM.isDefEq generatedRules[index]!.rhs storedRules[index]!.rhs).run
          methods) _ before = _ at h
        obtain ⟨answer, middle, defEqRun, h⟩ := bind_success h
        cases answer with
        | false =>
            simp only [Bool.not_false, if_true] at h
            change EStateM.Result.error _ middle = _ at h
            cases h
        | true =>
            simp only [Bool.not_true, Bool.false_eq_true, if_false] at h
            obtain ⟨tail⟩ := rules_trace h
            exact ⟨.cons (by simpa using Bool.eq_false_iff.mpr hfields) defEqRun tail⟩

/-- The successful exhaustive comparison of the stored declaration with the
selected generated candidate. -/
structure CandidateCheckRun (ty : KExpr .anon) (declaredLvls : UInt64) (declaredIsUnsafe : Bool)
    (params motives minors indices : UInt64) (storedRules : Array (Kernel.RecRule .anon))
    (generated : GeneratedRecursor .anon) (methods : Methods .anon) (before : TcState .anon) where
  lvls : declaredLvls = generated.lvls
  isUnsafe : declaredIsUnsafe = generated.isUnsafe
  params : params = generated.params
  motives : motives = generated.motives
  minors : minors = generated.minors
  indices : indices = generated.indices
  typeState : TcState .anon
  typeRun : (RecM.isDefEq generated.ty ty).run methods before = .ok true typeState
  ruleCount : generated.rules.size = storedRules.size
  after : TcState .anon
  rules : RulesTrace generated.rules storedRules methods 0 generated.rules.size typeState after

theorem candidate_check_run {ty : KExpr .anon} {declaredLvls : UInt64} {declaredIsUnsafe : Bool}
    {params motives minors indices : UInt64} {storedRules : Array (Kernel.RecRule .anon)}
    {generated : GeneratedRecursor .anon} {methods : Methods .anon} {before after : TcState .anon}
    (h : (RecM.checkGeneratedRecursorCandidate ty declaredLvls declaredIsUnsafe params motives minors
      indices storedRules generated).run methods before = .ok () after) :
    ∃ run : CandidateCheckRun ty declaredLvls declaredIsUnsafe params motives minors indices storedRules
      generated methods before, run.after = after := by
  unfold RecM.checkGeneratedRecursorCandidate at h
  by_cases hlvls : (declaredLvls != generated.lvls) = true
  · simp only [hlvls, if_true, ReaderT.run_bind] at h
    change EStateM.Result.error _ before = _ at h
    cases h
  simp only [hlvls, Bool.false_eq_true, if_false] at h
  by_cases hunsafe : (declaredIsUnsafe != generated.isUnsafe) = true
  · simp only [hunsafe, if_true, ReaderT.run_bind] at h
    change EStateM.Result.error _ before = _ at h
    cases h
  simp only [hunsafe, Bool.false_eq_true, if_false] at h
  by_cases harity : (params != generated.params || motives != generated.motives ||
      minors != generated.minors || indices != generated.indices) = true
  · simp only [harity, if_true, ReaderT.run_bind] at h
    change EStateM.Result.error _ before = _ at h
    cases h
  simp only [harity, Bool.false_eq_true, if_false, ReaderT.run_bind] at h
  change EStateM.bind ((RecM.isDefEq generated.ty ty).run methods) _ before = _ at h
  obtain ⟨answer, typeState, typeRun, h⟩ := bind_success h
  cases answer with
  | false =>
      simp only [Bool.not_false, if_true] at h
      change EStateM.Result.error _ typeState = _ at h
      cases h
  | true =>
      simp only [Bool.not_true, Bool.false_eq_true, if_false] at h
      by_cases hempty : (generated.rules.isEmpty && !storedRules.isEmpty) = true
      · simp only [hempty, if_true] at h
        change EStateM.Result.error _ typeState = _ at h
        cases h
      simp only [hempty, Bool.false_eq_true, if_false] at h
      by_cases hmissing : (!generated.rules.isEmpty && storedRules.isEmpty) = true
      · simp only [hmissing, if_true] at h
        change EStateM.Result.error _ typeState = _ at h
        cases h
      simp only [hmissing, Bool.false_eq_true, if_false] at h
      by_cases hsize : (generated.rules.size != storedRules.size) = true
      · simp only [hsize, if_true] at h
        change EStateM.Result.error _ typeState = _ at h
        cases h
      simp only [hsize, Bool.false_eq_true, if_false] at h
      obtain ⟨rules⟩ := rules_trace h
      have harity' := Bool.eq_false_iff.mpr harity
      simp only [Bool.or_eq_false_iff, bne_eq_false_iff_eq] at harity'
      exact ⟨⟨by simpa using Bool.eq_false_iff.mpr hlvls, by simpa using Bool.eq_false_iff.mpr hunsafe,
        harity'.1.1.1, harity'.1.1.2, harity'.1.2, harity'.2, typeState, typeRun,
        by simpa using Bool.eq_false_iff.mpr hsize, after, rules⟩, rfl⟩

/-! ### The member check -/

/-- The stateful prelude and the frozen inputs it hands to the comparison. -/
structure PreparedRun (id : KId .anon) (methods : Methods .anon) (before : TcState .anon) where
  snapshot : RecM.RecursorMemberDeclarationSnapshot .anon
  snapshotState : TcState .anon
  snapshotRun : (RecM.snapshotRecursorMemberDeclaration id).run methods before = .ok snapshot snapshotState
  indId : KId .anon
  majorState : TcState .anon
  majorRun : (RecM.validateRecursorMemberMajor snapshot).run methods snapshotState = .ok indId majorState
  resolvedBlock : KId .anon
  resolvedState : TcState .anon
  resolveRun : (RecM.resolveRecursorMemberBlock snapshot indId).run methods majorState =
    .ok resolvedBlock resolvedState
  computedK : Bool
  kState : TcState .anon
  kRun : (RecM.validateRecursorMemberKTarget snapshot indId).run methods resolvedState =
    .ok computedK kState
  populated : TcState .anon
  populateRun : (RecM.populateRecursorRulesFromBlock resolvedBlock snapshot.recBlock).run methods kState =
    .ok () populated
  generated : Array (GeneratedRecursor .anon)
  after : TcState .anon
  generatedRun : (RecM.snapshotGeneratedRecursors resolvedBlock).run methods populated =
    .ok generated after

/-- The prepared inputs handed to the comparison tail. -/
def PreparedRun.prepared {id : KId .anon} {methods : Methods .anon} {before : TcState .anon}
    (run : PreparedRun id methods before) : RecM.PreparedRecursorMemberCheck .anon :=
  { recBlock := run.snapshot.recBlock
    ty := run.snapshot.ty
    declaredK := run.snapshot.declaredK
    declaredLvls := run.snapshot.declaredLvls
    declaredIsUnsafe := run.snapshot.declaredIsUnsafe
    params := run.snapshot.params
    motives := run.snapshot.motives
    minors := run.snapshot.minors
    indices := run.snapshot.indices
    storedRules := run.snapshot.storedRules
    indId := run.indId
    resolvedBlock := run.resolvedBlock
    computedK := run.computedK
    generated := run.generated }

theorem prepared_run {id : KId .anon} {methods : Methods .anon} {before after : TcState .anon}
    {prepared : RecM.PreparedRecursorMemberCheck .anon}
    (h : (RecM.prepareRecursorMemberCheck id).run methods before = .ok prepared after) :
    ∃ run : PreparedRun id methods before, run.after = after ∧ run.prepared = prepared := by
  unfold RecM.prepareRecursorMemberCheck at h
  simp only [ReaderT.run_bind] at h
  change EStateM.bind ((RecM.snapshotRecursorMemberDeclaration id).run methods) _ before = _ at h
  obtain ⟨snapshot, snapshotState, snapshotRun, h⟩ := bind_success h
  change EStateM.bind ((RecM.validateRecursorMemberMajor snapshot).run methods) _ snapshotState = _ at h
  obtain ⟨indId, majorState, majorRun, h⟩ := bind_success h
  change EStateM.bind ((RecM.resolveRecursorMemberBlock snapshot indId).run methods) _ majorState =
    _ at h
  obtain ⟨resolvedBlock, resolvedState, resolveRun, h⟩ := bind_success h
  change EStateM.bind ((RecM.validateRecursorMemberKTarget snapshot indId).run methods) _
    resolvedState = _ at h
  obtain ⟨computedK, kState, kRun, h⟩ := bind_success h
  change EStateM.bind ((RecM.populateRecursorRulesFromBlock resolvedBlock snapshot.recBlock).run
    methods) _ kState = _ at h
  obtain ⟨⟨⟩, populated, populateRun, h⟩ := bind_success h
  change EStateM.bind ((RecM.snapshotGeneratedRecursors resolvedBlock).run methods) _ populated =
    _ at h
  obtain ⟨generated, generatedState, generatedRun, h⟩ := bind_success h
  change EStateM.Result.ok _ generatedState = _ at h
  cases h
  exact ⟨⟨snapshot, snapshotState, snapshotRun, indId, majorState, majorRun, resolvedBlock,
    resolvedState, resolveRun, computedK, kState, kRun, populated, populateRun, generated,
    _, generatedRun⟩, rfl, rfl⟩

/-- The complete member check: the prelude, candidate selection, and the
exhaustive comparison of the selected candidate. -/
structure RecursorMemberTrace (id : KId .anon) (methods : Methods .anon) (before : TcState .anon) where
  prepared : PreparedRun id methods before
  selectedIdx : Option Nat
  selectedState : TcState .anon
  selectRun : (RecM.selectGeneratedRecursorIndex prepared.snapshot.recBlock id prepared.snapshot.ty
    prepared.snapshot.params prepared.snapshot.motives prepared.snapshot.minors prepared.indId
    prepared.generated).run methods prepared.after = .ok selectedIdx selectedState
  selected : GeneratedRecursor .anon
  selection : selectedIdx.bind (prepared.generated[·]?) = some selected
  candidate : CandidateCheckRun prepared.snapshot.ty prepared.snapshot.declaredLvls
    prepared.snapshot.declaredIsUnsafe prepared.snapshot.params prepared.snapshot.motives
    prepared.snapshot.minors prepared.snapshot.indices prepared.snapshot.storedRules selected methods
    selectedState

theorem recursor_member_trace {id : KId .anon} {methods : Methods .anon} {before after : TcState .anon}
    (h : (RecM.checkRecursorMemberImpl id).run methods before = .ok () after) :
    ∃ trace : RecursorMemberTrace id methods before, trace.candidate.after = after := by
  unfold RecM.checkRecursorMemberImpl at h
  simp only [ReaderT.run_bind] at h
  change EStateM.bind ((RecM.prepareRecursorMemberCheck id).run methods) _ before = _ at h
  obtain ⟨prepared, preparedState, preparedRun, h⟩ := bind_success h
  obtain ⟨run, rfl, rfl⟩ := prepared_run preparedRun
  change (RecM.checkGeneratedRecursorFromCache run.snapshot.recBlock id run.snapshot.ty
    run.snapshot.declaredLvls run.snapshot.declaredIsUnsafe run.snapshot.params run.snapshot.motives
    run.snapshot.minors run.snapshot.indices run.indId run.snapshot.storedRules run.generated).run
    methods run.after = _ at h
  unfold RecM.checkGeneratedRecursorFromCache at h
  simp only [ReaderT.run_bind] at h
  change EStateM.bind ((RecM.selectGeneratedRecursorIndex run.snapshot.recBlock id run.snapshot.ty
    run.snapshot.params run.snapshot.motives run.snapshot.minors run.indId run.generated).run
    methods) _ run.after = _ at h
  obtain ⟨selectedIdx, selectedState, selectRun, h⟩ := bind_success h
  revert h
  cases hsel : selectedIdx.bind (run.generated[·]?) with
  | none =>
      intro h
      change EStateM.Result.error _ selectedState = _ at h
      cases h
  | some selected =>
      intro h
      obtain ⟨candidate, rfl⟩ := candidate_check_run h
      exact ⟨⟨run, selectedIdx, selectedState, selectRun, selected, hsel, candidate⟩, rfl⟩

/-- Singleton families have one motive, so the selected candidate is compared
in full with the stored declaration; no coherence escape exists. -/
theorem RecursorMemberTrace.strict {id : KId .anon} {methods : Methods .anon} {before : TcState .anon}
    (trace : RecursorMemberTrace id methods before) :
    trace.prepared.snapshot.declaredLvls = trace.selected.lvls ∧
      trace.prepared.snapshot.declaredIsUnsafe = trace.selected.isUnsafe ∧
      trace.prepared.snapshot.motives = trace.selected.motives ∧
      (RecM.isDefEq trace.selected.ty trace.prepared.snapshot.ty).run methods trace.selectedState =
        .ok true trace.candidate.typeState ∧
      trace.selected.rules.size = trace.prepared.snapshot.storedRules.size ∧
      trace.prepared.snapshot.declaredK = trace.prepared.computedK :=
  ⟨trace.candidate.lvls, trace.candidate.isUnsafe, trace.candidate.motives, trace.candidate.typeRun,
    trace.candidate.ruleCount, (kTarget_success trace.prepared.kRun).2⟩

/-! ### The singleton recursor block -/

/-- Whether a loaded declaration is a recursor. -/
def isRecursorDecl : KConst .anon → Bool
  | .recr .. => true
  | _ => false

/-- The two passes of `checkRecursorBlockImpl` over a one-member block. -/
structure RecursorBlockTrace (member : KId .anon) (methods : Methods .anon) (before : TcState .anon) where
  typeRun : MemberTypeRun member methods before
  recursor : isRecursorDecl typeRun.concrete = true
  reset : TcState .anon
  resetRun : TcM.reset typeRun.after = .ok () reset
  memberCheck : RecursorMemberTrace member methods reset

theorem recursor_block_trace {block member : KId .anon} {methods : Methods .anon}
    {before after : TcState .anon}
    (h : (RecM.checkRecursorBlockImpl block #[member]).run methods before = .ok () after) :
    ∃ trace : RecursorBlockTrace member methods before, trace.memberCheck.candidate.after = after := by
  unfold RecM.checkRecursorBlockImpl at h
  simp only [← Array.forIn_toList, List.forIn_cons, List.forIn_nil, ReaderT.run_bind,
    ReaderT.run_monadLift] at h
  change EStateM.bind (EStateM.bind (EStateM.bind TcM.reset _) _) _ before = _ at h
  obtain ⟨_, firstState, first, h⟩ := bind_success h
  obtain ⟨step, stepState, inner, firstMatch⟩ := bind_success first
  obtain ⟨⟨⟩, reset₁, resetRun₁, inner⟩ := bind_success inner
  change EStateM.bind (TcM.getConst member) _ reset₁ = _ at inner
  obtain ⟨concrete, loaded, getRun, inner⟩ := bind_success inner
  change EStateM.bind ((RecM.validateConstWellScoped concrete).run methods) _ loaded = _ at inner
  obtain ⟨⟨⟩, validated, validationRun, inner⟩ := bind_success inner
  revert inner
  cases concrete
  case recr name levelParams k isUnsafe lvls params indices motives minors recBlock memberIdx ty rules
      leanAll =>
    intro inner
    simp only [ReaderT.run_bind] at inner
    change EStateM.bind ((RecM.infer ty).run methods) _ validated = _ at inner
    obtain ⟨inferred, typeState, typeRun, inner⟩ := bind_success inner
    change EStateM.bind ((RecM.ensureSortDirect inferred).run methods) _ typeState = _ at inner
    obtain ⟨level, sortState, sortRun, inner⟩ := bind_success inner
    change EStateM.Result.ok (ForInStep.yield ()) sortState = _ at inner
    cases inner
    change EStateM.Result.ok () stepState = _ at firstMatch
    cases firstMatch
    change EStateM.bind (EStateM.bind (EStateM.bind TcM.reset _) _) _ _ = _ at h
    obtain ⟨_, secondState, second, h⟩ := bind_success h
    obtain ⟨step₂, stepState₂, inner₂, secondMatch⟩ := bind_success second
    obtain ⟨⟨⟩, reset₂, resetRun₂, inner₂⟩ := bind_success inner₂
    change EStateM.bind ((RecM.checkRecursorMemberImpl member).run methods) _ reset₂ = _ at inner₂
    obtain ⟨⟨⟩, checked, checkRun, inner₂⟩ := bind_success inner₂
    obtain ⟨memberCheck, rfl⟩ := recursor_member_trace checkRun
    change EStateM.Result.ok (ForInStep.yield ()) memberCheck.candidate.after = _ at inner₂
    cases inner₂
    change EStateM.Result.ok () memberCheck.candidate.after = _ at secondMatch
    cases secondMatch
    change EStateM.Result.ok () memberCheck.candidate.after = _ at h
    cases h
    exact ⟨⟨⟨_, reset₁, loaded, validated, inferred, typeState, level, _, resetRun₁, getRun,
      validationRun, typeRun, sortRun⟩, rfl, reset₂, resetRun₂, memberCheck⟩, rfl⟩
  all_goals
    intro inner
    simp only [ReaderT.run_bind] at inner
    change EStateM.bind (throw _) _ validated = _ at inner
    obtain ⟨_, _, hthrow, _⟩ := bind_success inner
    change EStateM.Result.error _ validated = _ at hthrow
    cases hthrow

end Ix.Kernel.Consistency.Inductive
