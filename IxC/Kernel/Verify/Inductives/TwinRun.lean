module

public import IxC.Kernel.Inductives.TwinInstall
public import IxC.Kernel.Semantics.Inductives.DeclRecTwinJ

public section

/-! # Facts from the executable stored-recursor twin checks -/

namespace Ix.Kernel.NativeTwin

open Ix.Kernel.Semantics

def Part.semantic (part : Part md) : TwinRecPart md := {
  cvW := part.raw
  cvW' := part.annotated
  cvC := part.canonical
  kC := part.canonicalKey
  mI := part.majorIndex
  rP := part.rulePrefix
  rulesW := part.rawRules
  rulesW' := part.checkedRules
  rulesC := part.canonicalRules
  model? := part.model? }

@[simp] theorem semantic_models (parts : List (Part md)) :
    twinModels (parts.map Part.semantic) = models parts := by
  simp only [twinModels, models, List.filterMap_map]
  rfl

@[simp] theorem semantic_provision (parts : List (Part md)) :
    twinProv (parts.map Part.semantic) = provision parts := by
  simp only [twinProv, provision, List.map_map]
  rfl

@[simp] theorem semantic_recursors (parts : List (Part md)) :
    twinRecs (parts.map Part.semantic) = recursors parts := by
  simp only [twinRecs, recursors, List.map_map]
  rfl

theorem majorAgrees_spec {majorIndex : Nat} {canonical annotated : Expr md}
    (h : majorAgrees majorIndex canonical annotated = true)
    {bsW : List (Expr md × BinderMeta)} {domW bodyW : Expr md} {bmW : BinderMeta}
    (hW : annotated.stripPis majorIndex = some (bsW, .forallE domW bodyW bmW)) :
    ∃ bsC domC bodyC bmC,
      canonical.stripPis majorIndex = some (bsC, .forallE domC bodyC bmC) ∧
      domW.getAppFn = domC.getAppFn ∧ domW.getAppArgs = domC.getAppArgs := by
  simp only [majorAgrees, hW] at h
  split at h
  next bsC domC bodyC bmC hC =>
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    exact ⟨bsC, domC, bodyC, bmC, hC, h⟩
  next hC => cases h

theorem ruleShape_plain {env : Env md} {part : Part md} {rule : RecRule md}
    (h : ruleShape env part rule = true) (hfire : rule.fire = .plain)
    {cv : ConstantVal md} {nP nF : Nat} (hfind : env.find? rule.ctor = some (.ctorInfo cv nP nF)) :
    Expr.recRulePlain part.annotated.type part.majorIndex part.rulePrefix rule.ctorParams cv.levelParams = true := by
  simpa only [ruleShape, hfire, hfind] using h

theorem ruleShape_nested {env : Env md} {part : Part md} {rule : RecRule md}
    (h : ruleShape env part rule = true) {levels : List Level} {pins : List (Expr md)}
    (hfire : rule.fire = .nested levels pins) :
    ∃ pre dom body bm D,
      part.annotated.type.stripPis part.majorIndex = some (pre, .forallE dom body bm) ∧
      dom.getAppFn = .const D levels ∧
      dom.getAppArgs =
        pins.map (Expr.liftLooseBVars (part.majorIndex - part.rulePrefix) 0) ++
          (List.range (part.majorIndex - part.rulePrefix)).map
            (fun i => Expr.bvar (part.majorIndex - part.rulePrefix - 1 - i)) := by
  simp only [ruleShape, hfire] at h
  split at h
  next pre dom body bm hshape =>
    split at h
    next D foundLevels hhead =>
      simp only [Bool.and_eq_true, beq_iff_eq] at h
      obtain ⟨rfl, hargs⟩ := h
      exact ⟨pre, dom, body, bm, D, hshape, hhead, hargs⟩
    next hhead => cases h
  next hshape => cases h

/-- The executable peer map changes only canonical names of this checked group. -/
theorem peerRename_spec (parts : List (Part md)) (key : Key md) :
    peerRename parts key = key ∨
      ∃ part ∈ parts, key = part.canonicalKey ∧ peerRename parts key = part.raw.name := by
  unfold peerRename
  cases hfind : parts.find? (fun part => part.canonicalKey == key) with
  | none => exact .inl rfl
  | some part =>
    exact .inr ⟨part, List.mem_of_find?_eq_some hfind,
      (beq_iff_eq.mp (List.find?_some hfind)).symm, rfl⟩

/-- A successful finishing check chooses one common rule renaming for the complete group. -/
theorem finish_spec {env output : Env md} {parts : List (Part md)}
    (h : finish (m := CheckM md) env parts = .ok output) :
    ∃ rename : Key md → Key md,
      (∀ key, rename key = key ∨ ∃ part ∈ parts, key = part.canonicalKey ∧ rename key = part.raw.name) ∧
      rulesWrap env rename parts = true ∧
      output = ⟨recursors parts ++ models parts ++ env.consts⟩ := by
  unfold finish at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  next hwrap =>
    cases h
    rcases Bool.or_eq_true.mp hwrap with hid | hpeer
    · exact ⟨id, fun _ => .inl rfl, hid, rfl⟩
    · exact ⟨peerRename parts, peerRename_spec parts, hpeer, rfl⟩
  next hwrap => cases h

def ModelSource (env : Env md) (part : Part md) : Prop :=
  match part.model? with
  | some (cv, value, hint) =>
    env.find? (auxKey part.canonicalKey .model) = some (.defnInfo cv value hint)
  | none =>
    (∀ cv value hint, env.find? (auxKey part.canonicalKey .model) ≠ some (.defnInfo cv value hint)) ∧
    (∀ bsW domW bodyW bmW,
      part.annotated.type.stripPis part.majorIndex = some (bsW, .forallE domW bodyW bmW) →
      ∃ bsC domC bodyC bmC,
        part.canonical.type.stripPis part.majorIndex = some (bsC, .forallE domC bodyC bmC) ∧
        domW.getAppFn = domC.getAppFn ∧ domW.getAppArgs = domC.getAppArgs)

structure CanonicalPart (env : Env md) (part : Part md) : Prop where
  stored : env.find? part.canonicalKey =
    some (.recInfo part.canonical part.majorIndex part.rulePrefix part.canonicalRules)
  levels : part.raw.levelParams = part.canonical.levelParams
  ruleCount : part.rawRules.length = part.canonicalRules.length
  typeWrap : WrapRel env.find? part.canonical.type part.annotated.type
  model : ModelSource env part

private theorem modelSource_of_guard (env : Env md) (part : Part md)
    (hmodel : part.model? = match env.find? (auxKey part.canonicalKey .model) with
      | some (.defnInfo cv value hint) => some (cv, value, hint)
      | _ => none)
    (hguard : (part.model?.isSome || majorAgrees part.majorIndex part.canonical.type part.annotated.type) = true) :
    ModelSource env part := by
  cases hfind : env.find? (auxKey part.canonicalKey .model) with
  | none =>
    simp only [hfind] at hmodel
    simp only [hmodel, Option.isSome_none, Bool.false_or] at hguard
    simp only [ModelSource, hmodel]
    refine ⟨?_, fun _ _ _ _ h => majorAgrees_spec hguard h⟩
    intro cv value hint
    simp [hfind]
  | some ci =>
    cases ci with
    | defnInfo cv value hint =>
      simp only [hfind] at hmodel
      simp only [ModelSource, hmodel]
      exact hfind
    | _ =>
      simp only [hfind] at hmodel
      simp only [hmodel, Option.isSome_none, Bool.false_or] at hguard
      simp only [ModelSource, hmodel]
      refine ⟨?_, fun _ _ _ _ h => majorAgrees_spec hguard h⟩
      intro cv value hint
      simp [hfind]

theorem candidate_spec {env : Env md} {raw annotated : ConstantVal md} {mI rP : Nat}
    {rules : List (RecRule md)} {key : Key md} {part : Part md}
    (h : candidate env.find? raw annotated mI rP rules key = some part) :
    part.raw = raw ∧ part.annotated = annotated ∧ part.majorIndex = mI ∧
      part.rulePrefix = rP ∧ part.rawRules = rules ∧ CanonicalPart env part := by
  unfold candidate at h
  split at h
  next canonical mI' rP' canonicalRules hfind =>
    simp only [bind, Option.bind, pure, Option.pure] at h
    split at h
    next hguard =>
      simp only [bind, Option.bind, pure, Option.pure] at h
      split at h
      next hmodel =>
        simp only [bind, Option.bind, pure, Option.pure, Option.some.injEq] at h
        subst part
        simp only [Bool.and_eq_true, beq_iff_eq] at hguard
        obtain ⟨⟨⟨⟨hmI, hrP⟩, hlevels⟩, hcount⟩, hwrap⟩ := hguard
        subst mI'; subst rP'
        refine ⟨rfl, rfl, rfl, rfl, rfl, ⟨hfind, hlevels, hcount, wrapRelOk_sound hwrap, ?_⟩⟩
        exact modelSource_of_guard env _ rfl hmodel
      next hmodel => cases h
    next hguard => cases h
  next hfind => cases h

theorem findCanonical_spec {env : Env md} {raw annotated : ConstantVal md} {mI rP : Nat}
    {rules : List (RecRule md)} {part : Part md} :
    ∀ entries : List (ConstantInfo md),
      findCanonical env.find? raw annotated mI rP rules entries = some part →
      part.raw = raw ∧ part.annotated = annotated ∧ part.majorIndex = mI ∧
        part.rulePrefix = rP ∧ part.rawRules = rules ∧ CanonicalPart env part
  | [], h => by cases h
  | ci :: entries, h => by
    cases ci with
    | recInfo cv majorIndex prefix canonicalRules =>
      simp only [findCanonical] at h
      cases hcandidate : candidate env.find? raw annotated mI rP rules cv.name with
      | none =>
        simp only [hcandidate, Option.orElse_none] at h
        exact findCanonical_spec entries h
      | some found =>
        simp only [hcandidate, Option.orElse_some] at h
        cases h
        exact candidate_spec hcandidate
    | _ => exact findCanonical_spec entries h

/-- Successful executable header checks provide the actual declaration judgement and
the stored canonical source used by the twin model theorem. -/
theorem checkHeader_spec {mode : CheckMode} {fuel : Nat} {env : Env md}
    {ci : ConstantInfo md} {part : Part md}
    (h : checkHeader (fueledOps mode fuel) env ci = .ok part) :
    ci = .recInfo part.raw part.majorIndex part.rulePrefix part.rawRules ∧
      ConstantValCheckJ (runJ mode fuel) env part.raw part.annotated ∧
      letFree part.annotated.type = true ∧ CanonicalPart env part := by
  cases ci with
  | recInfo raw majorIndex prefix rules =>
    unfold checkHeader at h
    simp only [bind, Except.bind] at h
    cases hchecked : checkConstantVal (fueledOps mode fuel) env raw with
    | error reason => rw [hchecked] at h; cases h
    | ok annotated =>
      rw [hchecked] at h
      split at h
      next hfree =>
        simp only [bind, Except.bind, pure, Except.pure] at h
        cases hcanonical : findCanonical env.find? raw annotated majorIndex prefix rules env.consts with
        | none => simp [hcanonical, throw, throwThe, MonadExceptOf.throw] at h
        | some found =>
          simp only [hcanonical, Except.ok.injEq] at h
          subst part
          obtain ⟨hraw, hannotated, hmajor, hprefix, hrules, hsource⟩ := findCanonical_spec env.consts hcanonical
          refine ⟨?_, ?_, ?_, hsource⟩
          · rw [hraw, hmajor, hprefix, hrules]
          · rw [hraw, hannotated]
            exact constantValCheckJ_of_run hchecked
          · rwa [hannotated]
      next hfree => cases h
  | _ => simp [checkHeader, throw, throwThe, MonadExceptOf.throw] at h

theorem checkRule_spec {mode : CheckMode} {fuel : Nat} {env envSelf : Env md}
    {part : Part md} {raw canonical checked : RecRule md}
    (h : checkRule (fueledOps mode fuel) env envSelf part raw canonical = .ok checked) :
    raw.ctor = canonical.ctor ∧ raw.nfields = canonical.nfields ∧
      raw.rhs.looseBVarsBounded 0 = true ∧ raw.rhs.hasFvar = false ∧
      (runJ mode fuel).annot envSelf 0 raw.rhs checked.rhs ∧
      checked.rhs.allLevelParamsDefined part.canonical.levelParams = true ∧
      checked.rhs.constsResolve envSelf = true ∧ letFree checked.rhs = true ∧
      ruleShape env part canonical = true ∧
      checked = { canonical with rhs := checked.rhs,
        eta := recRuleEtaOf env.find? part.raw.name canonical.ctor } := by
  unfold checkRule at h
  simp only [bind, Except.bind] at h
  split at h
  next hmeta =>
    simp only [bind, Except.bind] at h
    split at h
    next hraw =>
      simp only [bind, Except.bind] at h
      cases hann : (fueledOps mode fuel).annotate envSelf 0 raw.rhs with
      | error reason => rw [hann] at h; cases h
      | ok rhs =>
        rw [hann] at h
        split at h
        next hscope =>
          simp only [bind, Except.bind] at h
          split at h
          next hshape =>
            simp only [pure, Except.pure, Except.ok.injEq] at h
            subst checked
            simp only [Bool.and_eq_true, beq_iff_eq] at hmeta
            simp only [Bool.and_eq_true, Bool.not_eq_true] at hraw
            simp only [Bool.and_eq_true] at hscope
            exact ⟨hmeta.1, hmeta.2, hraw.1, hraw.2, hann,
              hscope.1.1, hscope.1.2, hscope.2, hshape, rfl⟩
          next hshape => cases h
        next hscope => cases h
    next hraw => cases h
  next hmeta => cases h

/-- Once the finishing check supplies its common renaming, a successful rule run is the
existing semantic twin-rule judgement with the canonical rule as generated RHS. -/
theorem checkRule_twin {mode : CheckMode} {fuel : Nat} {env envSelf : Env md}
    {part : Part md} {raw canonical checked : RecRule md} {rename : Key md → Key md}
    (h : checkRule (fueledOps mode fuel) env envSelf part raw canonical = .ok checked)
    (hwrap : WrapRel env.find? (canonical.rhs.renameConsts rename) checked.rhs) :
    TwinRuleJ (runJ mode fuel) env envSelf rename part.raw.name part.canonical.levelParams
      part.annotated part.majorIndex part.rulePrefix raw checked canonical := by
  obtain ⟨hctor, hfields, hbounded, hfvar, hann, hlevels, hresolve, hfree, hshape, hout⟩ :=
    checkRule_spec h
  have checkedCtor : checked.ctor = canonical.ctor := by rw [hout]
  have checkedFields : checked.nfields = canonical.nfields := by rw [hout]
  refine ⟨hctor.trans checkedCtor.symm, hfields.trans checkedFields.symm,
    hbounded, hfvar, hann, hlevels, hresolve, hfree, checkedCtor, checkedFields,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, canonical.rhs, WrapRel.refl _ _, hwrap, .inl rfl⟩
  · rw [hout]
  · rw [hout]
  · rw [hout]
  · rw [hout]
  · rw [hout]
  · intro hfire cv nP nF hfind
    have hfire' : canonical.fire = .plain := by simpa only [hout] using hfire
    have hfind' : env.find? canonical.ctor = some (.ctorInfo cv nP nF) := by
      simpa only [checkedCtor] using hfind
    simpa only [hout] using ruleShape_plain hshape hfire' hfind'
  · intro levels pins hfire
    have hfire' : canonical.fire = .nested levels pins := by simpa only [hout] using hfire
    exact ruleShape_nested hshape hfire'

end Ix.Kernel.NativeTwin
