module

public import IxC.Kernel.Inductives.TwinInstall
public import IxC.Kernel.Semantics.Inductives.DeclRecTwinJ

@[expose] public section

/-! # Facts from the executable stored-recursor twin checks -/

namespace Ix.Kernel.NativeTwin

open Ix.Kernel.Semantics

private theorem check_bind_ok {α β : Type} {x : CheckM md α} {f : α → CheckM md β} {b : β}
    (h : (x >>= f) = .ok b) : ∃ a, x = .ok a ∧ f a = .ok b := by
  cases hx : x with
  | error reason => simp [hx, bind, Except.bind] at h
  | ok a => exact ⟨a, rfl, by simpa only [hx, bind, Except.bind] using h⟩

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
    have hkey : (part.canonicalKey == key) = true := List.find?_some hfind
    exact .inr ⟨part, List.mem_of_find?_eq_some hfind,
      (beq_iff_eq.mp hkey).symm, rfl⟩

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
    rcases Bool.or_eq_true_iff.mp hwrap with hid | hpeer
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
    simp only [bind, Option.bind, pure] at h
    split at h
    next hguard =>
      dsimp only [bind, Option.bind, pure] at h
      split at h
      next hmodel =>
        simp only [bind, Option.bind, pure, Option.some.injEq] at h
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
    | recInfo cv majorIndex rulePrefixValue canonicalRules =>
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
  | recInfo raw majorIndex rulePrefixValue rules =>
    unfold checkHeader at h
    simp only [bind, Except.bind] at h
    cases hchecked : checkConstantVal (fueledOps mode fuel) env raw with
    | error reason => rw [hchecked] at h; cases h
    | ok annotated =>
      rw [hchecked] at h
      split at h
      next hfree =>
        simp only [bind, Except.bind, pure, Except.pure] at h
        cases hcanonical : findCanonical env.find? raw annotated majorIndex rulePrefixValue rules env.consts with
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

def HeaderChecked (mode : CheckMode) (fuel : Nat) (env : Env md) (part : Part md) : Prop :=
  ConstantValCheckJ (runJ mode fuel) env part.raw part.annotated ∧
    letFree part.annotated.type = true ∧ CanonicalPart env part

theorem checkHeaders_spec {mode : CheckMode} {fuel : Nat} {env : Env md} :
    ∀ (block : List (ConstantInfo md)) {parts : List (Part md)},
      checkHeaders (fueledOps mode fuel) env block = .ok parts →
      block = parts.map (fun part => .recInfo part.raw part.majorIndex part.rulePrefix part.rawRules) ∧
        ∀ part ∈ parts, HeaderChecked mode fuel env part
  | [], parts, h => by
    have hp : parts = [] := (Except.ok.inj h).symm
    subst parts
    simp
  | ci :: block, parts, h => by
    rw [checkHeaders] at h
    obtain ⟨part, hpart, h⟩ := check_bind_ok h
    obtain ⟨rest, hrest, h⟩ := check_bind_ok h
    have hout : part :: rest = parts := Except.ok.inj h
    subst parts
    obtain ⟨hci, hchecked⟩ := checkHeader_spec hpart
    obtain ⟨hblock, htail⟩ := checkHeaders_spec block hrest
    refine ⟨by rw [hci, hblock]; rfl, ?_⟩
    intro found hfound
    rcases List.mem_cons.mp hfound with rfl | hfound
    · exact hchecked
    · exact htail found hfound

theorem prepare_spec {mode : CheckMode} {fuel : Nat} {env : Env md}
    {block : List (ConstantInfo md)} {parts : List (Part md)}
    (h : prepare (fueledOps mode fuel) env block = .ok parts) :
    parts ≠ [] ∧
      block = parts.map (fun part => .recInfo part.raw part.majorIndex part.rulePrefix part.rawRules) ∧
      ((provision parts ++ models parts).map (·.name)).Nodup ∧
      (∀ ci ∈ provision parts ++ models parts, env.find? ci.name = none) ∧
      ∀ part ∈ parts, HeaderChecked mode fuel env part := by
  by_cases hnil : block.isEmpty = true
  · simp [prepare, hnil, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h
  · simp only [prepare, hnil, bind, Except.bind] at h
    obtain ⟨found, hheaders, h⟩ := check_bind_ok h
    split at h
    next hdistinct =>
      dsimp only [bind, Except.bind] at h
      split at h
      next hfresh =>
        simp only [bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h
        subst parts
        obtain ⟨hblock, hparts⟩ := checkHeaders_spec block hheaders
        refine ⟨?_, hblock, hdistinct, ?_, hparts⟩
        · intro hempty
          rw [hempty, List.map_nil] at hblock
          exact hnil (by rw [hblock]; rfl)
        · intro ci hci
          exact Option.isNone_iff_eq_none.mp (List.all_eq_true.mp hfresh ci hci)
      next hfresh => cases h
    next hdistinct => cases h

theorem checkRule_spec {mode : CheckMode} {fuel : Nat} {env envSelf : Env md}
    {part : Part md} {raw canonical checked : RecRule md}
    (h : checkRule (fueledOps mode fuel) env envSelf part raw canonical = .ok checked) :
    raw.ctor = canonical.ctor ∧ raw.nfields = canonical.nfields ∧
      raw.rhs.looseBVarsBounded 0 = true ∧ raw.rhs.hasFvar = false ∧
      (runJ mode fuel).annot envSelf 0 raw.rhs checked.rhs ∧
      checked.rhs.allLevelParamsDefined part.canonical.levelParams = true ∧
      checked.rhs.constsResolve envSelf = true ∧ letFree checked.rhs = true ∧
      ruleShape env part canonical = true ∧
      checked = { canonical with
        rhs := checked.rhs
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
  have checkedCtor : checked.ctor = canonical.ctor := congrArg RecRule.ctor hout
  have checkedFields : checked.nfields = canonical.nfields := congrArg RecRule.nfields hout
  have checkedParams : checked.ctorParams = canonical.ctorParams := congrArg RecRule.ctorParams hout
  have checkedFire : checked.fire = canonical.fire := congrArg RecRule.fire hout
  refine ⟨hctor.trans checkedCtor.symm, hfields.trans checkedFields.symm,
    hbounded, hfvar, hann, hlevels, hresolve, hfree, checkedCtor, checkedFields,
    checkedParams, checkedFire, congrArg RecRule.k hout, congrArg RecRule.paramsBlind hout,
    congrArg RecRule.eta hout, ?_, ?_, canonical.rhs, WrapRel.refl _ _, hwrap, .inl rfl⟩
  · intro hfire cv nP nF hfind
    have hfire' : canonical.fire = .plain := checkedFire.symm.trans hfire
    have hfind' : env.find? canonical.ctor = some (.ctorInfo cv nP nF) := by
      simpa only [checkedCtor] using hfind
    rw [checkedParams]
    exact ruleShape_plain hshape hfire' hfind'
  · intro levels pins hfire
    have hfire' : canonical.fire = .nested levels pins := checkedFire.symm.trans hfire
    exact ruleShape_nested hshape hfire'

theorem checkRules_twin {mode : CheckMode} {fuel : Nat} {env envSelf : Env md}
    {part : Part md} (rename : Key md → Key md) :
    ∀ (raws canonicals : List (RecRule md)) {checked : List (RecRule md)},
      checkRules (fueledOps mode fuel) env envSelf part raws canonicals = .ok checked →
      (checked.zip canonicals).all
        (fun (w, c) => wrapRelOk env.find? (c.rhs.renameConsts rename) w.rhs) = true →
      raws.length = checked.length ∧
        Forall₂ (fun (pair : RecRule md × RecRule md) canonical =>
          TwinRuleJ (runJ mode fuel) env envSelf rename part.raw.name part.canonical.levelParams
            part.annotated part.majorIndex part.rulePrefix pair.1 pair.2 canonical)
          (raws.zip checked) canonicals
  | [], [], checked, h, _ => by
    have hout : checked = [] := (Except.ok.inj h).symm
    subst checked
    exact ⟨rfl, .nil⟩
  | [], _ :: _, _, h, _ => by cases h
  | _ :: _, [], _, h, _ => by cases h
  | raw :: raws, canonical :: canonicals, checked, h, hwrap => by
    rw [checkRules] at h
    obtain ⟨first, hfirst, h⟩ := check_bind_ok h
    obtain ⟨rest, hrest, h⟩ := check_bind_ok h
    have hout : first :: rest = checked := Except.ok.inj h
    subst checked
    simp only [List.zip_cons_cons, List.all_cons, Bool.and_eq_true] at hwrap
    obtain ⟨hlen, htail⟩ := checkRules_twin rename raws canonicals hrest hwrap.2
    exact ⟨by simp only [List.length_cons, hlen],
      .cons (checkRule_twin hfirst (wrapRelOk_sound hwrap.1)) htail⟩

def Part.header (part : Part md) : Part md := { part with checkedRules := [] }

structure RulesChecked (mode : CheckMode) (fuel : Nat) (env envSelf : Env md)
    (before after : Part md) : Prop where
  shape : after = { before with checkedRules := after.checkedRules }
  run : checkRules (fueledOps mode fuel) env envSelf before before.rawRules before.canonicalRules =
    .ok after.checkedRules

theorem checkPartsRules_spec {mode : CheckMode} {fuel : Nat} {env envSelf : Env md} :
    ∀ (parts : List (Part md)) {checked : List (Part md)},
      checkPartsRules (fueledOps mode fuel) env envSelf parts = .ok checked →
      Forall₂ (RulesChecked mode fuel env envSelf) parts checked
  | [], checked, h => by
    have hout : checked = [] := (Except.ok.inj h).symm
    subst checked
    exact .nil
  | part :: parts, checked, h => by
    rw [checkPartsRules] at h
    obtain ⟨rules, hrules, h⟩ := check_bind_ok h
    obtain ⟨rest, hrest, h⟩ := check_bind_ok h
    have hout : { part with checkedRules := rules } :: rest = checked := Except.ok.inj h
    subst checked
    exact .cons ⟨rfl, hrules⟩ (checkPartsRules_spec parts hrest)

theorem RulesChecked.headers {mode : CheckMode} {fuel : Nat} {env envSelf : Env md}
    {before after : Part md} (h : RulesChecked mode fuel env envSelf before after) :
    before.header = after.header := by
  simpa only [Part.header] using (congrArg Part.header h.shape).symm

theorem checkedParts_headers {mode : CheckMode} {fuel : Nat} {env envSelf : Env md}
    {parts checked : List (Part md)}
    (h : Forall₂ (RulesChecked mode fuel env envSelf) parts checked) :
    parts.map Part.header = checked.map Part.header := by
  induction h with
  | nil => rfl
  | cons hp _ ih => simp only [List.map_cons, hp.headers, ih]

theorem checkedParts_member {mode : CheckMode} {fuel : Nat} {env envSelf : Env md}
    {parts checked : List (Part md)}
    (h : Forall₂ (RulesChecked mode fuel env envSelf) parts checked) :
    ∀ part ∈ checked, ∃ original ∈ parts, RulesChecked mode fuel env envSelf original part := by
  induction h with
  | nil => intro part hpart; cases hpart
  | @cons original part originals parts hhead htail ih =>
    intro found hfound
    rcases List.mem_cons.mp hfound with rfl | hfound
    · exact ⟨original, List.mem_cons_self, hhead⟩
    · obtain ⟨original', hmem, hrun⟩ := ih found hfound
      exact ⟨original', List.mem_cons_of_mem _ hmem, hrun⟩

theorem models_of_headers {parts checked : List (Part md)}
    (h : parts.map Part.header = checked.map Part.header) : models parts = models checked := by
  have h' := congrArg models h
  simpa only [models, List.filterMap_map, modelInfo?, Part.header, Function.comp_def] using h'

theorem provision_of_headers {parts checked : List (Part md)}
    (h : parts.map Part.header = checked.map Part.header) : provision parts = provision checked := by
  have h' := congrArg provision h
  simpa only [provision, List.map_map, Part.header, Function.comp_def] using h'

theorem declared_of_headers {parts checked : List (Part md)}
    (h : parts.map Part.header = checked.map Part.header) :
    parts.map (fun part => ConstantInfo.recInfo part.raw part.majorIndex part.rulePrefix part.rawRules) =
      checked.map (fun part => ConstantInfo.recInfo part.raw part.majorIndex part.rulePrefix part.rawRules) := by
  have h' := congrArg (List.map fun part =>
    ConstantInfo.recInfo part.raw part.majorIndex part.rulePrefix part.rawRules) h
  simpa only [List.map_map, Part.header, Function.comp_def] using h'

theorem CanonicalPart.of_headers {env : Env md} {before after : Part md}
    (h : before.header = after.header) (source : CanonicalPart env before) : CanonicalPart env after := by
  have hraw : before.raw = after.raw := congrArg Part.raw h
  have hannotated : before.annotated = after.annotated := congrArg Part.annotated h
  have hcanonical : before.canonical = after.canonical := congrArg Part.canonical h
  have hkey : before.canonicalKey = after.canonicalKey := congrArg Part.canonicalKey h
  have hmajor : before.majorIndex = after.majorIndex := congrArg Part.majorIndex h
  have hprefix : before.rulePrefix = after.rulePrefix := congrArg Part.rulePrefix h
  have hrawRules : before.rawRules = after.rawRules := congrArg Part.rawRules h
  have hcanonicalRules : before.canonicalRules = after.canonicalRules := congrArg Part.canonicalRules h
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [← hkey, ← hcanonical, ← hmajor, ← hprefix, ← hcanonicalRules]
    exact source.stored
  · rw [← hraw, ← hcanonical]
    exact source.levels
  · rw [← hrawRules, ← hcanonicalRules]
    exact source.ruleCount
  · rw [← hcanonical, ← hannotated]
    exact source.typeWrap
  · have hm : ModelSource env before.header := source.model
    rw [h] at hm
    exact hm

theorem HeaderChecked.of_headers {mode : CheckMode} {fuel : Nat} {env : Env md}
    {before after : Part md} (h : before.header = after.header)
    (checked : HeaderChecked mode fuel env before) : HeaderChecked mode fuel env after := by
  obtain ⟨hcv, hfree, hsource⟩ := checked
  have hraw : before.raw = after.raw := congrArg Part.raw h
  have hannotated : before.annotated = after.annotated := congrArg Part.annotated h
  refine ⟨?_, ?_, hsource.of_headers h⟩
  · rwa [← hraw, ← hannotated]
  · rwa [← hannotated]

theorem checkRule_header (ops : CheckerOps md (CheckM md)) (env envSelf : Env md)
    (part : Part md) (raw canonical : RecRule md) :
    checkRule ops env envSelf part.header raw canonical = checkRule ops env envSelf part raw canonical := rfl

theorem checkRules_header (ops : CheckerOps md (CheckM md)) (env envSelf : Env md)
    (part : Part md) : ∀ raws canonicals,
    checkRules ops env envSelf part.header raws canonicals = checkRules ops env envSelf part raws canonicals
  | [], [] => rfl
  | [], _ :: _ => rfl
  | _ :: _, [] => rfl
  | _ :: raws, _ :: canonicals => by
    simp only [checkRules, checkRule_header, checkRules_header ops env envSelf part raws canonicals]

theorem RulesChecked.run_after {mode : CheckMode} {fuel : Nat} {env envSelf : Env md}
    {before after : Part md} (h : RulesChecked mode fuel env envSelf before after) :
    checkRules (fueledOps mode fuel) env envSelf after after.rawRules after.canonicalRules =
      .ok after.checkedRules := by
  have hraw : before.rawRules = after.rawRules := congrArg Part.rawRules h.headers
  have hcanonical : before.canonicalRules = after.canonicalRules := congrArg Part.canonicalRules h.headers
  calc
    checkRules (fueledOps mode fuel) env envSelf after after.rawRules after.canonicalRules =
        checkRules (fueledOps mode fuel) env envSelf after.header after.rawRules after.canonicalRules :=
      (checkRules_header _ _ _ _ _ _).symm
    _ = checkRules (fueledOps mode fuel) env envSelf before.header before.rawRules before.canonicalRules := by
      rw [h.headers, hraw, hcanonical]
    _ = checkRules (fueledOps mode fuel) env envSelf before before.rawRules before.canonicalRules :=
      checkRules_header _ _ _ _ _ _
    _ = .ok after.checkedRules := h.run

/-- A successful pure twin check supplies the existing semantic declaration certificate.
Every header and rule judgement comes from its actual checking phase. -/
theorem check_semantic {mode : CheckMode} {fuel : Nat} {env output : Env md}
    {block : List (ConstantInfo md)}
    (h : check (fueledOps mode fuel) env block = .ok output) :
    DeclRecTwinRunJ (runJ mode fuel) env block output := by
  rw [check] at h
  obtain ⟨parts, hprepare, h⟩ := check_bind_ok h
  obtain ⟨checked, hchecked, hfinish⟩ := check_bind_ok h
  obtain ⟨hne, hblock, hdistinct, hfresh, hheaders⟩ := prepare_spec hprepare
  have hparts := checkPartsRules_spec parts hchecked
  have heq := checkedParts_headers hparts
  have hmodels := models_of_headers heq
  have hprovision := provision_of_headers heq
  obtain ⟨rename, hrename, hwrap, houtput⟩ := finish_spec hfinish
  have hnonempty : checked ≠ [] := by
    intro hempty
    have hpartsEmpty : parts.map Part.header = [] := by rw [heq, hempty]; rfl
    exact hne (List.map_eq_nil_iff.mp hpartsEmpty)
  have hnames : ((recursors checked ++ models checked).map (·.name)) =
      ((provision parts ++ models parts).map (·.name)) := by
    have hrec : (recursors checked).map (·.name) = (provision checked).map (·.name) := by
      simp only [recursors, provision, List.map_map]
      rfl
    rw [List.map_append, List.map_append, hrec, ← hprovision, ← hmodels]
  have hself : selfEnv env parts =
      ⟨twinProv (checked.map Part.semantic) ++ (twinModels (checked.map Part.semantic) ++ env.consts)⟩ := by
    simp only [selfEnv, semantic_provision, semantic_models, hmodels, hprovision, List.append_assoc]
  refine ⟨checked.map Part.semantic, rename, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro hempty
    exact hnonempty (List.map_eq_nil_iff.mp hempty)
  · simpa only [List.map_map, Part.semantic, Function.comp_def] using
      hblock.trans (declared_of_headers heq)
  · simpa only [semantic_recursors, semantic_models, List.append_assoc] using houtput
  · simp only [semantic_recursors, semantic_models, hnames]
    exact hdistinct
  · intro ci hci
    simp only [semantic_recursors, semantic_models] at hci
    have hname : ci.name ∈ (recursors checked ++ models checked).map (·.name) :=
      List.mem_map.mpr ⟨ci, hci, rfl⟩
    rw [hnames] at hname
    obtain ⟨original, hmem, hname⟩ := List.mem_map.mp hname
    rw [← hname]
    exact hfresh original hmem
  · intro key
    rcases hrename key with fixed | ⟨part, hpart, hkey, hrenamed⟩
    · exact .inl fixed
    · exact .inr ⟨part.semantic, List.mem_map.mpr ⟨part, hpart, rfl⟩, hkey, hrenamed⟩
  · intro semantic hsemantic
    obtain ⟨part, hpart, rfl⟩ := List.mem_map.mp hsemantic
    obtain ⟨original, horiginal, hrun⟩ := checkedParts_member hparts part hpart
    obtain ⟨hheader, hfree, hcanonical⟩ :=
      HeaderChecked.of_headers hrun.headers (hheaders original horiginal)
    have hrules := checkRules_twin rename part.rawRules part.canonicalRules hrun.run_after
      (List.all_eq_true.mp hwrap part hpart)
    refine ⟨hheader, hfree, hcanonical.stored, hcanonical.levels, hcanonical.model,
      ⟨part.canonical.type, WrapRel.refl _ _, hcanonical.typeWrap, .inl rfl⟩, hrules.1, ?_⟩
    simpa only [hself, Part.semantic] using hrules.2

end Ix.Kernel.NativeTwin
