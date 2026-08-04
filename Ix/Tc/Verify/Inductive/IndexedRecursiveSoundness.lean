import Ix.Tc.Verify.Inductive.IndexedRecursivePattern

/-!
# Indexed recursive iota soundness

This module opens the two generated `IndexedVec.rec` equations selected by
the E2a certificate and relates them to the dependent patterns consumed by
production WHNF.  All equation shapes below reduce from the retained
`GenerationChecked.rule`; no independently supplied rewrite law is used.
-/

namespace Ix.Tc.IndexedRecursivePattern

open Lean4Lean
open Lean4Lean.InductiveFixtures
open Lean4Lean.InductiveReplayFixtures
open IndexedRecursiveCertificateFixture

private abbrev generation := transaction.certificate.generation
private abbrev nilNormalized := generation.block.ctorPairs[0]
private abbrev consNormalized := generation.block.ctorPairs[1]
private abbrev nilLegacyRule :=
  VInductDecl.ruleRec 1 ``IndexedVec 1 indexedVecType 0
    indexedVecType.ctors[0]
private abbrev consLegacyRule :=
  VInductDecl.ruleRec 1 ``IndexedVec 1 indexedVecType 1
    indexedVecType.ctors[1]

@[simp] private theorem generationElimination :
    generation.elimination = .large :=
  IndexedRecursiveCertificateFixture.breadth.largeElimination

@[simp] private theorem checkedElimination :
    indexedVecChecked.elimination = .large :=
  IndexedRecursiveCertificateFixture.breadth.largeElimination

private theorem checkedType : indexedVecChecked.type = indexedVecType := by
  have h := indexedVecChecked.types_eq
  simpa [indexedVecDecl] using h.symm

private theorem checkedIndicesLength : indexedVecChecked.indices.length = 1 := rfl

@[simp] private theorem generationRecursorName :
    (.str generation.block.sourceType.name "rec") = ``IndexedVec.rec := rfl

@[simp] private theorem nilNormalizedName :
    nilNormalized.raw.name = ``IndexedVec.nil := rfl

@[simp] private theorem consNormalizedName :
    consNormalized.raw.name = ``IndexedVec.cons := rfl

private theorem consNormalizedRaw :
    consNormalized.raw = indexedVecType.ctors[1] := rfl

private theorem nilRule_eq_legacy :
    generation.rule 0 nilNormalized = nilLegacyRule := by
  have hlegacy :=
    VInductDecl.Checked.generatedRules_eq_legacy indexedVecChecked
  rw [checkedElimination] at hlegacy
  change generation.generatedRules =
    VInductDecl.rulesRec 1 ``IndexedVec 1 indexedVecType at hlegacy
  have hat := congrArg (fun rules : List VDefEq => rules[0]?) hlegacy
  rw [CertifiedSingletonGeneration.generatedRuleAt generation (by rfl)] at hat
  simpa [generation, nilNormalized, transaction_generation,
    indexedVecChecked.constructors_eq, indexedVecChecked.indices_eq,
    checkedType, checkedIndicesLength,
    indexedVecDecl, indexedVecType,
    VInductDecl.Checked.identityGeneration,
    VInductDecl.Checked.identityBlock,
    VInductDecl.NormalizedChecked.ctorPairs,
    VInductDecl.pairNormalizedCtors,
    VInductDecl.Checked.generatedRules, VInductDecl.rulesRec,
    nilLegacyRule] using Option.some.inj hat

private theorem consRule_eq_legacy :
    generation.rule 1 consNormalized = consLegacyRule := by
  have hlegacy :=
    VInductDecl.Checked.generatedRules_eq_legacy indexedVecChecked
  rw [checkedElimination] at hlegacy
  change generation.generatedRules =
    VInductDecl.rulesRec 1 ``IndexedVec 1 indexedVecType at hlegacy
  have hat := congrArg (fun rules : List VDefEq => rules[1]?) hlegacy
  rw [CertifiedSingletonGeneration.generatedRuleAt generation (by rfl)] at hat
  simpa [generation, consNormalized, transaction_generation,
    indexedVecChecked.constructors_eq, indexedVecChecked.indices_eq,
    checkedType, checkedIndicesLength,
    indexedVecDecl, indexedVecType,
    VInductDecl.Checked.identityGeneration,
    VInductDecl.Checked.identityBlock,
    VInductDecl.NormalizedChecked.ctorPairs,
    VInductDecl.pairNormalizedCtors,
    VInductDecl.Checked.generatedRules, VInductDecl.rulesRec,
    consLegacyRule] using Option.some.inj hat

/-- Parameter, motive, and both minors: the prefix shared by the recursor and
each generated equation before constructor fields are introduced. -/
private def commonBinders : List VExpr :=
  generation.paramsTel ++ generation.motiveType :: generation.minorTypes

private def ruleBinders (ctor : VInductDecl.NormalizedCtor) : List VExpr :=
  commonBinders ++
    VExpr.liftTelN (generation.block.ctorPairs.length + 1)
      (ctor.fieldsR indexedVecDecl.uvars indexedVecDecl.nparams) 0

private def ruleRecBase (ctor : VInductDecl.NormalizedCtor) : VExpr :=
  VExpr.appN
    (.const (.str generation.block.sourceType.name "rec")
      (VLevel.params (indexedVecDecl.uvars + 1)))
    (VExpr.bvarRevRange
      (ctor.fieldsR indexedVecDecl.uvars indexedVecDecl.nparams).length
      (indexedVecDecl.nparams + generation.block.ctorPairs.length + 1))

private def ruleIndices (ctor : VInductDecl.NormalizedCtor) : List VExpr :=
  ctor.resultIndicesR indexedVecDecl.uvars |>.map fun expression =>
    expression.liftN (generation.block.ctorPairs.length + 1)
      (ctor.fieldsR indexedVecDecl.uvars indexedVecDecl.nparams).length

private def ruleConstructorApp
    (ctor : VInductDecl.NormalizedCtor) : VExpr :=
  let fieldCount :=
    (ctor.fieldsR indexedVecDecl.uvars indexedVecDecl.nparams).length
  VExpr.appN
    (.const ctor.raw.name (VLevel.params' indexedVecDecl.uvars 1))
    (VExpr.bvarRevRange
        (fieldCount + generation.block.ctorPairs.length + 1)
        indexedVecDecl.nparams ++
      VExpr.bvarRevRange 0 fieldCount)

private def ruleCalls (ctor : VInductDecl.NormalizedCtor) : List VExpr :=
  let fieldCount :=
    (ctor.fieldsR indexedVecDecl.uvars indexedVecDecl.nparams).length
  ctor.recArgsR indexedVecDecl.uvars |>.map fun recursive =>
    recursive.ruleCall fieldCount generation.block.ctorPairs.length
      (ruleRecBase ctor)

private def ruleLhsBody (ctor : VInductDecl.NormalizedCtor) : VExpr :=
  VExpr.appN (ruleRecBase ctor)
    (ruleIndices ctor ++ [ruleConstructorApp ctor])

private def ruleRhsBody
    (index : Nat) (ctor : VInductDecl.NormalizedCtor) : VExpr :=
  let fieldCount :=
    (ctor.fieldsR indexedVecDecl.uvars indexedVecDecl.nparams).length
  VExpr.appN
    (.bvar (generation.block.ctorPairs.length - 1 - index + fieldCount))
    (VExpr.bvarRevRange 0 fieldCount ++ ruleCalls ctor)

private def ruleTypeBody (ctor : VInductDecl.NormalizedCtor) : VExpr :=
  let fieldCount :=
    (ctor.fieldsR indexedVecDecl.uvars indexedVecDecl.nparams).length
  VExpr.appN (.bvar (generation.block.ctorPairs.length + fieldCount))
    (ruleIndices ctor ++ [ruleConstructorApp ctor])

/-- Strip an exact number of leading lambda binders.  This is used only to
recover the body of a generated equation after the public legacy-equivalence
theorem has identified the complete closed rule. -/
private def dropLams : Nat → VExpr → VExpr
  | 0, expression => expression
  | count + 1, .lam _ body => dropLams count body
  | _ + 1, expression => expression

@[simp] private theorem dropLams_lamN (binders : List VExpr) (body : VExpr) :
    dropLams binders.length (VExpr.lamN binders body) = body := by
  induction binders with
  | nil => rfl
  | cons binder binders ih => simpa [dropLams, VExpr.lamN] using ih

@[simp] private theorem instRev_app (function argument : VExpr)
    (arguments : List VExpr) :
    VExpr.instRev (.app function argument) arguments =
      .app (VExpr.instRev function arguments)
        (VExpr.instRev argument arguments) := by
  simpa [VExpr.appN] using
    VExpr.instRev_appN arguments function [argument]

@[simp] private theorem instRev_const (name : Lean.Name)
    (levels : List VLevel) (arguments : List VExpr) :
    VExpr.instRev (.const name levels) arguments = .const name levels :=
  VExpr.instRev_closedN arguments trivial

/-- Exact de Bruijn body of the null equation retained by the generator. -/
private def nilLhsConcreteBody : VExpr :=
  .app
    (VExpr.appN (.const ``IndexedVec.rec (VLevel.params 2))
      [.bvar 3, .bvar 2, .bvar 1, .bvar 0, .const ``Nat.zero []])
    (.app (.const ``IndexedVec.nil [.param 1]) (.bvar 3))

private def nilRhsConcreteBody : VExpr := .bvar 1

/-- Exact de Bruijn bodies of the recursive successor equation. -/
private def consLhsConcreteBody : VExpr :=
  .app
    (VExpr.appN (.const ``IndexedVec.rec (VLevel.params 2))
      [.bvar 6, .bvar 5, .bvar 4, .bvar 3,
        .app (.const ``Nat.succ []) (.bvar 2)])
    (VExpr.appN (.const ``IndexedVec.cons [.param 1])
      [.bvar 6, .bvar 2, .bvar 1, .bvar 0])

private def consRhsConcreteBody : VExpr :=
  VExpr.appN (.bvar 3)
    [.bvar 2, .bvar 1, .bvar 0,
      VExpr.appN (.const ``IndexedVec.rec (VLevel.params 2))
        [.bvar 6, .bvar 5, .bvar 4, .bvar 3, .bvar 2, .bvar 0]]

@[simp] private theorem commonBinders_length : commonBinders.length = 4 := rfl

@[simp] private theorem nilRuleBinders : ruleBinders nilNormalized =
    commonBinders := rfl

@[simp] private theorem consRuleBinders_length :
    (ruleBinders consNormalized).length = 7 := rfl

/-- Direct exposure of the exact retained generator definition. -/
private theorem generatedRule_shape
    (index : Nat) (ctor : VInductDecl.NormalizedCtor) :
    (generation.rule index ctor).lhs =
        VExpr.lamN (ruleBinders ctor) (ruleLhsBody ctor) ∧
      (generation.rule index ctor).rhs =
        VExpr.lamN (ruleBinders ctor) (ruleRhsBody index ctor) ∧
      (generation.rule index ctor).type =
        VExpr.forallN (ruleBinders ctor) (ruleTypeBody ctor) := by
  simp [VInductDecl.GenerationChecked.rule, ruleBinders, commonBinders,
    ruleLhsBody, ruleRhsBody, ruleTypeBody, ruleRecBase, ruleIndices,
    ruleConstructorApp, ruleCalls, List.append_assoc]

private theorem nilLhsBody_eq :
    ruleLhsBody nilNormalized = nilLhsConcreteBody := by
  have hclosed :
      VExpr.lamN (ruleBinders nilNormalized) (ruleLhsBody nilNormalized) =
        nilLegacyRule.lhs :=
    (generatedRule_shape 0 nilNormalized).1.symm.trans
      (congrArg VDefEq.lhs nilRule_eq_legacy)
  have hbody := congrArg (dropLams 4) hclosed
  have hlength : (ruleBinders nilNormalized).length = 4 := by simp
  have hleft :
      dropLams 4
          (VExpr.lamN (ruleBinders nilNormalized)
            (ruleLhsBody nilNormalized)) =
        ruleLhsBody nilNormalized := by
    rw [← hlength]
    exact dropLams_lamN _ _
  rw [hleft] at hbody
  have hright : dropLams 4 nilLegacyRule.lhs = nilLhsConcreteBody := by
    rfl
  exact hbody.trans hright

private theorem nilRhsBody_eq :
    ruleRhsBody 0 nilNormalized = nilRhsConcreteBody := by
  have hclosed :
      VExpr.lamN (ruleBinders nilNormalized)
          (ruleRhsBody 0 nilNormalized) = nilLegacyRule.rhs :=
    (generatedRule_shape 0 nilNormalized).2.1.symm.trans
      (congrArg VDefEq.rhs nilRule_eq_legacy)
  have hbody := congrArg (dropLams 4) hclosed
  have hlength : (ruleBinders nilNormalized).length = 4 := by simp
  have hleft :
      dropLams 4
          (VExpr.lamN (ruleBinders nilNormalized)
            (ruleRhsBody 0 nilNormalized)) =
        ruleRhsBody 0 nilNormalized := by
    rw [← hlength]
    exact dropLams_lamN _ _
  rw [hleft] at hbody
  have hright : dropLams 4 nilLegacyRule.rhs = nilRhsConcreteBody := by
    rfl
  exact hbody.trans hright

private theorem consLhsBody_eq :
    ruleLhsBody consNormalized = consLhsConcreteBody := by
  have hclosed :
      VExpr.lamN (ruleBinders consNormalized)
          (ruleLhsBody consNormalized) = consLegacyRule.lhs :=
    (generatedRule_shape 1 consNormalized).1.symm.trans
      (congrArg VDefEq.lhs consRule_eq_legacy)
  have hbody := congrArg (dropLams 7) hclosed
  have hlength : (ruleBinders consNormalized).length = 7 := by simp
  have hleft :
      dropLams 7
          (VExpr.lamN (ruleBinders consNormalized)
            (ruleLhsBody consNormalized)) =
        ruleLhsBody consNormalized := by
    rw [← hlength]
    exact dropLams_lamN _ _
  rw [hleft] at hbody
  have hright : dropLams 7 consLegacyRule.lhs = consLhsConcreteBody := by
    rfl
  exact hbody.trans hright

private theorem consRhsBody_eq :
    ruleRhsBody 1 consNormalized = consRhsConcreteBody := by
  have hclosed :
      VExpr.lamN (ruleBinders consNormalized)
          (ruleRhsBody 1 consNormalized) = consLegacyRule.rhs :=
    (generatedRule_shape 1 consNormalized).2.1.symm.trans
      (congrArg VDefEq.rhs consRule_eq_legacy)
  have hbody := congrArg (dropLams 7) hclosed
  have hlength : (ruleBinders consNormalized).length = 7 := by simp
  have hleft :
      dropLams 7
          (VExpr.lamN (ruleBinders consNormalized)
            (ruleRhsBody 1 consNormalized)) =
        ruleRhsBody 1 consNormalized := by
    rw [← hlength]
    exact dropLams_lamN _ _
  rw [hleft] at hbody
  have hright : dropLams 7 consLegacyRule.rhs = consRhsConcreteBody := by
    rfl
  exact hbody.trans hright

/-- The recursor and either rule expose the same four-binder prefix after
universe instantiation. -/
private theorem recType_common (levels : List VLevel) :
    generation.recType.instL levels =
      VExpr.forallN (commonBinders.map (VExpr.instL levels))
        (VExpr.dropN 4 (generation.recType.instL levels)) := by
  rw [← VExpr.forallN_telN_dropN 4 (generation.recType.instL levels)]
  congr 1

private theorem ruleType_common (index : Nat)
    (ctor : VInductDecl.NormalizedCtor) (levels : List VLevel) :
    (generation.rule index ctor).type.instL levels =
      VExpr.forallN (commonBinders.map (VExpr.instL levels))
        (VExpr.dropN 4 ((generation.rule index ctor).type.instL levels)) := by
  rw [← VExpr.forallN_telN_dropN 4
    ((generation.rule index ctor).type.instL levels)]
  congr 1

/-- Opening the null rule produces its canonical indexed redex. -/
private theorem nilLhsBody_open
    (v u : VLevel) (alpha motive nilMinor consMinor : VExpr) :
    VExpr.instRev ((ruleLhsBody nilNormalized).instL [v, u])
        [alpha, motive, nilMinor, consMinor] =
      .app
        (VExpr.appN (.const ``IndexedVec.rec [v, u])
          [alpha, motive, nilMinor, consMinor, .const ``Nat.zero []])
        (.app (.const ``IndexedVec.nil [u]) alpha) := by
  rw [nilLhsBody_eq]
  let arguments := [alpha, motive, nilMinor, consMinor]
  have halpha : VExpr.instRev (.bvar 3) arguments = alpha := by
    simpa [arguments] using VExpr.instRev_bvar_at arguments 0 (by simp [arguments])
  have hmotive : VExpr.instRev (.bvar 2) arguments = motive := by
    simpa [arguments] using VExpr.instRev_bvar_at arguments 1 (by simp [arguments])
  have hnil : VExpr.instRev (.bvar 1) arguments = nilMinor := by
    simpa [arguments] using VExpr.instRev_bvar_at arguments 2 (by simp [arguments])
  have hcons : VExpr.instRev (.bvar 0) arguments = consMinor := by
    simpa [arguments] using VExpr.instRev_bvar_at arguments 3 (by simp [arguments])
  change VExpr.instRev (nilLhsConcreteBody.instL [v, u]) arguments = _
  simp [nilLhsConcreteBody, VExpr.instL_appN, VExpr.instRev_appN,
    VExpr.instL, VLevel.inst_map_id, VLevel.inst,
    halpha, hmotive, hnil, hcons]

/-- Opening the null RHS selects the null minor. -/
private theorem nilRhsBody_open
    (v u : VLevel) (alpha motive nilMinor consMinor : VExpr) :
    VExpr.instRev ((ruleRhsBody 0 nilNormalized).instL [v, u])
        [alpha, motive, nilMinor, consMinor] = nilMinor := by
  rw [nilRhsBody_eq]
  let arguments := [alpha, motive, nilMinor, consMinor]
  have hnil : VExpr.instRev (.bvar 1) arguments = nilMinor := by
    simpa [arguments] using VExpr.instRev_bvar_at arguments 2 (by simp [arguments])
  change VExpr.instRev (nilRhsConcreteBody.instL [v, u]) arguments = _
  simpa [nilRhsConcreteBody, VExpr.instL] using hnil

/-- Opening the recursive rule produces the successor-indexed constructor
redex selected by the generated equation. -/
private theorem consLhsBody_open
    (v u : VLevel)
    (alpha motive nilMinor consMinor n a as : VExpr) :
    VExpr.instRev ((ruleLhsBody consNormalized).instL [v, u])
        [alpha, motive, nilMinor, consMinor, n, a, as] =
      .app
        (VExpr.appN (.const ``IndexedVec.rec [v, u])
          [alpha, motive, nilMinor, consMinor,
            .app (.const ``Nat.succ []) n])
        (VExpr.appN (.const ``IndexedVec.cons [u]) [alpha, n, a, as]) := by
  rw [consLhsBody_eq]
  let arguments := [alpha, motive, nilMinor, consMinor, n, a, as]
  have halpha : VExpr.instRev (.bvar 6) arguments = alpha := by
    simpa [arguments] using VExpr.instRev_bvar_at arguments 0 (by simp [arguments])
  have hmotive : VExpr.instRev (.bvar 5) arguments = motive := by
    simpa [arguments] using VExpr.instRev_bvar_at arguments 1 (by simp [arguments])
  have hnil : VExpr.instRev (.bvar 4) arguments = nilMinor := by
    simpa [arguments] using VExpr.instRev_bvar_at arguments 2 (by simp [arguments])
  have hcons : VExpr.instRev (.bvar 3) arguments = consMinor := by
    simpa [arguments] using VExpr.instRev_bvar_at arguments 3 (by simp [arguments])
  have hn : VExpr.instRev (.bvar 2) arguments = n := by
    simpa [arguments] using VExpr.instRev_bvar_at arguments 4 (by simp [arguments])
  have ha : VExpr.instRev (.bvar 1) arguments = a := by
    simpa [arguments] using VExpr.instRev_bvar_at arguments 5 (by simp [arguments])
  have has : VExpr.instRev (.bvar 0) arguments = as := by
    simpa [arguments] using VExpr.instRev_bvar_at arguments 6 (by simp [arguments])
  change VExpr.instRev (consLhsConcreteBody.instL [v, u]) arguments = _
  simp [consLhsConcreteBody, VExpr.instL_appN, VExpr.instRev_appN,
    VExpr.instL, VLevel.inst_map_id, VLevel.inst,
    halpha, hmotive, hnil, hcons, hn, ha, has]

/-- Opening the recursive RHS selects the recursive minor and constructs the
recursive call at the predecessor index. -/
private theorem consRhsBody_open
    (v u : VLevel)
    (alpha motive nilMinor consMinor n a as : VExpr) :
    VExpr.instRev ((ruleRhsBody 1 consNormalized).instL [v, u])
        [alpha, motive, nilMinor, consMinor, n, a, as] =
      VExpr.appN consMinor
        [n, a, as,
          VExpr.appN (.const ``IndexedVec.rec [v, u])
            [alpha, motive, nilMinor, consMinor, n, as]] := by
  rw [consRhsBody_eq]
  let arguments := [alpha, motive, nilMinor, consMinor, n, a, as]
  have halpha : VExpr.instRev (.bvar 6) arguments = alpha := by
    simpa [arguments] using VExpr.instRev_bvar_at arguments 0 (by simp [arguments])
  have hmotive : VExpr.instRev (.bvar 5) arguments = motive := by
    simpa [arguments] using VExpr.instRev_bvar_at arguments 1 (by simp [arguments])
  have hnil : VExpr.instRev (.bvar 4) arguments = nilMinor := by
    simpa [arguments] using VExpr.instRev_bvar_at arguments 2 (by simp [arguments])
  have hcons : VExpr.instRev (.bvar 3) arguments = consMinor := by
    simpa [arguments] using VExpr.instRev_bvar_at arguments 3 (by simp [arguments])
  have hn : VExpr.instRev (.bvar 2) arguments = n := by
    simpa [arguments] using VExpr.instRev_bvar_at arguments 4 (by simp [arguments])
  have ha : VExpr.instRev (.bvar 1) arguments = a := by
    simpa [arguments] using VExpr.instRev_bvar_at arguments 5 (by simp [arguments])
  have has : VExpr.instRev (.bvar 0) arguments = as := by
    simpa [arguments] using VExpr.instRev_bvar_at arguments 6 (by simp [arguments])
  change VExpr.instRev (consRhsConcreteBody.instL [v, u]) arguments = _
  simp [consRhsConcreteBody, VExpr.instL_appN, VExpr.instRev_appN,
    VExpr.instL, VLevel.inst_map_id,
    halpha, hmotive, hnil, hcons, hn, ha, has]

private theorem recType_parameter (v u : VLevel) :
    generation.recType.instL [v, u] =
      .forallE (.sort (.succ u))
        (VExpr.dropN 1 (generation.recType.instL [v, u])) := by
  rw [← VExpr.forallN_telN_dropN 1 (generation.recType.instL [v, u])]
  congr 1

private theorem nilConstructorType_parameter (u : VLevel) :
    nilNormalized.raw.toVConstant.type.instL [u] =
      .forallE (.sort (.succ u))
        (VExpr.dropN 1 (nilNormalized.raw.toVConstant.type.instL [u])) := by
  rw [← VExpr.forallN_telN_dropN 1
    (nilNormalized.raw.toVConstant.type.instL [u])]
  congr 1

private theorem consConstructorType_parameter (u : VLevel) :
    consNormalized.raw.toVConstant.type.instL [u] =
      .forallE (.sort (.succ u))
        (VExpr.dropN 1 (consNormalized.raw.toVConstant.type.instL [u])) := by
  rw [← VExpr.forallN_telN_dropN 1
    (consNormalized.raw.toVConstant.type.instL [u])]
  congr 1

private def consEquationFieldType (v u : VLevel)
    (alpha motive nilMinor consMinor : VExpr) : VExpr :=
  VExpr.instRev
    (VExpr.dropN 4
      ((generation.rule 1 consNormalized).type.instL [v, u]))
    [alpha, motive, nilMinor, consMinor]

private def consConstructorFieldType (u : VLevel) (alpha : VExpr) : VExpr :=
  VExpr.instRev
    (VExpr.dropN 1 (consNormalized.raw.toVConstant.type.instL [u]))
    [alpha]

/-- Removing the last variable introduced by a block lift lowers that block
lift by one.  This is the substitution shape produced when the common
recursor arguments are instantiated beneath constructor fields. -/
private theorem inst_liftN_at_end (expression argument : VExpr) (count : Nat) :
    (VExpr.liftN (count + 1) expression).inst argument count =
      VExpr.liftN count expression := by
  rw [← VExpr.liftN'_liftN'
    (e := expression) (n1 := count) (n2 := 1) (k1 := 0) (k2 := count)
    (by omega) (by omega)]
  exact VExpr.inst_liftN (VExpr.liftN count expression) argument

/-- After the common parameter/motive/minor prefix is supplied, the
generated recursive equation and the constructor expose the same three
dependent field binders. -/
private theorem consFieldBinders_eq (v u : VLevel)
    (alpha motive nilMinor consMinor : VExpr) :
    VExpr.telN 3
        (consEquationFieldType v u alpha motive nilMinor consMinor) =
      VExpr.telN 3 (consConstructorFieldType u alpha) := by
  unfold consEquationFieldType consConstructorFieldType
  rw [consRule_eq_legacy]
  rw [consNormalizedRaw]
  simp [consLegacyRule, VInductDecl.ruleRec,
    VInductDecl.paramsTel, VInductDecl.motiveType,
    VInductDecl.minorTypesRec, VInductDecl.minorTypeRec,
    VInductDecl.ctorFieldsR, VInductDecl.idxTel,
    VInductDecl.ctorFields, indexedVecType,
    VExpr.instRev, VExpr.instL_forallN,
    VExpr.forallN, VExpr.telN, VExpr.dropN, VExpr.liftTelN, VExpr.liftN,
    VExpr.instL, VExpr.inst, VExpr.instVar,
    inst_liftN_at_end,
    VLevel.params', VLevel.params, VLevel.inst]

/-- The null indexed pattern is justified by generated rule zero, including
its uniform-parameter and zero-index checks. -/
theorem nilPatternSound
    {trProj : RawProjRel} {catalog : Catalog}
    {nameOf : Address → Option Lean.Name} {trusted : KId .anon → Prop}
    {family : SingletonFamilyCatalogLink trProj catalog nameOf trusted
      transaction}
    (link : SingletonRecursorCatalogLink trProj catalog nameOf trusted
      transaction family)
    {rule : RecRule .anon}
    (hrule : link.recursorConcrete.RecursorRuleAt 0 rule)
    (constructorId : KId .anon) :
    (nilPattern constructorId).Sound indexedVecFinalEnv := by
  unfold RecursorRulePattern.Sound
  simp [nilPattern, recursorName]
  intro future hfuture hfutureWF uvars Gamma matched levels captures A
    hGamma hmatches htype hchecks
  change Pattern.Matches
      (RecursorIotaPattern ``IndexedVec.rec 5 ``IndexedVec.nil 1)
      matched levels captures at hmatches
  obtain ⟨recursorArguments, constructorLevels, constructorArguments,
    hrecursorLength, hconstructorLength, hmatched, hrecCaptures,
    hconstructorCaptures⟩ :=
    RecursorIotaPattern.matches_spines_full hmatches
  rcases recursorArguments with _ | ⟨alpha, rec1⟩
  · simp at hrecursorLength
  rcases rec1 with _ | ⟨motive, rec2⟩
  · simp at hrecursorLength
  rcases rec2 with _ | ⟨nilMinor, rec3⟩
  · simp at hrecursorLength
  rcases rec3 with _ | ⟨consMinor, rec4⟩
  · simp at hrecursorLength
  rcases rec4 with _ | ⟨index, recTail⟩
  · simp at hrecursorLength
  have hrecTail : recTail = [] :=
    List.eq_nil_of_length_eq_zero (by simpa using hrecursorLength)
  subst recTail
  rcases constructorArguments with _ | ⟨constructorAlpha, ctorTail⟩
  · simp at hconstructorLength
  have hctorTail : ctorTail = [] :=
    List.eq_nil_of_length_eq_zero (by simpa using hconstructorLength)
  subst ctorTail

  have hcapAlpha := hrecCaptures ⟨0, by omega⟩
  have hcapMotive := hrecCaptures ⟨1, by omega⟩
  have hcapNil := hrecCaptures ⟨2, by omega⟩
  have hcapCons := hrecCaptures ⟨3, by omega⟩
  have hcapIndex := hrecCaptures ⟨4, by omega⟩
  have hcapConstructorAlpha := hconstructorCaptures ⟨0, by omega⟩
  simp at hcapAlpha hcapMotive hcapNil hcapCons hcapIndex hcapConstructorAlpha
  have hchecks' : nilChecks.OK (future.IsDefEqU uvars Gamma)
      levels captures := by simpa [nilPattern] using hchecks
  obtain ⟨hparameter, hindex⟩ :=
    nilChecks_ok (future.IsDefEqU uvars Gamma) levels captures hchecks'
  have hparameter' : future.IsDefEqU uvars Gamma alpha constructorAlpha := by
    rw [hcapAlpha, hcapConstructorAlpha]
    simpa [nilPattern] using hparameter
  have hindex' : future.IsDefEqU uvars Gamma index
      (.const ``Nat.zero []) := by
    rw [hcapIndex]
    simpa [nilPattern] using hindex

  rw [hmatched] at htype
  obtain ⟨majorDomain, majorBody, hrecursorApplied,
    hconstructorApplied⟩ := htype.app_inv hfutureWF.ordered hGamma

  obtain ⟨recursorHeadType, hrecursorHeadTyped⟩ :=
    Lean4Lean.VEnv.HasType.appN_head hfutureWF hGamma hrecursorApplied
  obtain ⟨recursorConstant, hrecursorLookup, hlevelsWF, hlevelsArity⟩ :=
    hrecursorHeadTyped.const_inv hfutureWF.ordered hGamma
  have hcertifiedRecursorLookup :=
    hfuture.constants transaction.facts.recursorLookup
  have hrecursorConstant : recursorConstant = generation.recursor :=
    Option.some.inj (hrecursorLookup.symm.trans hcertifiedRecursorLookup)
  subst recursorConstant
  have hlevelsLength : levels.length = 2 := by
    calc
      levels.length = generation.recUvars := by
        simpa [VInductDecl.GenerationChecked.recursor] using hlevelsArity
      _ = 2 := by
        rw [VInductDecl.GenerationChecked.recUvars_eq,
          generationElimination]
        rfl
  rcases levels with _ | ⟨v, levelTail⟩
  · simp at hlevelsLength
  rcases levelTail with _ | ⟨u, levelTail⟩
  · simp at hlevelsLength
  have hlevelTail : levelTail = [] :=
    List.eq_nil_of_length_eq_zero (by simpa using hlevelsLength)
  subst levelTail

  obtain ⟨constructorHeadType, hconstructorHeadTyped⟩ :=
    Lean4Lean.VEnv.HasType.appN_head hfutureWF hGamma hconstructorApplied
  obtain ⟨constructorConstant, hconstructorLookup, hconstructorLevelsWF,
    hconstructorLevelsArity⟩ :=
    hconstructorHeadTyped.const_inv hfutureWF.ordered hGamma
  have hnormalized : generation.block.ctorPairs[0]? =
      some nilNormalized := by rfl
  have hrawConstructor :=
    CertifiedSingletonGeneration.rawConstructorAt generation hnormalized
  have hrawConstructorMem :
      nilNormalized.raw ∈ generation.block.sourceType.ctors :=
    List.mem_of_getElem? hrawConstructor
  have hcertifiedConstructorLookup :=
    hfuture.constants (transaction.facts.ctorLookup hrawConstructorMem)
  have hconstructorConstant :
      constructorConstant = nilNormalized.raw.toVConstant :=
    Option.some.inj
      (hconstructorLookup.symm.trans hcertifiedConstructorLookup)
  subst constructorConstant
  have hconstructorLevelsLength : constructorLevels.length = 1 := by
    calc
      constructorLevels.length = nilNormalized.raw.toVConstant.uvars :=
        hconstructorLevelsArity
      _ = nilNormalized.raw.uvars := rfl
      _ = indexedVecDecl.uvars :=
        CertifiedSingletonGeneration.sourceConstructorUvars generation
          hrawConstructorMem
      _ = 1 := rfl
  rcases constructorLevels with _ | ⟨constructorU, constructorLevelTail⟩
  · simp at hconstructorLevelsLength
  have hconstructorLevelTail : constructorLevelTail = [] :=
    List.eq_nil_of_length_eq_zero
      (by simpa using hconstructorLevelsLength)
  subst constructorLevelTail

  have hrecursorConstantTyped : future.HasType uvars Gamma
      (.const ``IndexedVec.rec [v, u])
      (generation.recType.instL [v, u]) := by
    have htyped := Lean4Lean.VEnv.HasType.const (Γ := Gamma)
      hcertifiedRecursorLookup hlevelsWF hlevelsArity
    rw [generationRecursorName] at htyped
    simpa [VInductDecl.GenerationChecked.recursor] using htyped
  have hrecursorParameterHead : future.HasType uvars Gamma
      (.const ``IndexedVec.rec [v, u])
      (.forallE (.sort (.succ u))
        (VExpr.dropN 1 (generation.recType.instL [v, u]))) := by
    rw [← recType_parameter]
    exact hrecursorConstantTyped
  have hrecursorAppliedSplit : future.HasType uvars Gamma
      (VExpr.appN (.const ``IndexedVec.rec [v, u])
        ([alpha] ++ [motive, nilMinor, consMinor, index]))
      (.forallE majorDomain majorBody) := by
    simpa using hrecursorApplied
  obtain ⟨recursorParameterResult, hrecursorParameterApplied⟩ :=
    Lean4Lean.VEnv.HasType.appN_prefix hfutureWF hGamma
      (prefixArgs := [alpha])
      (suffixArgs := [motive, nilMinor, consMinor, index])
      hrecursorAppliedSplit
  have hrecursorAlpha : future.HasType uvars Gamma alpha
      (.sort (.succ u)) :=
    Lean4Lean.VEnv.HasType.app_argument_of_head hfutureWF hGamma
      hrecursorParameterApplied hrecursorParameterHead

  have hconstructorConstantTyped : future.HasType uvars Gamma
      (.const ``IndexedVec.nil [constructorU])
      (nilNormalized.raw.toVConstant.type.instL [constructorU]) := by
    simpa [nilNormalizedName] using
      (Lean4Lean.VEnv.HasType.const (Γ := Gamma)
        hcertifiedConstructorLookup hconstructorLevelsWF
          hconstructorLevelsArity)
  have hconstructorParameterHead : future.HasType uvars Gamma
      (.const ``IndexedVec.nil [constructorU])
      (.forallE (.sort (.succ constructorU))
        (VExpr.dropN 1
          (nilNormalized.raw.toVConstant.type.instL [constructorU]))) := by
    rw [← nilConstructorType_parameter]
    exact hconstructorConstantTyped
  have hconstructorAlpha : future.HasType uvars Gamma constructorAlpha
      (.sort (.succ constructorU)) :=
    Lean4Lean.VEnv.HasType.app_argument_of_head hfutureWF hGamma
      hconstructorApplied hconstructorParameterHead

  obtain ⟨parameterType, hparameterTyped⟩ := hparameter'
  have hrecursorSort : future.IsDefEqU uvars Gamma
      (.sort (.succ u)) parameterType :=
    hrecursorAlpha.uniqU hfutureWF hGamma hparameterTyped.hasType.1
  have hconstructorSort : future.IsDefEqU uvars Gamma
      (.sort (.succ constructorU)) parameterType :=
    hconstructorAlpha.uniqU hfutureWF hGamma hparameterTyped.hasType.2
  have hsorts : future.IsDefEqU uvars Gamma
      (.sort (.succ u)) (.sort (.succ constructorU)) :=
    hrecursorSort.trans hfutureWF hGamma hconstructorSort.symm
  have huniverse : u ≈ constructorU :=
    VLevel.succ_congr_iff.mp
      (Lean4Lean.VEnv.IsDefEqU.sort_inv hfutureWF hGamma hsorts)

  have hnilLookup := hcertifiedConstructorLookup
  rw [nilNormalizedName] at hnilLookup
  have hconstructorConstantEq : future.IsDefEq uvars Gamma
      (.const ``IndexedVec.nil [constructorU])
      (.const ``IndexedVec.nil [u])
      (nilNormalized.raw.toVConstant.type.instL [constructorU]) := by
    exact .constDF hnilLookup hconstructorLevelsWF
      (fun level hlevel => by
        simp only [List.mem_singleton] at hlevel
        subst level
        exact hlevelsWF u (by simp))
      hconstructorLevelsArity
      (.cons huniverse.symm .nil)
  rw [nilConstructorType_parameter] at hconstructorConstantEq
  have hparameterU : future.IsDefEqU uvars Gamma alpha constructorAlpha :=
    ⟨parameterType, hparameterTyped⟩
  have hparameterAtConstructor : future.IsDefEq uvars Gamma
      constructorAlpha alpha (.sort (.succ constructorU)) :=
    hparameterU.symm.of_l hfutureWF hGamma hconstructorAlpha
  have hconstructorEq : future.IsDefEqU uvars Gamma
      (.app (.const ``IndexedVec.nil [constructorU]) constructorAlpha)
      (.app (.const ``IndexedVec.nil [u]) alpha) :=
    ⟨_, .appDF hconstructorConstantEq hparameterAtConstructor⟩

  obtain ⟨indexDomain, indexBody, hrecursorBeforeIndex, hindexTyped⟩ :=
    hrecursorApplied.app_inv hfutureWF.ordered hGamma
  have hindexAtDomain : future.IsDefEq uvars Gamma index
      (.const ``Nat.zero []) indexDomain :=
    hindex'.of_l hfutureWF hGamma hindexTyped
  have hrecursorIndexEq : future.IsDefEqU uvars Gamma
      (VExpr.appN (.const ``IndexedVec.rec [v, u])
        [alpha, motive, nilMinor, consMinor, index])
      (VExpr.appN (.const ``IndexedVec.rec [v, u])
        [alpha, motive, nilMinor, consMinor, .const ``Nat.zero []]) := by
    refine ⟨indexBody.inst index, ?_⟩
    simpa only [VExpr.appN] using
      (Lean4Lean.VEnv.IsDefEq.appDF hrecursorBeforeIndex hindexAtDomain)
  have hrecursorIndexEqTyped : future.IsDefEq uvars Gamma
      (VExpr.appN (.const ``IndexedVec.rec [v, u])
        [alpha, motive, nilMinor, consMinor, index])
      (VExpr.appN (.const ``IndexedVec.rec [v, u])
        [alpha, motive, nilMinor, consMinor, .const ``Nat.zero []])
      (.forallE majorDomain majorBody) :=
    hrecursorIndexEq.of_l hfutureWF hGamma hrecursorApplied
  have hconstructorEqTyped : future.IsDefEq uvars Gamma
      (.app (.const ``IndexedVec.nil [constructorU]) constructorAlpha)
      (.app (.const ``IndexedVec.nil [u]) alpha) majorDomain :=
    hconstructorEq.of_l hfutureWF hGamma hconstructorApplied
  have hredex : future.IsDefEqU uvars Gamma
      (.app
        (VExpr.appN (.const ``IndexedVec.rec [v, u])
          [alpha, motive, nilMinor, consMinor, index])
        (.app (.const ``IndexedVec.nil [constructorU]) constructorAlpha))
      (.app
        (VExpr.appN (.const ``IndexedVec.rec [v, u])
          [alpha, motive, nilMinor, consMinor, .const ``Nat.zero []])
      (.app (.const ``IndexedVec.nil [u]) alpha)) :=
    ⟨_, .appDF hrecursorIndexEqTyped hconstructorEqTyped⟩

  obtain ⟨registeredNormalized, hregisteredNormalized, hregistered⟩ :=
    link.registeredRuleAt hrule
  have hregisteredNormalizedEq : registeredNormalized = nilNormalized := by
    rw [hnormalized] at hregisteredNormalized
    exact (Option.some.inj hregisteredNormalized).symm
  subst registeredNormalized
  have hregisteredFuture := hregistered.mono hfuture
  obtain ⟨_, _, _, _, hdefeqRegistered, hdefeqWF, _, _, _⟩ :=
    hregisteredFuture
  have hlevelsRuleArity :
      [v, u].length = (generation.rule 0 nilNormalized).uvars := by rfl
  have hequation : future.IsDefEq uvars Gamma
      ((generation.rule 0 nilNormalized).lhs.instL [v, u])
      ((generation.rule 0 nilNormalized).rhs.instL [v, u])
      ((generation.rule 0 nilNormalized).type.instL [v, u]) :=
    .extra hdefeqRegistered hlevelsWF hlevelsRuleArity

  have hrecursorCommonType : future.HasType uvars Gamma
      (.const ``IndexedVec.rec [v, u])
      (VExpr.forallN (commonBinders.map (VExpr.instL [v, u]))
        (VExpr.dropN 4 (generation.recType.instL [v, u]))) := by
    rw [← recType_common]
    exact hrecursorConstantTyped
  have hequationLhsCommonType : future.HasType uvars Gamma
      ((generation.rule 0 nilNormalized).lhs.instL [v, u])
      (VExpr.forallN (commonBinders.map (VExpr.instL [v, u]))
        (VExpr.dropN 4
          ((generation.rule 0 nilNormalized).type.instL [v, u]))) := by
    rw [← ruleType_common]
    exact hequation.hasType.1
  have hrecursorCommonAppliedSplit : future.HasType uvars Gamma
      (VExpr.appN (.const ``IndexedVec.rec [v, u])
        ([alpha, motive, nilMinor, consMinor] ++ [index]))
      (.forallE majorDomain majorBody) := by
    simpa using hrecursorApplied
  obtain ⟨recursorCommonResult, hrecursorCommonApplied⟩ :=
    Lean4Lean.VEnv.HasType.appN_prefix hfutureWF hGamma
      (prefixArgs := [alpha, motive, nilMinor, consMinor])
      (suffixArgs := [index]) hrecursorCommonAppliedSplit
  have hcommonLength :
      [alpha, motive, nilMinor, consMinor].length =
        (commonBinders.map (VExpr.instL [v, u])).length := by simp
  have hequationLhsApplied :=
    Lean4Lean.VEnv.HasType.transfer_appN_telescope_instRev
      hfutureWF hGamma hcommonLength hrecursorCommonApplied
      hrecursorCommonType hequationLhsCommonType
  have hequationApplied :=
    Lean4Lean.VEnv.IsDefEq.appN_same hfutureWF hGamma hequation
      hequationLhsApplied
  have hequationRhsApplied :=
    (hequationApplied.of_l hfutureWF hGamma
      hequationLhsApplied).hasType.2

  have hruleBinderLength :
      [alpha, motive, nilMinor, consMinor].length =
        ((ruleBinders nilNormalized).map (VExpr.instL [v, u])).length := by
    simp
  have hequationLhsApplied' := hequationLhsApplied
  rw [(generatedRule_shape 0 nilNormalized).1,
    VExpr.instL_lamN] at hequationLhsApplied'
  have hlhsBeta := Lean4Lean.VEnv.HasType.lamN_appN_beta
    hfutureWF hGamma hruleBinderLength hequationLhsApplied'
  rw [nilLhsBody_open] at hlhsBeta
  have hlhsBeta' : future.IsDefEqU uvars Gamma
      (VExpr.appN ((generation.rule 0 nilNormalized).lhs.instL [v, u])
        [alpha, motive, nilMinor, consMinor])
      (.app
        (VExpr.appN (.const ``IndexedVec.rec [v, u])
          [alpha, motive, nilMinor, consMinor, .const ``Nat.zero []])
        (.app (.const ``IndexedVec.nil [u]) alpha)) := by
    rw [(generatedRule_shape 0 nilNormalized).1,
      VExpr.instL_lamN]
    exact hlhsBeta

  have hequationRhsApplied' := hequationRhsApplied
  rw [(generatedRule_shape 0 nilNormalized).2.1,
    VExpr.instL_lamN] at hequationRhsApplied'
  have hrhsBeta := Lean4Lean.VEnv.HasType.lamN_appN_beta
    hfutureWF hGamma hruleBinderLength hequationRhsApplied'
  rw [nilRhsBody_open] at hrhsBeta
  have hrhsBeta' : future.IsDefEqU uvars Gamma
      (VExpr.appN ((generation.rule 0 nilNormalized).rhs.instL [v, u])
        [alpha, motive, nilMinor, consMinor]) nilMinor := by
    rw [(generatedRule_shape 0 nilNormalized).2.1,
      VExpr.instL_lamN]
    exact hrhsBeta

  have hgenerated :=
    (hlhsBeta'.symm.trans hfutureWF hGamma hequationApplied).trans
      hfutureWF hGamma hrhsBeta'
  have hresult := hredex.trans hfutureWF hGamma hgenerated
  let selected : Fin 5 := ⟨2, by omega⟩
  have hselected? := hrecCaptures selected
  have hselected : nilMinor =
      captures (RecursorIotaPattern.recursorArgumentPath ``IndexedVec.rec 5
        ``IndexedVec.nil 1 selected) := by
    exact Option.some.inj (by simpa [selected] using hselected?)
  rw [hmatched]
  change future.IsDefEqU uvars Gamma
    (.app
      (VExpr.appN (.const ``IndexedVec.rec [v, u])
        [alpha, motive, nilMinor, consMinor, index])
      (VExpr.appN (.const ``IndexedVec.nil [constructorU])
        [constructorAlpha]))
    (captures (RecursorIotaPattern.recursorArgumentPath ``IndexedVec.rec 5
      ``IndexedVec.nil 1 selected))
  rw [← hselected]
  simpa only [VExpr.appN] using hresult

/-- The recursive indexed pattern is exactly the second generated equation.
Besides the common recursor prefix, this proof transports the constructor's
dependent three-field telescope to the equation before opening its recursive
RHS. -/
theorem consPatternSound
    {trProj : RawProjRel} {catalog : Catalog}
    {nameOf : Address → Option Lean.Name} {trusted : KId .anon → Prop}
    {family : SingletonFamilyCatalogLink trProj catalog nameOf trusted
      transaction}
    (link : SingletonRecursorCatalogLink trProj catalog nameOf trusted
      transaction family)
    {rule : RecRule .anon}
    (hrule : link.recursorConcrete.RecursorRuleAt 1 rule)
    (constructorId : KId .anon) :
    (consPattern constructorId).Sound indexedVecFinalEnv := by
  unfold RecursorRulePattern.Sound
  simp [consPattern, recursorName]
  intro future hfuture hfutureWF uvars Gamma matched levels captures A
    hGamma hmatches htype hchecks
  change Pattern.Matches
      (RecursorIotaPattern ``IndexedVec.rec 5 ``IndexedVec.cons 4)
      matched levels captures at hmatches
  obtain ⟨recursorArguments, constructorLevels, constructorArguments,
    hrecursorLength, hconstructorLength, hmatched, hrecCaptures,
    hconstructorCaptures⟩ :=
    RecursorIotaPattern.matches_spines_full hmatches
  rcases recursorArguments with _ | ⟨alpha, rec1⟩
  · simp at hrecursorLength
  rcases rec1 with _ | ⟨motive, rec2⟩
  · simp at hrecursorLength
  rcases rec2 with _ | ⟨nilMinor, rec3⟩
  · simp at hrecursorLength
  rcases rec3 with _ | ⟨consMinor, rec4⟩
  · simp at hrecursorLength
  rcases rec4 with _ | ⟨index, recTail⟩
  · simp at hrecursorLength
  have hrecTail : recTail = [] :=
    List.eq_nil_of_length_eq_zero (by simpa using hrecursorLength)
  subst recTail
  rcases constructorArguments with _ | ⟨constructorAlpha, ctor1⟩
  · simp at hconstructorLength
  rcases ctor1 with _ | ⟨n, ctor2⟩
  · simp at hconstructorLength
  rcases ctor2 with _ | ⟨a, ctor3⟩
  · simp at hconstructorLength
  rcases ctor3 with _ | ⟨as, ctorTail⟩
  · simp at hconstructorLength
  have hctorTail : ctorTail = [] :=
    List.eq_nil_of_length_eq_zero (by simpa using hconstructorLength)
  subst ctorTail

  have hcapAlpha := hrecCaptures ⟨0, by omega⟩
  have hcapMotive := hrecCaptures ⟨1, by omega⟩
  have hcapNil := hrecCaptures ⟨2, by omega⟩
  have hcapCons := hrecCaptures ⟨3, by omega⟩
  have hcapIndex := hrecCaptures ⟨4, by omega⟩
  have hcapConstructorAlpha := hconstructorCaptures ⟨0, by omega⟩
  have hcapN := hconstructorCaptures ⟨1, by omega⟩
  have hcapA := hconstructorCaptures ⟨2, by omega⟩
  have hcapAs := hconstructorCaptures ⟨3, by omega⟩
  simp at hcapAlpha hcapMotive hcapNil hcapCons hcapIndex
  simp at hcapConstructorAlpha hcapN hcapA hcapAs
  have hchecks' : consChecks.OK (future.IsDefEqU uvars Gamma)
      levels captures := by simpa [consPattern] using hchecks
  obtain ⟨hparameter, hindex⟩ :=
    consChecks_ok (future.IsDefEqU uvars Gamma) levels captures hchecks'
  have hparameter' : future.IsDefEqU uvars Gamma alpha constructorAlpha := by
    rw [hcapAlpha, hcapConstructorAlpha]
    simpa [consPattern] using hparameter
  have hindex' : future.IsDefEqU uvars Gamma index
      (.app (.const ``Nat.succ []) n) := by
    rw [hcapIndex, hcapN]
    simpa [consPattern] using hindex

  rw [hmatched] at htype
  obtain ⟨majorDomain, majorBody, hrecursorApplied,
    hconstructorApplied⟩ := htype.app_inv hfutureWF.ordered hGamma

  obtain ⟨recursorHeadType, hrecursorHeadTyped⟩ :=
    Lean4Lean.VEnv.HasType.appN_head hfutureWF hGamma hrecursorApplied
  obtain ⟨recursorConstant, hrecursorLookup, hlevelsWF, hlevelsArity⟩ :=
    hrecursorHeadTyped.const_inv hfutureWF.ordered hGamma
  have hcertifiedRecursorLookup :=
    hfuture.constants transaction.facts.recursorLookup
  have hrecursorConstant : recursorConstant = generation.recursor :=
    Option.some.inj (hrecursorLookup.symm.trans hcertifiedRecursorLookup)
  subst recursorConstant
  have hlevelsLength : levels.length = 2 := by
    calc
      levels.length = generation.recUvars := by
        simpa [VInductDecl.GenerationChecked.recursor] using hlevelsArity
      _ = 2 := by
        rw [VInductDecl.GenerationChecked.recUvars_eq,
          generationElimination]
        rfl
  rcases levels with _ | ⟨v, levelTail⟩
  · simp at hlevelsLength
  rcases levelTail with _ | ⟨u, levelTail⟩
  · simp at hlevelsLength
  have hlevelTail : levelTail = [] :=
    List.eq_nil_of_length_eq_zero (by simpa using hlevelsLength)
  subst levelTail

  obtain ⟨constructorHeadType, hconstructorHeadTyped⟩ :=
    Lean4Lean.VEnv.HasType.appN_head hfutureWF hGamma hconstructorApplied
  obtain ⟨constructorConstant, hconstructorLookup, hconstructorLevelsWF,
    hconstructorLevelsArity⟩ :=
    hconstructorHeadTyped.const_inv hfutureWF.ordered hGamma
  have hnormalized : generation.block.ctorPairs[1]? =
      some consNormalized := by rfl
  have hrawConstructor :=
    CertifiedSingletonGeneration.rawConstructorAt generation hnormalized
  have hrawConstructorMem :
      consNormalized.raw ∈ generation.block.sourceType.ctors :=
    List.mem_of_getElem? hrawConstructor
  have hcertifiedConstructorLookup :=
    hfuture.constants (transaction.facts.ctorLookup hrawConstructorMem)
  have hconstructorConstant :
      constructorConstant = consNormalized.raw.toVConstant :=
    Option.some.inj
      (hconstructorLookup.symm.trans hcertifiedConstructorLookup)
  subst constructorConstant
  have hconstructorLevelsLength : constructorLevels.length = 1 := by
    calc
      constructorLevels.length = consNormalized.raw.toVConstant.uvars :=
        hconstructorLevelsArity
      _ = consNormalized.raw.uvars := rfl
      _ = indexedVecDecl.uvars :=
        CertifiedSingletonGeneration.sourceConstructorUvars generation
          hrawConstructorMem
      _ = 1 := rfl
  rcases constructorLevels with _ | ⟨constructorU, constructorLevelTail⟩
  · simp at hconstructorLevelsLength
  have hconstructorLevelTail : constructorLevelTail = [] :=
    List.eq_nil_of_length_eq_zero
      (by simpa using hconstructorLevelsLength)
  subst constructorLevelTail

  have hrecursorConstantTyped : future.HasType uvars Gamma
      (.const ``IndexedVec.rec [v, u])
      (generation.recType.instL [v, u]) := by
    have htyped := Lean4Lean.VEnv.HasType.const (Γ := Gamma)
      hcertifiedRecursorLookup hlevelsWF hlevelsArity
    rw [generationRecursorName] at htyped
    simpa [VInductDecl.GenerationChecked.recursor] using htyped
  have hrecursorParameterHead : future.HasType uvars Gamma
      (.const ``IndexedVec.rec [v, u])
      (.forallE (.sort (.succ u))
        (VExpr.dropN 1 (generation.recType.instL [v, u]))) := by
    rw [← recType_parameter]
    exact hrecursorConstantTyped
  have hrecursorAppliedSplit : future.HasType uvars Gamma
      (VExpr.appN (.const ``IndexedVec.rec [v, u])
        ([alpha] ++ [motive, nilMinor, consMinor, index]))
      (.forallE majorDomain majorBody) := by
    simpa using hrecursorApplied
  obtain ⟨recursorParameterResult, hrecursorParameterApplied⟩ :=
    Lean4Lean.VEnv.HasType.appN_prefix hfutureWF hGamma
      (prefixArgs := [alpha])
      (suffixArgs := [motive, nilMinor, consMinor, index])
      hrecursorAppliedSplit
  have hrecursorAlpha : future.HasType uvars Gamma alpha
      (.sort (.succ u)) :=
    Lean4Lean.VEnv.HasType.app_argument_of_head hfutureWF hGamma
      hrecursorParameterApplied hrecursorParameterHead

  have hconstructorConstantTyped : future.HasType uvars Gamma
      (.const ``IndexedVec.cons [constructorU])
      (consNormalized.raw.toVConstant.type.instL [constructorU]) := by
    simpa [consNormalizedName] using
      (Lean4Lean.VEnv.HasType.const (Γ := Gamma)
        hcertifiedConstructorLookup hconstructorLevelsWF
          hconstructorLevelsArity)
  have hconstructorParameterHead : future.HasType uvars Gamma
      (.const ``IndexedVec.cons [constructorU])
      (.forallE (.sort (.succ constructorU))
        (VExpr.dropN 1
          (consNormalized.raw.toVConstant.type.instL [constructorU]))) := by
    rw [← consConstructorType_parameter]
    exact hconstructorConstantTyped
  have hconstructorAppliedSplit : future.HasType uvars Gamma
      (VExpr.appN (.const ``IndexedVec.cons [constructorU])
        ([constructorAlpha] ++ [n, a, as])) majorDomain := by
    simpa using hconstructorApplied
  obtain ⟨constructorParameterResult, hconstructorParameterApplied⟩ :=
    Lean4Lean.VEnv.HasType.appN_prefix hfutureWF hGamma
      (prefixArgs := [constructorAlpha]) (suffixArgs := [n, a, as])
      hconstructorAppliedSplit
  have hconstructorAlpha : future.HasType uvars Gamma constructorAlpha
      (.sort (.succ constructorU)) :=
    Lean4Lean.VEnv.HasType.app_argument_of_head hfutureWF hGamma
      hconstructorParameterApplied hconstructorParameterHead

  obtain ⟨parameterType, hparameterTyped⟩ := hparameter'
  have hrecursorSort : future.IsDefEqU uvars Gamma
      (.sort (.succ u)) parameterType :=
    hrecursorAlpha.uniqU hfutureWF hGamma hparameterTyped.hasType.1
  have hconstructorSort : future.IsDefEqU uvars Gamma
      (.sort (.succ constructorU)) parameterType :=
    hconstructorAlpha.uniqU hfutureWF hGamma hparameterTyped.hasType.2
  have hsorts : future.IsDefEqU uvars Gamma
      (.sort (.succ u)) (.sort (.succ constructorU)) :=
    hrecursorSort.trans hfutureWF hGamma hconstructorSort.symm
  have huniverse : u ≈ constructorU :=
    VLevel.succ_congr_iff.mp
      (Lean4Lean.VEnv.IsDefEqU.sort_inv hfutureWF hGamma hsorts)

  have hconsLookup := hcertifiedConstructorLookup
  rw [consNormalizedName] at hconsLookup
  have hconstructorConstantEq : future.IsDefEq uvars Gamma
      (.const ``IndexedVec.cons [constructorU])
      (.const ``IndexedVec.cons [u])
      (consNormalized.raw.toVConstant.type.instL [constructorU]) := by
    exact .constDF hconsLookup hconstructorLevelsWF
      (fun level hlevel => by
        simp only [List.mem_singleton] at hlevel
        subst level
        exact hlevelsWF u (by simp))
      hconstructorLevelsArity
      (.cons huniverse.symm .nil)
  rw [consConstructorType_parameter] at hconstructorConstantEq
  have hparameterU : future.IsDefEqU uvars Gamma alpha constructorAlpha :=
    ⟨parameterType, hparameterTyped⟩
  have hparameterAtConstructor : future.IsDefEq uvars Gamma
      constructorAlpha alpha (.sort (.succ constructorU)) :=
    hparameterU.symm.of_l hfutureWF hGamma hconstructorAlpha
  have hconstructorPrefixEq : future.IsDefEqU uvars Gamma
      (.app (.const ``IndexedVec.cons [constructorU]) constructorAlpha)
      (.app (.const ``IndexedVec.cons [u]) alpha) :=
    ⟨_, .appDF hconstructorConstantEq hparameterAtConstructor⟩
  have hconstructorPrefixEqTyped : future.IsDefEq uvars Gamma
      (.app (.const ``IndexedVec.cons [constructorU]) constructorAlpha)
      (.app (.const ``IndexedVec.cons [u]) alpha)
      constructorParameterResult :=
    hconstructorPrefixEq.of_l hfutureWF hGamma hconstructorParameterApplied
  have hconstructorAppliedFromPrefix : future.HasType uvars Gamma
      (VExpr.appN
        (.app (.const ``IndexedVec.cons [constructorU]) constructorAlpha)
        [n, a, as]) majorDomain := by
    simpa only [VExpr.appN] using hconstructorApplied
  have hconstructorEq : future.IsDefEqU uvars Gamma
      (VExpr.appN (.const ``IndexedVec.cons [constructorU])
        [constructorAlpha, n, a, as])
      (VExpr.appN (.const ``IndexedVec.cons [u]) [alpha, n, a, as]) := by
    simpa only [VExpr.appN] using
      (Lean4Lean.VEnv.IsDefEq.appN_same hfutureWF hGamma
        hconstructorPrefixEqTyped hconstructorAppliedFromPrefix)

  obtain ⟨indexDomain, indexBody, hrecursorBeforeIndex, hindexTyped⟩ :=
    hrecursorApplied.app_inv hfutureWF.ordered hGamma
  have hindexAtDomain : future.IsDefEq uvars Gamma index
      (.app (.const ``Nat.succ []) n) indexDomain :=
    hindex'.of_l hfutureWF hGamma hindexTyped
  have hrecursorIndexEq : future.IsDefEqU uvars Gamma
      (VExpr.appN (.const ``IndexedVec.rec [v, u])
        [alpha, motive, nilMinor, consMinor, index])
      (VExpr.appN (.const ``IndexedVec.rec [v, u])
        [alpha, motive, nilMinor, consMinor,
          .app (.const ``Nat.succ []) n]) := by
    refine ⟨indexBody.inst index, ?_⟩
    simpa only [VExpr.appN] using
      (Lean4Lean.VEnv.IsDefEq.appDF hrecursorBeforeIndex hindexAtDomain)
  have hrecursorIndexEqTyped : future.IsDefEq uvars Gamma
      (VExpr.appN (.const ``IndexedVec.rec [v, u])
        [alpha, motive, nilMinor, consMinor, index])
      (VExpr.appN (.const ``IndexedVec.rec [v, u])
        [alpha, motive, nilMinor, consMinor,
          .app (.const ``Nat.succ []) n])
      (.forallE majorDomain majorBody) :=
    hrecursorIndexEq.of_l hfutureWF hGamma hrecursorApplied
  have hconstructorEqTyped : future.IsDefEq uvars Gamma
      (VExpr.appN (.const ``IndexedVec.cons [constructorU])
        [constructorAlpha, n, a, as])
      (VExpr.appN (.const ``IndexedVec.cons [u]) [alpha, n, a, as])
      majorDomain :=
    hconstructorEq.of_l hfutureWF hGamma hconstructorApplied
  have hredex : future.IsDefEqU uvars Gamma
      (.app
        (VExpr.appN (.const ``IndexedVec.rec [v, u])
          [alpha, motive, nilMinor, consMinor, index])
        (VExpr.appN (.const ``IndexedVec.cons [constructorU])
          [constructorAlpha, n, a, as]))
      (.app
        (VExpr.appN (.const ``IndexedVec.rec [v, u])
          [alpha, motive, nilMinor, consMinor,
            .app (.const ``Nat.succ []) n])
        (VExpr.appN (.const ``IndexedVec.cons [u])
          [alpha, n, a, as])) :=
    ⟨_, .appDF hrecursorIndexEqTyped hconstructorEqTyped⟩

  obtain ⟨registeredNormalized, hregisteredNormalized, hregistered⟩ :=
    link.registeredRuleAt hrule
  have hregisteredNormalizedEq : registeredNormalized = consNormalized := by
    rw [hnormalized] at hregisteredNormalized
    exact (Option.some.inj hregisteredNormalized).symm
  subst registeredNormalized
  have hregisteredFuture := hregistered.mono hfuture
  obtain ⟨_, _, _, _, hdefeqRegistered, hdefeqWF, _, _, _⟩ :=
    hregisteredFuture
  have hlevelsRuleArity :
      [v, u].length = (generation.rule 1 consNormalized).uvars := by rfl
  have hequation : future.IsDefEq uvars Gamma
      ((generation.rule 1 consNormalized).lhs.instL [v, u])
      ((generation.rule 1 consNormalized).rhs.instL [v, u])
      ((generation.rule 1 consNormalized).type.instL [v, u]) :=
    .extra hdefeqRegistered hlevelsWF hlevelsRuleArity

  have hrecursorCommonType : future.HasType uvars Gamma
      (.const ``IndexedVec.rec [v, u])
      (VExpr.forallN (commonBinders.map (VExpr.instL [v, u]))
        (VExpr.dropN 4 (generation.recType.instL [v, u]))) := by
    rw [← recType_common]
    exact hrecursorConstantTyped
  have hequationLhsCommonType : future.HasType uvars Gamma
      ((generation.rule 1 consNormalized).lhs.instL [v, u])
      (VExpr.forallN (commonBinders.map (VExpr.instL [v, u]))
        (VExpr.dropN 4
          ((generation.rule 1 consNormalized).type.instL [v, u]))) := by
    rw [← ruleType_common]
    exact hequation.hasType.1
  have hrecursorCommonAppliedSplit : future.HasType uvars Gamma
      (VExpr.appN (.const ``IndexedVec.rec [v, u])
        ([alpha, motive, nilMinor, consMinor] ++ [index]))
      (.forallE majorDomain majorBody) := by
    simpa using hrecursorApplied
  obtain ⟨recursorCommonResult, hrecursorCommonApplied⟩ :=
    Lean4Lean.VEnv.HasType.appN_prefix hfutureWF hGamma
      (prefixArgs := [alpha, motive, nilMinor, consMinor])
      (suffixArgs := [index]) hrecursorCommonAppliedSplit
  have hcommonLength :
      [alpha, motive, nilMinor, consMinor].length =
        (commonBinders.map (VExpr.instL [v, u])).length := by simp
  have hequationLhsCommonApplied : future.HasType uvars Gamma
      (VExpr.appN ((generation.rule 1 consNormalized).lhs.instL [v, u])
        [alpha, motive, nilMinor, consMinor])
      (consEquationFieldType v u alpha motive nilMinor consMinor) := by
    exact Lean4Lean.VEnv.HasType.transfer_appN_telescope_instRev
      hfutureWF hGamma hcommonLength hrecursorCommonApplied
      hrecursorCommonType hequationLhsCommonType

  have hcanonicalConstructorConstantTyped : future.HasType uvars Gamma
      (.const ``IndexedVec.cons [u])
      (consNormalized.raw.toVConstant.type.instL [u]) := by
    exact Lean4Lean.VEnv.HasType.const hconsLookup
      (fun level hlevel => by
        simp only [List.mem_singleton] at hlevel
        subst level
        exact hlevelsWF u (by simp))
      (by rfl)
  have hcanonicalConstructorParameterHead : future.HasType uvars Gamma
      (.const ``IndexedVec.cons [u])
      (.forallE (.sort (.succ u))
        (VExpr.dropN 1 (consNormalized.raw.toVConstant.type.instL [u]))) := by
    rw [← consConstructorType_parameter]
    exact hcanonicalConstructorConstantTyped
  have hcanonicalConstructorPrefix : future.HasType uvars Gamma
      (.app (.const ``IndexedVec.cons [u]) alpha)
      (consConstructorFieldType u alpha) := by
    have happ := Lean4Lean.VEnv.HasType.app
      hcanonicalConstructorParameterHead hrecursorAlpha
    simpa [consConstructorFieldType, VExpr.instRev] using happ
  have hcanonicalConstructorApplied : future.HasType uvars Gamma
      (VExpr.appN (.app (.const ``IndexedVec.cons [u]) alpha) [n, a, as])
      majorDomain := by
    have htyped :=
      (hconstructorEq.of_l hfutureWF hGamma hconstructorApplied).hasType.2
    simpa only [VExpr.appN] using htyped

  have hequationFieldHead : future.HasType uvars Gamma
      (VExpr.appN ((generation.rule 1 consNormalized).lhs.instL [v, u])
        [alpha, motive, nilMinor, consMinor])
      (VExpr.forallN
        (VExpr.telN 3
          (consEquationFieldType v u alpha motive nilMinor consMinor))
        (VExpr.dropN 3
          (consEquationFieldType v u alpha motive nilMinor consMinor))) := by
    rw [← VExpr.forallN_telN_dropN 3
      (consEquationFieldType v u alpha motive nilMinor consMinor)]
    exact hequationLhsCommonApplied
  have hconstructorFieldHead : future.HasType uvars Gamma
      (.app (.const ``IndexedVec.cons [u]) alpha)
      (VExpr.forallN (VExpr.telN 3 (consConstructorFieldType u alpha))
        (VExpr.dropN 3 (consConstructorFieldType u alpha))) := by
    rw [← VExpr.forallN_telN_dropN 3
      (consConstructorFieldType u alpha)]
    exact hcanonicalConstructorPrefix
  have hconstructorFieldHead' : future.HasType uvars Gamma
      (.app (.const ``IndexedVec.cons [u]) alpha)
      (VExpr.forallN
        (VExpr.telN 3
          (consEquationFieldType v u alpha motive nilMinor consMinor))
        (VExpr.dropN 3 (consConstructorFieldType u alpha))) := by
    rw [consFieldBinders_eq]
    exact hconstructorFieldHead
  have hfieldLength :
      [n, a, as].length =
        (VExpr.telN 3
          (consEquationFieldType v u alpha motive nilMinor consMinor)).length := by
    rw [consFieldBinders_eq]
    simp [consConstructorFieldType, consNormalizedRaw, indexedVecType,
      VExpr.instRev, VExpr.instL, VExpr.inst, VExpr.instVar,
      VExpr.telN, VExpr.dropN]
  have hequationLhsFieldsApplied :=
    Lean4Lean.VEnv.HasType.transfer_appN_telescope_instRev
      hfutureWF hGamma hfieldLength hcanonicalConstructorApplied
      hconstructorFieldHead' hequationFieldHead
  have hequationLhsApplied : future.HasType uvars Gamma
      (VExpr.appN ((generation.rule 1 consNormalized).lhs.instL [v, u])
        [alpha, motive, nilMinor, consMinor, n, a, as])
      (VExpr.instRev
        (VExpr.dropN 3
          (consEquationFieldType v u alpha motive nilMinor consMinor))
        [n, a, as]) := by
    rw [show [alpha, motive, nilMinor, consMinor, n, a, as] =
      [alpha, motive, nilMinor, consMinor] ++ [n, a, as] by rfl,
      VExpr.appN_append]
    exact hequationLhsFieldsApplied
  have hequationApplied :=
    Lean4Lean.VEnv.IsDefEq.appN_same hfutureWF hGamma hequation
      hequationLhsApplied
  have hequationRhsApplied :=
    (hequationApplied.of_l hfutureWF hGamma
      hequationLhsApplied).hasType.2

  have hruleBinderLength :
      [alpha, motive, nilMinor, consMinor, n, a, as].length =
        ((ruleBinders consNormalized).map (VExpr.instL [v, u])).length := by
    simp
  have hequationLhsApplied' := hequationLhsApplied
  rw [(generatedRule_shape 1 consNormalized).1,
    VExpr.instL_lamN] at hequationLhsApplied'
  have hlhsBeta := Lean4Lean.VEnv.HasType.lamN_appN_beta
    hfutureWF hGamma hruleBinderLength hequationLhsApplied'
  rw [consLhsBody_open] at hlhsBeta
  have hlhsBeta' : future.IsDefEqU uvars Gamma
      (VExpr.appN ((generation.rule 1 consNormalized).lhs.instL [v, u])
        [alpha, motive, nilMinor, consMinor, n, a, as])
      (.app
        (VExpr.appN (.const ``IndexedVec.rec [v, u])
          [alpha, motive, nilMinor, consMinor,
            .app (.const ``Nat.succ []) n])
        (VExpr.appN (.const ``IndexedVec.cons [u])
          [alpha, n, a, as])) := by
    rw [(generatedRule_shape 1 consNormalized).1,
      VExpr.instL_lamN]
    exact hlhsBeta

  have hequationRhsApplied' := hequationRhsApplied
  rw [(generatedRule_shape 1 consNormalized).2.1,
    VExpr.instL_lamN] at hequationRhsApplied'
  have hrhsBeta := Lean4Lean.VEnv.HasType.lamN_appN_beta
    hfutureWF hGamma hruleBinderLength hequationRhsApplied'
  rw [consRhsBody_open] at hrhsBeta
  have hrhsBeta' : future.IsDefEqU uvars Gamma
      (VExpr.appN ((generation.rule 1 consNormalized).rhs.instL [v, u])
        [alpha, motive, nilMinor, consMinor, n, a, as])
      (VExpr.appN consMinor
        [n, a, as,
          VExpr.appN (.const ``IndexedVec.rec [v, u])
            [alpha, motive, nilMinor, consMinor, n, as]]) := by
    rw [(generatedRule_shape 1 consNormalized).2.1,
      VExpr.instL_lamN]
    exact hrhsBeta

  have hgenerated :=
    (hlhsBeta'.symm.trans hfutureWF hGamma hequationApplied).trans
      hfutureWF hGamma hrhsBeta'
  have hresult := hredex.trans hfutureWF hGamma hgenerated
  rw [hmatched]
  change future.IsDefEqU uvars Gamma
    (.app
      (VExpr.appN (.const ``IndexedVec.rec [v, u])
        [alpha, motive, nilMinor, consMinor, index])
      (VExpr.appN (.const ``IndexedVec.cons [constructorU])
        [constructorAlpha, n, a, as]))
    ((consPattern constructorId).rhs.apply [v, u] captures)
  rw [consPattern_rhs_apply]
  simpa [hcapAlpha, hcapMotive, hcapNil, hcapCons, hcapN, hcapA, hcapAs]
    using hresult

/-- Complete production relation for generated rule zero. -/
theorem nilPatternRel
    {trProj : RawProjRel} {catalog : Catalog}
    {nameOf : Address → Option Lean.Name} {trusted : KId .anon → Prop}
    {family : SingletonFamilyCatalogLink trProj catalog nameOf trusted
      transaction}
    (link : SingletonRecursorCatalogLink trProj catalog nameOf trusted
      transaction family)
    (hzero : 0 < family.constructorIds.size)
    {rule : RecRule .anon}
    (hrule : link.recursorConcrete.RecursorRuleAt 0 rule) :
    RawRecursorRulePatternRel indexedVecFinalEnv catalog nameOf
      link.recursorId link.recursorConcrete rule
        (nilPattern (family.constructorIds[0]'hzero)) :=
  RawRecursorRulePatternRel.of_metadata_sound
    (nilPatternMetadata link hzero hrule)
    (nilPatternSound link hrule (family.constructorIds[0]'hzero))

/-- Complete production relation for generated rule one, including the
recursive call at the predecessor index. -/
theorem consPatternRel
    {trProj : RawProjRel} {catalog : Catalog}
    {nameOf : Address → Option Lean.Name} {trusted : KId .anon → Prop}
    {family : SingletonFamilyCatalogLink trProj catalog nameOf trusted
      transaction}
    (link : SingletonRecursorCatalogLink trProj catalog nameOf trusted
      transaction family)
    (hone : 1 < family.constructorIds.size)
    {rule : RecRule .anon}
    (hrule : link.recursorConcrete.RecursorRuleAt 1 rule) :
    RawRecursorRulePatternRel indexedVecFinalEnv catalog nameOf
      link.recursorId link.recursorConcrete rule
        (consPattern (family.constructorIds[1]'hone)) :=
  RawRecursorRulePatternRel.of_metadata_sound
    (consPatternMetadata link hone hrule)
    (consPatternSound link hrule (family.constructorIds[1]'hone))

end Ix.Tc.IndexedRecursivePattern
