/-
Adapted for Ix: namespace, imports, and shared universe semantics.
SPDX-License-Identifier: Apache-2.0
Source attribution and revision: Ix/Theory/Named/NOTICE.
-/

import Ix.Theory.Named.Verify.Environment.EliminationFixturesCommon

open Ix.Theory (VLevel)

/-! Exact `Unit`/`PUnit` and `Empty` elimination edge-shape fixtures.

`Unit` is a reducible alias for `PUnit` on this Lean revision. The alias has
definition metadata but no independent inductive/constructor/recursor records,
so the real one-constructor transaction is checked under `PUnit`. `Empty`
supplies the matching zero-constructor transaction. -/

namespace Ix.Theory.Named.InductiveReplayFixtures
open Lean Meta Elab Term
open Ix.Theory.Named.InductiveFixtures

/-- Translate the declaration-first universe order produced by `vconst` to
the fresh-first order stored by large recursor metadata. -/
private def permC06C (constant : VConstant) (levels : List VLevel) :
    VConstant :=
  ⟨constant.uvars, constant.type.instL levels⟩

/-! ## Unit is exactly the reducible PUnit alias -/

def unitAliasInfo06C : DefinitionVal := kernelDefVal% Unit

/-- Pin every field of the actual `Unit` definition metadata. In particular,
there is no fabricated alias-level recursor for the edge fixture. -/
example :
    (unitAliasInfo06C.name, unitAliasInfo06C.levelParams,
      unitAliasInfo06C.type, unitAliasInfo06C.value,
      unitAliasInfo06C.hints, unitAliasInfo06C.safety,
      unitAliasInfo06C.all) =
    (``Unit, [], .sort (.succ .zero),
      .const ``PUnit [.succ .zero], .abbrev, .safe, [``Unit]) := rfl

/-! ## Complete kernel metadata shapes -/

def inductiveShape06C (info : ConstantInfo) :
    Option (Name × List Name × Nat × Nat × List Name × List Name × Nat ×
      Bool × Bool × Bool) :=
  match info with
  | .inductInfo induct => some
      (induct.name, induct.levelParams, induct.numParams, induct.numIndices,
        induct.all, induct.ctors, induct.numNested, induct.isRec,
        induct.isUnsafe, induct.isReflexive)
  | _ => none

def constructorShape06C (info : ConstantInfo) :
    Option (Name × List Name × Name × Nat × Nat × Nat × Bool) :=
  match info with
  | .ctorInfo ctor => some
      (ctor.name, ctor.levelParams, ctor.induct, ctor.cidx, ctor.numParams,
        ctor.numFields, ctor.isUnsafe)
  | _ => none

def completeRecursorShape06C (info : ConstantInfo) :
    Option (Name × List Name × List Name × Nat × Nat × Nat × Nat × Bool ×
      Bool × List (Name × Nat)) :=
  match info with
  | .recInfo rec => some
      (rec.name, rec.levelParams, rec.all, rec.numParams, rec.numIndices,
        rec.numMotives, rec.numMinors, rec.k, rec.isUnsafe,
        rec.rules.map fun rule => (rule.ctor, rule.nfields))
  | _ => none

/-! ## PUnit: one constructor, one minor, one rule -/

def punitInfo06C : ConstantInfo := kernelInductInfo% PUnit
def punitCtorInfo06C : ConstantInfo := kernelCtorInfo% PUnit.unit
def punitRecInfo06C : ConstantInfo := kernelRecInfo% PUnit.rec
def punitRuleRhs06C : VExpr := kernelRecRuleRhs% PUnit.rec 0

example : inductiveShape06C punitInfo06C = some
    (``PUnit, [`u], 0, 0, [``PUnit], [``PUnit.unit], 0, false, false,
      false) := rfl
example : punitInfo06C.type = .sort (.param `u) := rfl
example : constructorShape06C punitCtorInfo06C = some
    (``PUnit.unit, [`u], ``PUnit, 0, 0, 0, false) := rfl
example : punitCtorInfo06C.type = .const ``PUnit [.param `u] := rfl
example : completeRecursorShape06C punitRecInfo06C = some
    (``PUnit.rec, [`u_1, `u], [``PUnit], 0, 0, 1, 1, false, false,
      [(``PUnit.unit, 0)]) := rfl

example : punitChecked.params = [] := rfl
example : punitChecked.indices = [] := rfl
example : punitChecked.constructors.length = 1 := rfl
example : punitChecked.constructors[0].fields = [] := rfl
example : punitChecked.constructors[0].recursive = [] := rfl
example : punitGenerationChecked.block.ctorPairs.length = 1 := rfl
example : punitGenerationChecked.minorTypes =
    [.app (.bvar 0) (.const ``PUnit.unit [.param 1])] := rfl
example : punitGenerationChecked.generatedRules.length = 1 := rfl

/-- The complete generated type agrees with the real recursor, including the
fresh-first `[u_1, u]` metadata order. -/
example : punitGenerationChecked.recursor =
    permC06C (vconst(type_of% @PUnit.rec)) [.param 1, .param 0] := rfl

/-- Removing the three outer binders exposes motive, sole minor, then major.
The minor has no field or induction-hypothesis binders. -/
example : VExpr.telN 3 punitGenerationChecked.recType =
    [punitGenerationChecked.motiveType,
      .app (.bvar 0) (.const ``PUnit.unit [.param 1]),
      .const ``PUnit [.param 1]] := rfl

example : punitRuleRhs06C =
    punitGenerationChecked.generatedRules[0].rhs := rfl

def punitKernelType06C : InductiveType where
  name := punitInfo06C.name
  type := punitInfo06C.type
  ctors := [{ name := punitCtorInfo06C.name, type := punitCtorInfo06C.type }]

def punitEliminationResult06C :=
  AddInductive.NormalizationEliminationExecution.buildExecution 0
    [punitKernelType06C] 0 false (spec06Context [`u])

theorem punitEliminationResult06C_isOk :
    punitEliminationResult06C.isOk = true := by
  native_decide

def punitProducedExecution06C :
    { execution // punitEliminationResult06C = .ok execution } :=
  match h : punitEliminationResult06C with
  | .ok execution => ⟨execution, rfl⟩
  | .error _ => by
      have hOk := punitEliminationResult06C_isOk
      rw [h] at hOk
      contradiction

def punitExecution06C := punitProducedExecution06C.val

def punitAlignment06C : AddInductive.CheckerEliminationRun
    punitGenerationChecked punitExecution06C :=
  (AddInductive.CheckerEliminationRun.build? punitGenerationChecked
    punitExecution06C).get (by native_decide)

def punitLargeSingleton06C :=
  punitExecution06C.elimination.large.singleton.get (by native_decide)

example : punitExecution06C.normalization.stats.params.size = 0 := by
  native_decide
example : punitExecution06C.normalization.stats.nindices = #[0] := by
  native_decide
example : punitExecution06C.normalization.stats.isNotZero = false := by
  native_decide
example : punitExecution06C.elimination.large.result = true := by
  native_decide
example : punitLargeSingleton06C.trace.parameterCount = 0 := by
  native_decide
example : punitLargeSingleton06C.trace.proofFieldCount = 0 := by
  native_decide
example : punitLargeSingleton06C.trace.dataFieldCount = 0 := by
  native_decide
example : punitExecution06C.kTarget.result = false := by native_decide
example : punitExecution06C.kTarget.singleton = none := by native_decide
example : punitExecution06C.elimination.level = .param `u_1 :=
  Level.isStructEq_eq (by native_decide)
example : punitExecution06C.recLevelParams = [`u_1, `u] := by
  native_decide
example : punitExecution06C.recLevels = [.param `u_1, .param `u] :=
  levelListStructEq06_eq (by native_decide)
example : punitGenerationChecked.elimination = .large :=
  punitAlignment06C.large_result_iff.mp (by native_decide)
example : punitGenerationChecked.kTarget = false :=
  punitAlignment06C.kTarget_result_false_iff.mp (by native_decide)

/-! ## Empty: zero constructors, zero minors, zero rules -/

def emptyInfo06C : ConstantInfo := kernelInductInfo% Empty
def emptyRecInfo06C : ConstantInfo := kernelRecInfo% Empty.rec

example : inductiveShape06C emptyInfo06C = some
    (``Empty, [], 0, 0, [``Empty], [], 0, false, false, false) := rfl
example : emptyInfo06C.type = .sort (.succ .zero) := rfl
example : completeRecursorShape06C emptyRecInfo06C = some
    (``Empty.rec, [`u], [``Empty], 0, 0, 1, 0, false, false, []) := rfl

example : emptyChecked.params = [] := rfl
example : emptyChecked.indices = [] := rfl
example : emptyChecked.constructors = [] := rfl
example : emptyGenerationChecked.block.ctorPairs = [] := rfl
example : emptyGenerationChecked.minorTypes = [] := rfl
example : emptyGenerationChecked.generatedRules = [] := rfl
example : emptyGenerationChecked.recursor = vconst(type_of% @Empty.rec) := rfl

/-- Empty elimination has no synthetic constructor minor: motive is followed
immediately by the major. -/
example : VExpr.telN 2 emptyGenerationChecked.recType =
    [emptyGenerationChecked.motiveType, .const ``Empty []] := rfl

def emptyKernelType06C : InductiveType where
  name := emptyInfo06C.name
  type := emptyInfo06C.type
  ctors := []

def emptyEliminationResult06C :=
  AddInductive.NormalizationEliminationExecution.buildExecution 0
    [emptyKernelType06C] 0 false (spec06Context [])

theorem emptyEliminationResult06C_isOk :
    emptyEliminationResult06C.isOk = true := by
  native_decide

def emptyProducedExecution06C :
    { execution // emptyEliminationResult06C = .ok execution } :=
  match h : emptyEliminationResult06C with
  | .ok execution => ⟨execution, rfl⟩
  | .error _ => by
      have hOk := emptyEliminationResult06C_isOk
      rw [h] at hOk
      contradiction

def emptyExecution06C := emptyProducedExecution06C.val

def emptyAlignment06C : AddInductive.CheckerEliminationRun
    emptyGenerationChecked emptyExecution06C :=
  (AddInductive.CheckerEliminationRun.build? emptyGenerationChecked
    emptyExecution06C).get (by native_decide)

example : emptyExecution06C.normalization.stats.params.size = 0 := by
  native_decide
example : emptyExecution06C.normalization.stats.nindices = #[0] := by
  native_decide
example : emptyExecution06C.normalization.stats.isNotZero = true := by
  native_decide
example : emptyExecution06C.elimination.large.result = true := by
  native_decide
example : emptyExecution06C.elimination.large.singleton = none := by
  native_decide
example : emptyExecution06C.kTarget.result = false := by native_decide
example : emptyExecution06C.kTarget.singleton = none := by native_decide
example : emptyExecution06C.elimination.level = .param `u :=
  Level.isStructEq_eq (by native_decide)
example : emptyExecution06C.recLevelParams = [`u] := by native_decide
example : emptyExecution06C.recLevels = [.param `u] :=
  levelListStructEq06_eq (by native_decide)
example : emptyGenerationChecked.elimination = .large :=
  emptyAlignment06C.large_result_iff.mp (by native_decide)
example : emptyGenerationChecked.kTarget = false :=
  emptyAlignment06C.kTarget_result_false_iff.mp (by native_decide)

end Ix.Theory.Named.InductiveReplayFixtures
