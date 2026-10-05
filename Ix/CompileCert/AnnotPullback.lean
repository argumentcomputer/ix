import Ix.CompileCert.Entry

/-! Annotated reading transport, before constructing a source strong model.

Public value equality does not determine an `AnnotTerm`. This relation instead
compares the actual leaves, binder bits, opened bodies and projection positions
used by `denoteMeta`. Establishing it from both checked declaration streams is
an obligation, not a consequence of public `InstalledExprImage`.
-/
namespace Ix.CompileCert

open Kernel Kernel.Model Kernel.Semantics Kernel.SetTheory Kernel.Verify

def PullbackMap.annotations (map : PullbackMap)
    (target : Kernel.Name → (Kernel.Name → Nat) → AnnotTerm) : Kernel.Name → (Kernel.Name → Nat) → AnnotTerm :=
  fun name levels => target (map.name name) (map.levels name levels)

theorem PullbackMap.fromEnvs_annotation_instance {V : Type u} [SetTheory V]
    {sourceEnv targetEnv : Env} (target : StrongInstalledModel V targetEnv)
    {names : Kernel.Name → Kernel.Name} (association : TelescopeAssociation sourceEnv targetEnv names)
    {name : Kernel.Name} {sourceEntry targetEntry : Kernel.ConstantInfo}
    (sourceLookup : sourceEnv.find? name = some sourceEntry)
    (targetLookup : targetEnv.find? (names name) = some targetEntry)
    (sourceLevels targetLevels : Kernel.Name → Nat) (sourceUs targetUs : List Kernel.Level)
    (sourceArity : sourceUs.length = sourceEntry.toConstantVal.levelParams.length)
    (targetArity : targetUs.length = targetEntry.toConstantVal.levelParams.length)
    (arguments : sourceUs.map (Kernel.Level.eval sourceLevels) = targetUs.map (Kernel.Level.eval targetLevels)) :
    (PullbackMap.fromEnvs sourceEnv targetEnv names).annotations target.internal.base2.acval name
        (Kernel.Level.substFn sourceLevels sourceEntry.toConstantVal.levelParams sourceUs) =
      target.internal.base2.acval (names name)
        (Kernel.Level.substFn targetLevels targetEntry.toConstantVal.levelParams targetUs) := by
  apply target.internal.base2.acval_params (names name) targetEntry targetLookup
  exact PullbackMap.fromEnvs_instance association sourceLookup targetLookup sourceLevels targetLevels
    sourceUs targetUs sourceArity targetArity arguments

/-- Scope-indexed correspondence follows the actual reading's binder opening.
The free-variable type annotation is irrelevant to this reading, but its own
context validity remains a separate strong-model obligation. -/
inductive AnnotatedImage
    (sa ta : Kernel.Name → (Kernel.Name → Nat) → AnnotTerm)
    (se te : Env) (sl tl : Kernel.Name → Nat) : Nat → Kernel.Expr → Kernel.Expr → Prop
  | bvar {d i} : AnnotatedImage sa ta se te sl tl d (.bvar i) (.bvar i)
  | sort {d s t} (level : s.eval sl = t.eval tl) :
      AnnotatedImage sa ta se te sl tl d (.sort s) (.sort t)
  | fvar {d i st tt} : AnnotatedImage sa ta se te sl tl d (.fvar i st) (.fvar i tt)
  | constant {d sn tn sus tus sci tci}
      (sourceLookup : se.find? sn = some sci) (targetLookup : te.find? tn = some tci)
      (sourceArity : sus.length = sci.toConstantVal.levelParams.length)
      (targetArity : tus.length = tci.toConstantVal.levelParams.length)
      (leaf : sa sn (Kernel.Level.substFn sl sci.toConstantVal.levelParams sus) =
        ta tn (Kernel.Level.substFn tl tci.toConstantVal.levelParams tus)) :
      AnnotatedImage sa ta se te sl tl d (.const sn sus) (.const tn tus)
  | app {d sf sx tf tx}
      (function : AnnotatedImage sa ta se te sl tl d sf tf)
      (argument : AnnotatedImage sa ta se te sl tl d sx tx) :
      AnnotatedImage sa ta se te sl tl d (.app sf sx) (.app tf tx)
  | lam {d st sb sm tt tb tm}
      (domain : AnnotatedImage sa ta se te sl tl d st tt)
      (opened : AnnotatedImage sa ta se te sl tl (d + 1)
        (sb.instantiate1 (.fvar d st)) (tb.instantiate1 (.fvar d tt)))
      (bits : pwBit sl sm.pw = pwBit tl tm.pw) :
      AnnotatedImage sa ta se te sl tl d (.lam st sb sm) (.lam tt tb tm)
  | forallE {d st sb sm tt tb tm}
      (domain : AnnotatedImage sa ta se te sl tl d st tt)
      (opened : AnnotatedImage sa ta se te sl tl (d + 1)
        (sb.instantiate1 (.fvar d st)) (tb.instantiate1 (.fvar d tt)))
      (bits : pwBit sl sm.pw = pwBit tl tm.pw) :
      AnnotatedImage sa ta se te sl tl d (.forallE st sb sm) (.forallE tt tb tm)
  | projTable {d sn si sx tn ti tx sp tp}
      (sourceTable : se.findProj? sn si = some sp)
      (targetTable : te.findProj? tn ti = some tp)
      (position : si + sp.off = ti + tp.off)
      (operand : AnnotatedImage sa ta se te sl tl d sx tx) :
      AnnotatedImage sa ta se te sl tl d (.proj sn si sx) (.proj tn ti tx)
  | projPair {d sn tn i sx tx}
      (sourceTable : se.findProj? sn i = none)
      (targetTable : te.findProj? tn i = none)
      (operand : AnnotatedImage sa ta se te sl tl d sx tx) :
      AnnotatedImage sa ta se te sl tl d (.proj sn i sx) (.proj tn i tx)
  | natLit {d n}
      (supported : natLitSupported se = natLitSupported te)
      (zero : sa natZeroName (Kernel.Level.substFn sl [] []) = ta natZeroName (Kernel.Level.substFn tl [] []))
      (succ : sa natSuccName (Kernel.Level.substFn sl [] []) = ta natSuccName (Kernel.Level.substFn tl [] [])) :
      AnnotatedImage sa ta se te sl tl d (.lit (.natVal n)) (.lit (.natVal n))
  | strLit {d s}
      (supported : strLitSupported se = strLitSupported te)
      (basis : ∀ n ∈ [natZeroName, natSuccName, charName, charOfNatName, stringOfListName],
        sa n (Kernel.Level.substFn sl [] []) = ta n (Kernel.Level.substFn tl [] []))
      (nil : sa listNilName (Kernel.Level.substFn sl (levelParamsAt se listNilName) [.zero]) =
        ta listNilName (Kernel.Level.substFn tl (levelParamsAt te listNilName) [.zero]))
      (cons : sa listConsName (Kernel.Level.substFn sl (levelParamsAt se listConsName) [.zero]) =
        ta listConsName (Kernel.Level.substFn tl (levelParamsAt te listConsName) [.zero])) :
      AnnotatedImage sa ta se te sl tl d (.lit (.strVal s)) (.lit (.strVal s))

theorem AnnotatedImage.reading {sa ta se te sl tl d s t}
    (image : AnnotatedImage sa ta se te sl tl d s t) :
    denoteMeta sa se sl d s = denoteMeta ta te tl d t := by
  induction image with
  | bvar => simp only [denoteMeta]
  | sort level => simp only [denoteMeta, level]
  | fvar => simp only [denoteMeta]
  | constant sourceLookup targetLookup sourceArity targetArity leaf =>
    simp only [denoteMeta, sourceLookup, targetLookup, sourceArity, targetArity, ↓reduceIte, leaf]
  | app _ _ ihf iha => simp only [denoteMeta, ihf, iha]
  | lam _ _ bits ihd ihb => simp only [denoteMeta, ihd, ihb, bits]
  | forallE _ _ bits ihd ihb => simp only [denoteMeta, ihd, ihb, bits]
  | projTable sourceTable targetTable position _ ih =>
    simp only [denoteMeta, ih, sourceTable, targetTable, position]
  | projPair sourceTable targetTable _ ih =>
    simp only [denoteMeta, ih, sourceTable, targetTable]
  | natLit supported zero succ => simp only [denoteMeta, supported, zero, succ]
  | strLit supported basis nil cons =>
    have zero := basis natZeroName (by simp)
    have succ := basis natSuccName (by simp)
    have char := basis charName (by simp)
    have ofNat := basis charOfNatName (by simp)
    have ofList := basis stringOfListName (by simp)
    simp only [denoteMeta, supported, zero, succ, char, ofNat, ofList, nil, cons]

/-- Transfer the strong-model currency on the exact target annotation object.
Neither an independently chosen source model nor equality of public values
can replace the annotated correspondence premise. -/
theorem AnnotatedImage.pullback {V : Type u} [SetTheory V]
    {sa ta se te sl tl d s t annotation} (image : AnnotatedImage sa ta se te sl tl d s t)
    (reading : denoteMeta ta te tl d t = some annotation) (ρ : Nat → V)
    (truthful : WellDenotedV V ρ annotation) :
    ∃ sourceAnnotation, denoteMeta sa se sl d s = some sourceAnnotation ∧
      sourceAnnotation = annotation ∧ AnnotValid V ρ sourceAnnotation ∧
      WellDenotedV V ρ sourceAnnotation := by
  exact ⟨annotation, image.reading.trans reading, rfl, truthful.2, truthful⟩

/-- The existing executable projection check supplies the exact table/fallback
part of the annotated relation; no equality of public values is used. -/
theorem checkInstalledProjection_annotated
    {sa ta se te sl tl d sn tn si ti sx tx} {names : Kernel.Name → Kernel.Name}
    (checked : checkInstalledProjection se te names sn tn si ti = true)
    (operand : AnnotatedImage sa ta se te sl tl d sx tx) :
    AnnotatedImage sa ta se te sl tl d (.proj sn si sx) (.proj tn ti tx) := by
  simp only [checkInstalledProjection, Bool.and_eq_true] at checked
  have position := checked.2
  cases sourceTable : se.findProj? sn si with
  | none =>
    cases targetTable : te.findProj? tn ti with
    | some entry => simp [sourceTable, targetTable] at position
    | none =>
      simp only [sourceTable, targetTable, decide_eq_true_eq] at position
      rcases position with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact .projPair sourceTable targetTable operand
      · exact .projPair sourceTable targetTable operand
  | some sourceEntry =>
    cases targetTable : te.findProj? tn ti with
    | none => simp [sourceTable, targetTable] at position
    | some targetEntry =>
      simp only [sourceTable, targetTable, decide_eq_true_eq] at position
      exact .projTable sourceTable targetTable position operand

theorem PullbackMap.fromEnvs_annotated_constant {V : Type u} [SetTheory V]
    {sourceEnv targetEnv : Env} (target : StrongInstalledModel V targetEnv)
    {names : Kernel.Name → Kernel.Name} (association : TelescopeAssociation sourceEnv targetEnv names)
    {name : Kernel.Name} {sourceEntry targetEntry : Kernel.ConstantInfo}
    (sourceLookup : sourceEnv.find? name = some sourceEntry)
    (targetLookup : targetEnv.find? (names name) = some targetEntry)
    (sourceLevels targetLevels : Kernel.Name → Nat) (sourceUs targetUs : List Kernel.Level)
    (sourceArity : sourceUs.length = sourceEntry.toConstantVal.levelParams.length)
    (targetArity : targetUs.length = targetEntry.toConstantVal.levelParams.length)
    (arguments : sourceUs.map (Kernel.Level.eval sourceLevels) = targetUs.map (Kernel.Level.eval targetLevels))
    (depth : Nat) :
    AnnotatedImage ((PullbackMap.fromEnvs sourceEnv targetEnv names).annotations target.internal.base2.acval)
      target.internal.base2.acval sourceEnv targetEnv sourceLevels targetLevels depth
      (.const name sourceUs) (.const (names name) targetUs) := by
  exact .constant sourceLookup targetLookup sourceArity targetArity
    (PullbackMap.fromEnvs_annotation_instance target association sourceLookup targetLookup
      sourceLevels targetLevels sourceUs targetUs sourceArity targetArity arguments)

private theorem evalEqList_map {φ : Kernel.Name → Nat} {left right : List Kernel.Level}
    (same : Kernel.Level.EvalEqList φ left right) :
    left.map (Kernel.Level.eval φ) = right.map (Kernel.Level.eval φ) := by
  induction left generalizing right with
  | nil => cases right <;> simp_all [Kernel.Level.EvalEqList]
  | cons x xs ih =>
    cases right with
    | nil => contradiction
    | cons y ys => simp only [List.map_cons, same.1, ih same.2]

/-- Successful universe comparison and checked member telescopes establish an
annotated constant image directly, including compatible many-to-one names. -/
theorem checkInstalledConstant_annotated {V : Type u} [SetTheory V]
    {sourceEnv targetEnv : Env} (target : StrongInstalledModel V targetEnv)
    {names : Kernel.Name → Kernel.Name} (association : TelescopeAssociation sourceEnv targetEnv names)
    (image : UniverseImage) (targetLevels : Kernel.Name → Nat)
    {sourceName targetName : Kernel.Name} {sourceUs targetUs : List Kernel.Level}
    (checked : checkInstalledConstant sourceEnv names image sourceName targetName sourceUs targetUs = some true)
    (depth : Nat) :
    AnnotatedImage ((PullbackMap.fromEnvs sourceEnv targetEnv names).annotations target.internal.base2.acval)
      target.internal.base2.acval sourceEnv targetEnv (image.valuation targetLevels) targetLevels depth
      (.const sourceName sourceUs) (.const targetName targetUs) := by
  cases lookup : sourceEnv.find? sourceName with
  | none => simp [checkInstalledConstant, lookup] at checked
  | some entry =>
    simp only [checkInstalledConstant, lookup] at checked
    split at checked
    · rename_i conditions
      obtain ⟨rfl, arity⟩ := conditions
      obtain ⟨targetEntry, targetLookup, _, _, sameArity⟩ := association sourceName entry lookup
      have meanings := evalEqList_map (Kernel.Level.isEquivList_sound checked targetLevels)
      have evaluated : sourceUs.map (Kernel.Level.eval (image.valuation targetLevels)) =
          targetUs.map (Kernel.Level.eval targetLevels) := by
        simpa only [List.map_map, Function.comp_def, UniverseImage.eval] using meanings
      have lengths := congrArg List.length evaluated
      simp only [List.length_map] at lengths
      exact PullbackMap.fromEnvs_annotated_constant target association lookup targetLookup
        (image.valuation targetLevels) targetLevels sourceUs targetUs arity
        (by omega) evaluated depth
    · contradiction

/-- The pulled leaves already carry both halves of the strong truthfulness
currency, even before any source environment model has been constructed. -/
theorem PullbackMap.annotations_wellDenotedV {V : Type u} [SetTheory V]
    {env : Env} (target : StrongInstalledModel V env) (map : PullbackMap)
    (name : Kernel.Name) (levels : Kernel.Name → Nat) (ρ : Nat → V) :
    WellDenotedV V ρ (map.annotations target.internal.base2.acval name levels) := by
  exact ⟨target.internal.base2.acval_wellDenoted _ _ _, target.internal.acval_validV _ _ _⟩

/-- Source parameter locality is discharged from the checked telescopes and
the actual target annotated model, rather than an assumed source model. -/
theorem PullbackMap.annotations_params {V : Type u} [SetTheory V]
    {sourceEnv targetEnv : Env} (target : StrongInstalledModel V targetEnv)
    {names : Kernel.Name → Kernel.Name} (association : TelescopeAssociation sourceEnv targetEnv names)
    {name : Kernel.Name} {entry : Kernel.ConstantInfo} (lookup : sourceEnv.find? name = some entry)
    (first second : Kernel.Name → Nat)
    (agree : ∀ parameter ∈ entry.toConstantVal.levelParams, first parameter = second parameter) :
    (PullbackMap.fromEnvs sourceEnv targetEnv names).annotations target.internal.base2.acval name first =
      (PullbackMap.fromEnvs sourceEnv targetEnv names).annotations target.internal.base2.acval name second := by
  obtain ⟨targetEntry, targetLookup, locality⟩ := PullbackMap.fromEnvs_locality association name entry lookup
  exact target.internal.base2.acval_params _ targetEntry targetLookup _ _ (locality first second agree)

/-- Actual stored target type grading and membership transfer to the source
type reading under the same pulled annotated leaves. The remaining premise
is the annotated type image; independent source installation cannot supply it.
This discharges the reading, grading and membership fields together. -/
theorem installed_type_annotated_pullback {V : Type u} [SetTheory V]
    {sourceEnv targetEnv : Env} (target : StrongInstalledModel V targetEnv)
    (names : Kernel.Name → Kernel.Name) {name : Kernel.Name}
    {sourceEntry targetEntry : Kernel.ConstantInfo}
    (sourceLookup : sourceEnv.find? name = some sourceEntry)
    (targetLookup : targetEnv.find? (names name) = some targetEntry)
    (levels : Kernel.Name → Nat)
    (image : AnnotatedImage
      ((PullbackMap.fromEnvs sourceEnv targetEnv names).annotations target.internal.base2.acval)
      target.internal.base2.acval sourceEnv targetEnv levels
      ((PullbackMap.fromEnvs sourceEnv targetEnv names).levels name levels) 0
      sourceEntry.toConstantVal.type targetEntry.toConstantVal.type) :
    ∃ annotation,
      denoteMeta ((PullbackMap.fromEnvs sourceEnv targetEnv names).annotations target.internal.base2.acval)
        sourceEnv levels 0 sourceEntry.toConstantVal.type = some annotation ∧
      (∀ ρ : Nat → V, WellDenotedV V ρ annotation) ∧
      (∀ ρ : Nat → V, interp V ρ
        ((PullbackMap.fromEnvs sourceEnv targetEnv names).annotations target.internal.base2.acval
          sourceEntry.name levels) ∈ˢ interp V ρ annotation) := by
  have member := Kernel.Semantics.Env.find?_mem targetLookup
  obtain ⟨annotation, reading⟩ := target.internal.type_reads targetEntry member
    ((PullbackMap.fromEnvs sourceEnv targetEnv names).levels name levels)
  refine ⟨annotation, image.reading.trans reading,
    target.internal.type_wellDenotedV targetEntry member _ annotation reading, ?_⟩
  intro ρ
  have membership := target.internal.mem_type targetEntry member _ annotation reading ρ
  have sourceName := Kernel.Semantics.Env.find?_name sourceLookup
  have targetName := Kernel.Semantics.Env.find?_name targetLookup
  simpa only [sourceName, PullbackMap.annotations, PullbackMap.fromEnvs, targetName] using membership

end Ix.CompileCert
