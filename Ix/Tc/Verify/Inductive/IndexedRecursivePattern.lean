import Ix.Tc.Verify.Inductive.IndexedRecursiveCertificate
import Ix.Tc.Verify.Inductive.IotaPattern

/-!
# Generated iota patterns for the indexed recursive fixture

This module compiles the two exact `IndexedVec.rec` equations into the same
`SimplePattern.iota` vocabulary consumed by production WHNF.  The `cons`
pattern is deliberately nontrivial: its RHS applies the selected minor to
three fields and constructs the recursive call at the predecessor index from
captured recursor and constructor arguments.
-/

namespace Ix.Tc.IndexedRecursivePattern

open Lean4Lean
open Lean4Lean.InductiveFixtures
open Lean4Lean.InductiveReplayFixtures
open IndexedRecursiveCertificateFixture

def recursorName : Lean.Name := ``IndexedVec.rec

@[simp] private theorem certifiedRecursorName :
    (.str transaction.certificate.generation.block.sourceType.name "rec") =
      recursorName := rfl

@[simp] private theorem sourceParameterCount : indexedVecDecl.nparams = 1 := rfl

@[simp] private theorem nilFieldCount :
    (transaction.certificate.generation.block.ctorPairs[0].fieldsR
      indexedVecDecl.uvars indexedVecDecl.nparams).length = 0 := rfl

@[simp] private theorem consFieldCount :
    (transaction.certificate.generation.block.ctorPairs[1].fieldsR
      indexedVecDecl.uvars indexedVecDecl.nparams).length = 3 := rfl

@[simp] private theorem nilRawFieldCount :
    (VInductDecl.ctorFields
      (VExpr.dropN indexedVecDecl.nparams indexedVecType.ctors[0].type)).length =
        0 := rfl

@[simp] private theorem consRawFieldCount :
    (VInductDecl.ctorFields
      (VExpr.dropN indexedVecDecl.nparams indexedVecType.ctors[1].type)).length =
        3 := rfl

@[simp] private theorem nilConstructorName :
    indexedVecType.ctors[0].name = ``IndexedVec.nil := rfl

@[simp] private theorem consConstructorName :
    indexedVecType.ctors[1].name = ``IndexedVec.cons := rfl

private def nilRecursorArgumentRhs (index : Fin 5) :
    (RecursorIotaPattern recursorName 5 ``IndexedVec.nil 1).RHS :=
  RecursorIotaPattern.recursorArgumentRhs recursorName 5
    ``IndexedVec.nil 1 index

private def nilConstructorArgumentRhs (index : Fin 1) :
    (RecursorIotaPattern recursorName 5 ``IndexedVec.nil 1).RHS :=
  RecursorIotaPattern.constructorArgumentRhs recursorName 5
    ``IndexedVec.nil 1 index

/-- The two dependent equalities required before the null rule may fire:
the constructor uses the recursor's uniform parameter and its result index is
`Nat.zero`.  These are semantic checks, not trusted syntactic rewrites. -/
def nilChecks :
    (RecursorIotaPattern recursorName 5 ``IndexedVec.nil 1).Check :=
  .defeq (nilRecursorArgumentRhs ⟨0, by omega⟩)
    (nilConstructorArgumentRhs ⟨0, by omega⟩)
    (.defeq (nilRecursorArgumentRhs ⟨4, by omega⟩)
      (.fixed (.const ``Nat.zero []) (by trivial)) .true)

private def consRecursorArgumentRhs (index : Fin 5) :
    (RecursorIotaPattern recursorName 5 ``IndexedVec.cons 4).RHS :=
  RecursorIotaPattern.recursorArgumentRhs recursorName 5
    ``IndexedVec.cons 4 index

private def consConstructorArgumentRhs (index : Fin 4) :
    (RecursorIotaPattern recursorName 5 ``IndexedVec.cons 4).RHS :=
  RecursorIotaPattern.constructorArgumentRhs recursorName 5
    ``IndexedVec.cons 4 index

/-- The two dependent equalities required before the recursive rule may fire:
the uniform parameter agrees and the recursor index is the successor of the
constructor's predecessor index. -/
def consChecks :
    (RecursorIotaPattern recursorName 5 ``IndexedVec.cons 4).Check :=
  .defeq (consRecursorArgumentRhs ⟨0, by omega⟩)
    (consConstructorArgumentRhs ⟨0, by omega⟩)
    (.defeq (consRecursorArgumentRhs ⟨4, by omega⟩)
      (.app (.fixed (.const ``Nat.succ []) (by trivial))
        (consConstructorArgumentRhs ⟨1, by omega⟩)) .true)

/-- Application-spine constructor in the dependent pattern RHS language. -/
def rhsAppN {pattern : Pattern} : pattern.RHS → List pattern.RHS → pattern.RHS
  | head, [] => head
  | head, argument :: rest => rhsAppN (.app head argument) rest

@[simp] theorem rhsAppN_apply {pattern : Pattern} (head : pattern.RHS)
    (arguments : List pattern.RHS) (levels : List VLevel)
    (captures : pattern.Path → VExpr) :
    (rhsAppN head arguments).apply levels captures =
      VExpr.appN (head.apply levels captures)
        (arguments.map (Pattern.RHS.apply levels captures)) := by
  induction arguments generalizing head with
  | nil => rfl
  | cons argument rest ih =>
      simp only [rhsAppN, ih, Pattern.RHS.apply, List.map_cons,
        VExpr.appN]

/-- The null constructor selects the first minor. -/
def nilPattern (constructorId : KId .anon) : RecursorRulePattern where
  recursorName := recursorName
  constructorId := constructorId
  constructorName := ``IndexedVec.nil
  constructorParams := 1
  constructorFields := 0
  ruleIndex := 0
  majorIdx := 5
  rhs := RecursorIotaPattern.recursorArgumentRhs recursorName 5
    ``IndexedVec.nil 1 ⟨2, by omega⟩
  checks := nilChecks

/-- The recursive call appearing in the `cons` equation:
`IndexedVec.rec α motive nil cons n as`. -/
def consRecursiveCall :
    (RecursorIotaPattern recursorName 5 ``IndexedVec.cons 4).RHS :=
  rhsAppN
    (.fixed (.const recursorName (VLevel.params 2)) (by trivial))
    [ RecursorIotaPattern.recursorArgumentRhs recursorName 5
        ``IndexedVec.cons 4 ⟨0, by omega⟩,
      RecursorIotaPattern.recursorArgumentRhs recursorName 5
        ``IndexedVec.cons 4 ⟨1, by omega⟩,
      RecursorIotaPattern.recursorArgumentRhs recursorName 5
        ``IndexedVec.cons 4 ⟨2, by omega⟩,
      RecursorIotaPattern.recursorArgumentRhs recursorName 5
        ``IndexedVec.cons 4 ⟨3, by omega⟩,
      RecursorIotaPattern.constructorArgumentRhs recursorName 5
        ``IndexedVec.cons 4 ⟨1, by omega⟩,
      RecursorIotaPattern.constructorArgumentRhs recursorName 5
        ``IndexedVec.cons 4 ⟨3, by omega⟩ ]

/-- The successor constructor's generated RHS:
`consMinor n a as (IndexedVec.rec α motive nil cons n as)`. -/
def consRhs :
    (RecursorIotaPattern recursorName 5 ``IndexedVec.cons 4).RHS :=
  rhsAppN
    (RecursorIotaPattern.recursorArgumentRhs recursorName 5
      ``IndexedVec.cons 4 ⟨3, by omega⟩)
    [ RecursorIotaPattern.constructorArgumentRhs recursorName 5
        ``IndexedVec.cons 4 ⟨1, by omega⟩,
      RecursorIotaPattern.constructorArgumentRhs recursorName 5
        ``IndexedVec.cons 4 ⟨2, by omega⟩,
      RecursorIotaPattern.constructorArgumentRhs recursorName 5
        ``IndexedVec.cons 4 ⟨3, by omega⟩,
      consRecursiveCall ]

/-- Compiled production pattern for the indexed recursive constructor. -/
def consPattern (constructorId : KId .anon) : RecursorRulePattern where
  recursorName := recursorName
  constructorId := constructorId
  constructorName := ``IndexedVec.cons
  constructorParams := 1
  constructorFields := 3
  ruleIndex := 1
  majorIdx := 5
  rhs := consRhs
  checks := consChecks

@[simp] theorem nilPattern_rhs_apply (constructorId : KId .anon)
    (levels : List VLevel)
    (captures : (RecursorIotaPattern ``IndexedVec.rec 5 ``IndexedVec.nil 1).Path →
      VExpr) :
    (nilPattern constructorId).rhs.apply levels captures =
      captures (RecursorIotaPattern.recursorArgumentPath ``IndexedVec.rec 5
        ``IndexedVec.nil 1 ⟨2, by omega⟩) := by
  rfl

@[simp] theorem consPattern_rhs_apply (constructorId : KId .anon)
    (v u : VLevel)
    (captures : (RecursorIotaPattern ``IndexedVec.rec 5 ``IndexedVec.cons 4).Path →
      VExpr) :
    (consPattern constructorId).rhs.apply [v, u] captures =
      VExpr.appN
        (captures (RecursorIotaPattern.recursorArgumentPath ``IndexedVec.rec 5
          ``IndexedVec.cons 4 ⟨3, by omega⟩))
        [ captures (RecursorIotaPattern.constructorArgumentPath
            ``IndexedVec.rec 5 ``IndexedVec.cons 4 ⟨1, by omega⟩),
          captures (RecursorIotaPattern.constructorArgumentPath
            ``IndexedVec.rec 5 ``IndexedVec.cons 4 ⟨2, by omega⟩),
          captures (RecursorIotaPattern.constructorArgumentPath
            ``IndexedVec.rec 5 ``IndexedVec.cons 4 ⟨3, by omega⟩),
          VExpr.appN (.const ``IndexedVec.rec [v, u])
            [ captures (RecursorIotaPattern.recursorArgumentPath
                ``IndexedVec.rec 5 ``IndexedVec.cons 4 ⟨0, by omega⟩),
              captures (RecursorIotaPattern.recursorArgumentPath
                ``IndexedVec.rec 5 ``IndexedVec.cons 4 ⟨1, by omega⟩),
              captures (RecursorIotaPattern.recursorArgumentPath
                ``IndexedVec.rec 5 ``IndexedVec.cons 4 ⟨2, by omega⟩),
              captures (RecursorIotaPattern.recursorArgumentPath
                ``IndexedVec.rec 5 ``IndexedVec.cons 4 ⟨3, by omega⟩),
              captures (RecursorIotaPattern.constructorArgumentPath
                ``IndexedVec.rec 5 ``IndexedVec.cons 4 ⟨1, by omega⟩),
              captures (RecursorIotaPattern.constructorArgumentPath
                ``IndexedVec.rec 5 ``IndexedVec.cons 4 ⟨3, by omega⟩) ] ] := by
  simp [consPattern, consRhs, consRecursiveCall, recursorName,
    Pattern.RHS.apply, VExpr.instL, VLevel.inst_map_id]

/-- Semantic content of the null pattern's two dependent checks. -/
theorem nilChecks_ok
    (defeq : VExpr → VExpr → Prop) (levels : List VLevel)
    (captures : (RecursorIotaPattern ``IndexedVec.rec 5 ``IndexedVec.nil 1).Path →
      VExpr)
    (h : nilChecks.OK defeq levels captures) :
    defeq
        (captures (RecursorIotaPattern.recursorArgumentPath ``IndexedVec.rec 5
          ``IndexedVec.nil 1 ⟨0, by omega⟩))
        (captures (RecursorIotaPattern.constructorArgumentPath ``IndexedVec.rec 5
          ``IndexedVec.nil 1 ⟨0, by omega⟩)) ∧
      defeq
        (captures (RecursorIotaPattern.recursorArgumentPath ``IndexedVec.rec 5
          ``IndexedVec.nil 1 ⟨4, by omega⟩))
        (.const ``Nat.zero []) := by
  simpa [recursorName, nilChecks, nilRecursorArgumentRhs,
    nilConstructorArgumentRhs,
    Pattern.Check.OK, RecursorIotaPattern.recursorArgumentRhs,
    RecursorIotaPattern.constructorArgumentRhs, Pattern.RHS.apply,
    VExpr.instL] using h

/-- Semantic content of the recursive pattern's uniform-parameter and
successor-index checks. -/
theorem consChecks_ok
    (defeq : VExpr → VExpr → Prop) (levels : List VLevel)
    (captures : (RecursorIotaPattern ``IndexedVec.rec 5 ``IndexedVec.cons 4).Path →
      VExpr)
    (h : consChecks.OK defeq levels captures) :
    defeq
        (captures (RecursorIotaPattern.recursorArgumentPath ``IndexedVec.rec 5
          ``IndexedVec.cons 4 ⟨0, by omega⟩))
        (captures (RecursorIotaPattern.constructorArgumentPath ``IndexedVec.rec 5
          ``IndexedVec.cons 4 ⟨0, by omega⟩)) ∧
      defeq
        (captures (RecursorIotaPattern.recursorArgumentPath ``IndexedVec.rec 5
          ``IndexedVec.cons 4 ⟨4, by omega⟩))
        (.app (.const ``Nat.succ [])
          (captures (RecursorIotaPattern.constructorArgumentPath ``IndexedVec.rec 5
            ``IndexedVec.cons 4 ⟨1, by omega⟩))) := by
  simpa [recursorName, consChecks, consRecursorArgumentRhs,
    consConstructorArgumentRhs,
    Pattern.Check.OK, RecursorIotaPattern.recursorArgumentRhs,
    RecursorIotaPattern.constructorArgumentRhs, Pattern.RHS.apply,
    VExpr.instL] using h

/-- The certified family has exactly the two physical constructor slots used
by the patterns above. -/
theorem constructorCount
    {trProj : RawProjRel} {catalog : Catalog}
    {nameOf : Address → Option Lean.Name} {trusted : KId .anon → Prop}
    (family : SingletonFamilyCatalogLink trProj catalog nameOf trusted
      transaction) : family.constructorIds.size = 2 := by
  rw [family.constructorCount]
  rfl

/-- Production's ordinary iota path selects argument five: one parameter,
one motive, two minors, and one index precede the major. -/
theorem majorIndex
    {trProj : RawProjRel} {catalog : Catalog}
    {nameOf : Address → Option Lean.Name} {trusted : KId .anon → Prop}
    {family : SingletonFamilyCatalogLink trProj catalog nameOf trusted
      transaction}
    (link : SingletonRecursorCatalogLink trProj catalog nameOf trusted
      transaction family) :
    link.recursorConcrete.RecursorMajorIdx = some 5 := by
  cases concreteEq : link.recursorConcrete with
  | recr name levelParams k isUnsafe levels params indices motives minors
      block memberIdx type rules leanAll =>
      have shape := link.recursorShape
      rw [concreteEq] at shape
      simp only [KConst.IsCertifiedSingletonRecursor] at shape
      simp only [KConst.RecursorMajorIdx]
      rw [shape.2.2.2.2.2.2.2.1]
      have hconstructors := constructorCount family
      rw [shape.2.1, shape.2.2.1, shape.2.2.2.1,
        shape.2.2.2.2.1, hconstructors]
      rfl
  | _ =>
      have shape := link.recursorShape
      rw [concreteEq] at shape
      simp [KConst.IsCertifiedSingletonRecursor] at shape

/-- Resolve the certified null constructor to production slot zero with its
exact one-parameter/zero-field layout. -/
theorem nilConstructorAt
    {trProj : RawProjRel} {catalog : Catalog}
    {nameOf : Address → Option Lean.Name} {trusted : KId .anon → Prop}
    (family : SingletonFamilyCatalogLink trProj catalog nameOf trusted
      transaction) (hzero : 0 < family.constructorIds.size) :
    ∃ concrete,
      catalog (family.constructorIds[0]'hzero) = some concrete ∧
      concrete.ConstructorAt 0 1 0 ∧
      nameOf (family.constructorIds[0]'hzero).addr =
        some ``IndexedVec.nil := by
  obtain ⟨sourceConstructor, concrete, hsource, hcatalog, hconcrete,
    hname, _⟩ := family.constructor 0 hzero
  have hsourceEq : sourceConstructor = indexedVecType.ctors[0] := by
    apply Option.some.inj
    exact hsource.symm.trans rfl
  subst sourceConstructor
  refine ⟨concrete, hcatalog, ?_, by
    simpa only [nilConstructorName] using hname⟩
  cases concrete with
  | ctor name levelParams isUnsafe levels induct cidx params fields type =>
      simp only [KConst.IsCertifiedSingletonConstructor] at hconcrete
      simp only [KConst.ConstructorAt]
      refine ⟨hconcrete.2.2.1, ?_, ?_⟩
      · apply UInt64.toNat_inj.mp
        simpa only [sourceParameterCount,
          show (1 : UInt64).toNat = 1 from rfl] using
            hconcrete.2.2.2.1
      · apply UInt64.toNat_inj.mp
        simpa only [nilRawFieldCount,
          show (0 : UInt64).toNat = 0 from rfl] using
            hconcrete.2.2.2.2
  | _ => simp [KConst.IsCertifiedSingletonConstructor] at hconcrete

/-- Resolve the certified recursive constructor to production slot one with
its exact one-parameter/three-field layout. -/
theorem consConstructorAt
    {trProj : RawProjRel} {catalog : Catalog}
    {nameOf : Address → Option Lean.Name} {trusted : KId .anon → Prop}
    (family : SingletonFamilyCatalogLink trProj catalog nameOf trusted
      transaction) (hone : 1 < family.constructorIds.size) :
    ∃ concrete,
      catalog (family.constructorIds[1]'hone) = some concrete ∧
      concrete.ConstructorAt 1 1 3 ∧
      nameOf (family.constructorIds[1]'hone).addr =
        some ``IndexedVec.cons := by
  obtain ⟨sourceConstructor, concrete, hsource, hcatalog, hconcrete,
    hname, _⟩ := family.constructor 1 hone
  have hsourceEq : sourceConstructor = indexedVecType.ctors[1] := by
    apply Option.some.inj
    exact hsource.symm.trans rfl
  subst sourceConstructor
  refine ⟨concrete, hcatalog, ?_, by
    simpa only [consConstructorName] using hname⟩
  cases concrete with
  | ctor name levelParams isUnsafe levels induct cidx params fields type =>
      simp only [KConst.IsCertifiedSingletonConstructor] at hconcrete
      simp only [KConst.ConstructorAt]
      refine ⟨hconcrete.2.2.1, ?_, ?_⟩
      · apply UInt64.toNat_inj.mp
        simpa only [sourceParameterCount,
          show (1 : UInt64).toNat = 1 from rfl] using
            hconcrete.2.2.2.1
      · apply UInt64.toNat_inj.mp
        simpa only [consRawFieldCount,
          show (3 : UInt64).toNat = 3 from rfl] using
            hconcrete.2.2.2.2
  | _ => simp [KConst.IsCertifiedSingletonConstructor] at hconcrete

/-- Exact finite production metadata for the null generated rule. -/
theorem nilPatternMetadata
    {trProj : RawProjRel} {catalog : Catalog}
    {nameOf : Address → Option Lean.Name} {trusted : KId .anon → Prop}
    {family : SingletonFamilyCatalogLink trProj catalog nameOf trusted
      transaction}
    (link : SingletonRecursorCatalogLink trProj catalog nameOf trusted
      transaction family) {rule : RecRule .anon}
    (hzero : 0 < family.constructorIds.size)
    (hrule : link.recursorConcrete.RecursorRuleAt 0 rule) :
    RawRecursorRulePatternMetadataRel catalog nameOf link.recursorId
      link.recursorConcrete rule
        (nilPattern (family.constructorIds[0]'hzero)) := by
  obtain ⟨normalized, hnormalized, _, hfields, _, _⟩ := link.ruleAt hrule
  have hnormalizedEq :
      normalized = transaction.certificate.generation.block.ctorPairs[0] := by
    apply Option.some.inj
    exact hnormalized.symm.trans rfl
  subst normalized
  obtain ⟨constructor, hcatalog, hconstructorAt, hname⟩ :=
    nilConstructorAt family hzero
  refine {
    recursorName := by
      simpa only [nilPattern, certifiedRecursorName] using link.recursorName
    majorIdx := by simpa [nilPattern] using majorIndex link
    majorIdxCoherent := link.recursorShape.coherent
    ruleAt := hrule
    constructorName := by simpa [nilPattern] using hname
    constructorAt := ⟨constructor, by simpa [nilPattern] using hcatalog,
      by simpa [nilPattern] using hconstructorAt⟩
    fields := ?_ }
  apply UInt64.toNat_inj.mp
  simpa only [nilPattern, nilFieldCount,
    show (0 : UInt64).toNat = 0 from rfl] using hfields

/-- Exact finite production metadata for the recursive generated rule. -/
theorem consPatternMetadata
    {trProj : RawProjRel} {catalog : Catalog}
    {nameOf : Address → Option Lean.Name} {trusted : KId .anon → Prop}
    {family : SingletonFamilyCatalogLink trProj catalog nameOf trusted
      transaction}
    (link : SingletonRecursorCatalogLink trProj catalog nameOf trusted
      transaction family) {rule : RecRule .anon}
    (hone : 1 < family.constructorIds.size)
    (hrule : link.recursorConcrete.RecursorRuleAt 1 rule) :
    RawRecursorRulePatternMetadataRel catalog nameOf link.recursorId
      link.recursorConcrete rule
        (consPattern (family.constructorIds[1]'hone)) := by
  obtain ⟨normalized, hnormalized, _, hfields, _, _⟩ := link.ruleAt hrule
  have hnormalizedEq :
      normalized = transaction.certificate.generation.block.ctorPairs[1] := by
    apply Option.some.inj
    exact hnormalized.symm.trans rfl
  subst normalized
  obtain ⟨constructor, hcatalog, hconstructorAt, hname⟩ :=
    consConstructorAt family hone
  refine {
    recursorName := by
      simpa only [consPattern, certifiedRecursorName] using link.recursorName
    majorIdx := by simpa [consPattern] using majorIndex link
    majorIdxCoherent := link.recursorShape.coherent
    ruleAt := hrule
    constructorName := by simpa [consPattern] using hname
    constructorAt := ⟨constructor, by simpa [consPattern] using hcatalog,
      by simpa [consPattern] using hconstructorAt⟩
    fields := ?_ }
  apply UInt64.toNat_inj.mp
  simpa only [consPattern, consFieldCount,
    show (3 : UInt64).toNat = 3 from rfl] using hfields

end Ix.Tc.IndexedRecursivePattern
