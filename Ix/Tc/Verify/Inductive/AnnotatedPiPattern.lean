import Ix.Tc.Verify.Inductive.IotaPattern
import Ix.Tc.Verify.Inductive.AnnotatedPiRecursorFixture

/-!
# Annotation-normalizing recursive-Pi iota pattern

The generated `AnnotatedPi.mk` equation is the smallest recursive-Pi rule
whose stored constructor field retains reducible annotation syntax.  The
recursor itself has only a motive and one minor premise before its major, and
the constructor has one function field.  Consequently there are no uniform
parameter or result-index comparisons to encode in the production pattern.

As for the more general recursive-Pi fixture, the pattern language has no
lambda constructor.  We therefore retain the exact closed generated RHS and
apply it to the motive, minor premise, and constructor field captures.  The
soundness proof beta-reduces that application to the registered equation.
-/

namespace Ix.Tc.AnnotatedPiPattern

open Lean4Lean
open Lean4Lean.InductiveFixtures
open AnnotatedPiCertificateFixture
open AnnotatedPiFixture
open AnnotatedPiRecursorFixture

private abbrev generation := transaction.certificate.generation

def recursorName : Lean.Name := ``AnnotatedPi.rec

private def recursorArgumentRhs (index : Fin 2) :
    (RecursorIotaPattern recursorName 2 ``AnnotatedPi.mk 1).RHS :=
  RecursorIotaPattern.recursorArgumentRhs recursorName 2 ``AnnotatedPi.mk 1
    index

private def constructorArgumentRhs (index : Fin 1) :
    (RecursorIotaPattern recursorName 2 ``AnnotatedPi.mk 1).RHS :=
  RecursorIotaPattern.constructorArgumentRhs recursorName 2
    ``AnnotatedPi.mk 1 index

/-- Application-spine constructor for the dependent pattern RHS language. -/
def rhsAppN {pattern : Pattern} : pattern.RHS -> List pattern.RHS ->
    pattern.RHS
  | head, [] => head
  | head, argument :: rest => rhsAppN (.app head argument) rest

@[simp] theorem rhsAppN_apply {pattern : Pattern} (head : pattern.RHS)
    (arguments : List pattern.RHS) (levels : List VLevel)
    (captures : pattern.Path -> VExpr) :
    (rhsAppN head arguments).apply levels captures =
      VExpr.appN (head.apply levels captures)
        (arguments.map (Pattern.RHS.apply levels captures)) := by
  induction arguments generalizing head with
  | nil => rfl
  | cons argument rest ih =>
      simp only [rhsAppN, ih, Pattern.RHS.apply, List.map_cons, VExpr.appN]

private theorem generatedRhsClosed :
    (generation.rule 0 mkNormalized).rhs.Closed :=
  (mkGeneratedRuleWF.2.closedN transaction.facts.afterWF.ordered
    (by trivial))

/-- Exact registered equation RHS applied to the three production captures. -/
def rhs : (RecursorIotaPattern recursorName 2 ``AnnotatedPi.mk 1).RHS :=
  rhsAppN
    (.fixed (generation.rule 0 mkNormalized).rhs generatedRhsClosed)
    [ recursorArgumentRhs ⟨0, by omega⟩,
      recursorArgumentRhs ⟨1, by omega⟩,
      constructorArgumentRhs ⟨0, by omega⟩ ]

/-- Compiled production iota pattern for `AnnotatedPi.mk`. -/
def pattern (constructorId : KId .anon) : RecursorRulePattern where
  recursorName := recursorName
  constructorId := constructorId
  constructorName := ``AnnotatedPi.mk
  constructorParams := 0
  constructorFields := 1
  ruleIndex := 0
  majorIdx := 2
  rhs := rhs
  checks := .true

@[simp] theorem pattern_rhs_apply (constructorId : KId .anon)
    (u : VLevel)
    (captures : (RecursorIotaPattern ``AnnotatedPi.rec 2
      ``AnnotatedPi.mk 1).Path -> VExpr) :
    (pattern constructorId).rhs.apply [u] captures =
      VExpr.appN ((generation.rule 0 mkNormalized).rhs.instL [u])
        [ captures (RecursorIotaPattern.recursorArgumentPath
            ``AnnotatedPi.rec 2 ``AnnotatedPi.mk 1 ⟨0, by omega⟩),
          captures (RecursorIotaPattern.recursorArgumentPath
            ``AnnotatedPi.rec 2 ``AnnotatedPi.mk 1 ⟨1, by omega⟩),
          captures (RecursorIotaPattern.constructorArgumentPath
            ``AnnotatedPi.rec 2 ``AnnotatedPi.mk 1 ⟨0, by omega⟩) ] := by
  simp [pattern, rhs, rhsAppN_apply, recursorName, recursorArgumentRhs,
    constructorArgumentRhs, Pattern.RHS.apply]

/-! ## Exact finite metadata -/

theorem constructorAt : mkConcrete.ConstructorAt 0 0 1 := by
  cases concreteEq : mkConcrete with
  | ctor name levelParams isUnsafe levels induct cidx params fields type =>
      have shape := mkShape
      rw [concreteEq] at shape
      simp only [KConst.IsCertifiedSingletonConstructor] at shape
      simp only [KConst.ConstructorAt]
      refine ⟨shape.2.2.1, ?_, ?_⟩
      · apply UInt64.toNat_inj.mp
        have hparams : annotatedPiRawDecl.nparams = 0 := rfl
        rw [hparams] at shape
        simpa only [show (0 : UInt64).toNat = 0 from rfl] using
          shape.2.2.2.1
      · apply UInt64.toNat_inj.mp
        have hfields :
            (VInductDecl.ctorFields
              (VExpr.dropN annotatedPiRawDecl.nparams mkSource.type)).length =
                1 := rfl
        rw [hfields] at shape
        simpa only [show (1 : UInt64).toNat = 1 from rfl] using
          shape.2.2.2.2
  | _ =>
      have shape := mkShape
      rw [concreteEq] at shape
      simp [KConst.IsCertifiedSingletonConstructor] at shape

theorem majorIndex : recursorConcrete.RecursorMajorIdx = some 2 := by
  cases concreteEq : recursorConcrete with
  | recr name levelParams k isUnsafe levels params indices motives minors
      block memberIdx type rules leanAll =>
      have shape := recursorShape
      rw [concreteEq] at shape
      simp only [KConst.IsCertifiedSingletonRecursor] at shape
      simp only [KConst.RecursorMajorIdx]
      have hparams : annotatedPiRawDecl.nparams = 0 := rfl
      have hindices : generation.block.rawIndices.length = 0 := rfl
      rw [show params = 0 by
          apply UInt64.toNat_inj.mp
          rw [hparams] at shape
          simpa using shape.2.1,
        show motives = 1 by
          apply UInt64.toNat_inj.mp
          simpa using shape.2.2.2.1,
        show minors = 1 by
          apply UInt64.toNat_inj.mp
          simpa [constructorIds] using shape.2.2.2.2.1,
        show indices = 0 by
          apply UInt64.toNat_inj.mp
          rw [hindices] at shape
          simpa using shape.2.2.1]
      rfl
  | _ =>
      have shape := recursorShape
      rw [concreteEq] at shape
      simp [KConst.IsCertifiedSingletonRecursor] at shape

@[simp] private theorem mkFieldCount :
    (mkNormalized.fieldsR annotatedPiRawDecl.uvars
      annotatedPiRawDecl.nparams).length = 1 := rfl

theorem metadata {rule : RecRule .anon}
    (hrule : recursorConcrete.RecursorRuleAt 0 rule) :
    RawRecursorRulePatternMetadataRel AnnotatedPiRecursorFixture.catalog
      AnnotatedPiRecursorFixture.nameOf recursorId
      recursorConcrete rule (pattern mkId) := by
  refine {
    recursorName := by simpa [pattern, recursorName] using nameOf_recursor
    majorIdx := by simpa [pattern] using majorIndex
    majorIdxCoherent := recursorShape.coherent
    ruleAt := hrule
    constructorName := by
      simpa [pattern] using AnnotatedPiRecursorFixture.nameOf_mk
    constructorAt := ⟨mkConcrete, by
        simpa [pattern] using AnnotatedPiRecursorFixture.catalog_mk,
      by simpa [pattern] using constructorAt⟩
    fields := ?_ }
  obtain ⟨normalized, hnormalized, _, hfields, _, _⟩ :=
    recursorLink.ruleAt hrule
  have hnormalizedEq : normalized = mkNormalized := by
    rw [mkNormalizedAt] at hnormalized
    exact (Option.some.inj hnormalized).symm
  subst normalized
  apply UInt64.toNat_inj.mp
  simpa only [pattern, mkFieldCount,
    show (1 : UInt64).toNat = 1 from rfl] using hfields

end Ix.Tc.AnnotatedPiPattern
