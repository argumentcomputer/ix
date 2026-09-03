import Ix.Tc.Verify.Inductive.IotaPattern
import Ix.Tc.Verify.Inductive.RecursivePiRecursorFixture

/-!
# Recursive-Pi iota pattern

The generated `Acc.intro` equation is the first supported iota rule whose
recursive call occurs beneath a function telescope.  Lean4Lean's pattern RHS
language intentionally contains only closed constants, applications, and
captures; it has no primitive lambda constructor.  We retain exact alignment
with the registered equation by using its complete closed RHS lambda as a
fixed template and applying that template to the six captured rule binders.
Beta reduction of that application constructs the two-binder induction
hypothesis without adding an unverified pattern-language extension.
-/

namespace Ix.Tc.RecursivePiPattern

open Lean4Lean
open Lean4Lean.InductiveFixtures
open RecursivePiCertificateFixture
open RecursivePiRecursorFixture

private abbrev generation := transaction.certificate.generation

def recursorName : Lean.Name := ``Acc.rec

private def recursorArgumentRhs (index : Fin 5) :
    (RecursorIotaPattern recursorName 5 ``Acc.intro 4).RHS :=
  RecursorIotaPattern.recursorArgumentRhs recursorName 5 ``Acc.intro 4 index

private def constructorArgumentRhs (index : Fin 4) :
    (RecursorIotaPattern recursorName 5 ``Acc.intro 4).RHS :=
  RecursorIotaPattern.constructorArgumentRhs recursorName 5 ``Acc.intro 4
    index

/-- The recursor and constructor must agree on both uniform parameters and
the constructor-result/recursor index before the iota rule may fire. -/
def checks :
    (RecursorIotaPattern recursorName 5 ``Acc.intro 4).Check :=
  .defeq (recursorArgumentRhs ⟨0, by omega⟩)
    (constructorArgumentRhs ⟨0, by omega⟩)
    (.defeq (recursorArgumentRhs ⟨1, by omega⟩)
      (constructorArgumentRhs ⟨1, by omega⟩)
      (.defeq (recursorArgumentRhs ⟨4, by omega⟩)
        (constructorArgumentRhs ⟨2, by omega⟩) .true))

/-- Application-spine constructor in the dependent pattern RHS language. -/
def rhsAppN {pattern : Pattern} : pattern.RHS → List pattern.RHS →
    pattern.RHS
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
      simp only [rhsAppN, ih, Pattern.RHS.apply, List.map_cons, VExpr.appN]

private theorem generatedRhsClosed :
    (generation.rule 0 introNormalized).rhs.Closed :=
  (introGeneratedRuleWF.2.closedN transaction.facts.afterWF.ordered
    (by trivial))

/-- Exact registered equation RHS applied to the production argument slices.

The final constructor capture is the recursive function field `h`.  The
closed generated RHS builds `fun b hba => Acc.rec ... b (h b hba)` after the
six outer applications beta-reduce. -/
def rhs : (RecursorIotaPattern recursorName 5 ``Acc.intro 4).RHS :=
  rhsAppN
    (.fixed (generation.rule 0 introNormalized).rhs generatedRhsClosed)
    [ recursorArgumentRhs ⟨0, by omega⟩,
      recursorArgumentRhs ⟨1, by omega⟩,
      recursorArgumentRhs ⟨2, by omega⟩,
      recursorArgumentRhs ⟨3, by omega⟩,
      recursorArgumentRhs ⟨4, by omega⟩,
      constructorArgumentRhs ⟨3, by omega⟩ ]

/-- Compiled recursive-Pi production pattern for `Acc.intro`. -/
def pattern (constructorId : KId .anon) : RecursorRulePattern where
  recursorName := recursorName
  constructorId := constructorId
  constructorName := ``Acc.intro
  constructorParams := 2
  constructorFields := 2
  ruleIndex := 0
  majorIdx := 5
  rhs := rhs
  checks := checks

@[simp] theorem pattern_rhs_apply (constructorId : KId .anon)
    (v u : VLevel)
    (captures : (RecursorIotaPattern ``Acc.rec 5 ``Acc.intro 4).Path →
      VExpr) :
    (pattern constructorId).rhs.apply [v, u] captures =
      VExpr.appN ((generation.rule 0 introNormalized).rhs.instL [v, u])
        [ captures (RecursorIotaPattern.recursorArgumentPath ``Acc.rec 5
            ``Acc.intro 4 ⟨0, by omega⟩),
          captures (RecursorIotaPattern.recursorArgumentPath ``Acc.rec 5
            ``Acc.intro 4 ⟨1, by omega⟩),
          captures (RecursorIotaPattern.recursorArgumentPath ``Acc.rec 5
            ``Acc.intro 4 ⟨2, by omega⟩),
          captures (RecursorIotaPattern.recursorArgumentPath ``Acc.rec 5
            ``Acc.intro 4 ⟨3, by omega⟩),
          captures (RecursorIotaPattern.recursorArgumentPath ``Acc.rec 5
            ``Acc.intro 4 ⟨4, by omega⟩),
          captures (RecursorIotaPattern.constructorArgumentPath ``Acc.rec 5
            ``Acc.intro 4 ⟨3, by omega⟩) ] := by
  simp [pattern, rhs, rhsAppN_apply, recursorName, recursorArgumentRhs,
    constructorArgumentRhs, Pattern.RHS.apply]

/-- Semantic content of the two uniform-parameter checks and the result-index
check. -/
theorem checks_ok
    (defeq : VExpr → VExpr → Prop) (levels : List VLevel)
    (captures : (RecursorIotaPattern ``Acc.rec 5 ``Acc.intro 4).Path →
      VExpr)
    (h : checks.OK defeq levels captures) :
    defeq
        (captures (RecursorIotaPattern.recursorArgumentPath ``Acc.rec 5
          ``Acc.intro 4 ⟨0, by omega⟩))
        (captures (RecursorIotaPattern.constructorArgumentPath ``Acc.rec 5
          ``Acc.intro 4 ⟨0, by omega⟩)) ∧
      defeq
        (captures (RecursorIotaPattern.recursorArgumentPath ``Acc.rec 5
          ``Acc.intro 4 ⟨1, by omega⟩))
        (captures (RecursorIotaPattern.constructorArgumentPath ``Acc.rec 5
          ``Acc.intro 4 ⟨1, by omega⟩)) ∧
      defeq
        (captures (RecursorIotaPattern.recursorArgumentPath ``Acc.rec 5
          ``Acc.intro 4 ⟨4, by omega⟩))
        (captures (RecursorIotaPattern.constructorArgumentPath ``Acc.rec 5
          ``Acc.intro 4 ⟨2, by omega⟩)) := by
  simpa [checks, recursorName, recursorArgumentRhs,
    constructorArgumentRhs, Pattern.Check.OK,
    RecursorIotaPattern.recursorArgumentRhs,
    RecursorIotaPattern.constructorArgumentRhs, Pattern.RHS.apply] using h

/-! ## Exact finite metadata -/

theorem constructorAt :
    RecursivePiFixture.introConcrete.ConstructorAt 0 2 2 := by
  cases concreteEq : RecursivePiFixture.introConcrete with
  | ctor name levelParams isUnsafe levels induct cidx params fields type =>
      have shape := RecursivePiFixture.introShape
      rw [concreteEq] at shape
      simp only [KConst.IsCertifiedSingletonConstructor] at shape
      simp only [KConst.ConstructorAt]
      refine ⟨shape.2.2.1, ?_, ?_⟩
      · apply UInt64.toNat_inj.mp
        have hparams : accDecl.nparams = 2 := rfl
        rw [hparams] at shape
        simpa only [show (2 : UInt64).toNat = 2 from rfl] using
          shape.2.2.2.1
      · apply UInt64.toNat_inj.mp
        have hfields :
            (VInductDecl.ctorFields
              (VExpr.dropN accDecl.nparams
                RecursivePiFixture.introSource.type)).length = 2 := rfl
        rw [hfields] at shape
        simpa only [show (2 : UInt64).toNat = 2 from rfl] using
          shape.2.2.2.2
  | _ =>
      have shape := RecursivePiFixture.introShape
      rw [concreteEq] at shape
      simp [KConst.IsCertifiedSingletonConstructor] at shape

theorem majorIndex : recursorConcrete.RecursorMajorIdx = some 5 := by
  cases concreteEq : recursorConcrete with
  | recr name levelParams k isUnsafe levels params indices motives minors
      block memberIdx type rules leanAll =>
      have shape := recursorShape
      rw [concreteEq] at shape
      simp only [KConst.IsCertifiedSingletonRecursor] at shape
      simp only [KConst.RecursorMajorIdx]
      have hparams : accDecl.nparams = 2 := rfl
      have hindices : generation.block.rawIndices.length = 1 := rfl
      rw [show params = 2 by
          apply UInt64.toNat_inj.mp
          rw [hparams] at shape
          simpa using shape.2.1,
        show motives = 1 by
          apply UInt64.toNat_inj.mp
          simpa using shape.2.2.2.1,
        show minors = 1 by
          apply UInt64.toNat_inj.mp
          simpa [RecursivePiFixture.constructorIds] using shape.2.2.2.2.1,
        show indices = 1 by
          apply UInt64.toNat_inj.mp
          rw [hindices] at shape
          simpa using shape.2.2.1]
      rfl
  | _ =>
      have shape := recursorShape
      rw [concreteEq] at shape
      simp [KConst.IsCertifiedSingletonRecursor] at shape

@[simp] private theorem introFieldCount :
    (introNormalized.fieldsR accDecl.uvars accDecl.nparams).length = 2 := rfl

theorem metadata {rule : RecRule .anon}
    (hrule : recursorConcrete.RecursorRuleAt 0 rule) :
    RawRecursorRulePatternMetadataRel catalog nameOf recursorId
      recursorConcrete rule (pattern RecursivePiFixture.introId) := by
  refine {
    recursorName := by simpa [pattern, recursorName] using nameOf_recursor
    majorIdx := by simpa [pattern] using majorIndex
    majorIdxCoherent := recursorShape.coherent
    ruleAt := hrule
    constructorName := by
      simpa [pattern] using RecursivePiRecursorFixture.nameOf_intro
    constructorAt := ⟨RecursivePiFixture.introConcrete,
      by simpa [pattern] using catalog_intro,
      by simpa [pattern] using constructorAt⟩
    fields := ?_ }
  obtain ⟨normalized, hnormalized, _, hfields, _, _⟩ :=
    recursorLink.ruleAt hrule
  have hnormalizedEq : normalized = introNormalized := by
    rw [introNormalizedAt] at hnormalized
    exact (Option.some.inj hnormalized).symm
  subst normalized
  apply UInt64.toNat_inj.mp
  simpa only [pattern, introFieldCount,
    show (2 : UInt64).toNat = 2 from rfl] using hfields

end Ix.Tc.RecursivePiPattern
