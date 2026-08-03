import Ix.Tc.Verify.DefEq.BoolTrue
import Ix.Tc.Verify.Whnf.Projection.StringExpansion

/-!
# String-literal definitional equality

The third recursive tier expands compact String syntax before either side is
normalized.  K1's expansion plan proves that the concrete intern transaction
terminates with a supported, structurally translatable term.  DefEq needs the
stronger fact recorded here: that exact generated term translates to the same
Theory literal as the compact source syntax.
-/

namespace Ix.Tc

open Lean4Lean (VExpr)

/-- A K1 String-expansion plan together with the exact Theory meaning needed
by DefEq.  Merely knowing that the generated expression has *some*
translation would not justify comparing it in place of the source literal. -/
structure DefEqStringExpansionPlan
    (trProj : RawProjRel) (world : VerifyWorld) (support : RunSupport)
    (p : Primitives .anon) (value : String) where
  plan : RecM.StringExpansionPlan trProj world support p value
  literalTranslation : ∀ uvars Delta,
    TrKExprS world.venv uvars world.nameOf trProj Delta
      (KExpr.mkApp (RecM.stringMkConst p) plan.list)
      (.trLiteral (.strVal value))

/-- Run-scoped String resources for every canonical primitive table that can
occur in an invariant state. -/
structure DefEqStringContext (trProj : RawProjRel) (world : VerifyWorld)
    (support : RunSupport) where
  collisionFree : support.CollisionFree
  plan : ∀ p, p.CanonicalAnon → ∀ value,
    DefEqStringExpansionPlan trProj world support p value

namespace RecM

attribute [local irreducible] strLitToConstructor
  strLitToConstructorWithPrimitives

/-- A concrete semantic plan strengthens K1's exact-result expansion theorem
with the particular Theory literal required by DefEq. -/
theorem strLitToConstructor_defeq_plan_wf
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {Delta : KVLCtx} {s : TcState .anon} {value : String}
    (hcollision : support.CollisionFree)
    (semanticPlan :
      DefEqStringExpansionPlan trProj world support s.prims value) :
    RecM.WF layer semantics trProj world support uvars Delta s
      (strLitToConstructor value)
      (fun expanded _ => support expanded ∧
        TrKExprS world.venv uvars world.nameOf trProj Delta expanded
          (.trLiteral (.strVal value))) := by
  apply RecM.WF.mono
    (strLitToConstructor_plan_exact_wf hcollision semanticPlan.plan)
  · intro expanded after hpost
    rcases hpost with ⟨hexact, hsupported, _⟩
    subst expanded
    exact ⟨hsupported, semanticPlan.literalTranslation uvars Delta⟩
  · intro _ _ _
    trivial

/-- The concrete String expansion returns a supported expression whose
structural translation is exactly the compact source literal's translation. -/
theorem strLitToConstructor_defeq_wf
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {Delta : KVLCtx} {s : TcState .anon} {value : String}
    (context : DefEqStringContext trProj world support)
    (hcanonical : CanonicalPrimitiveStates layer semantics trProj world
      support uvars) :
    RecM.WF layer semantics trProj world support uvars Delta s
      (strLitToConstructor value)
      (fun expanded _ => support expanded ∧
        TrKExprS world.venv uvars world.nameOf trProj Delta expanded
          (.trLiteral (.strVal value))) := by
  intro methods hmethods hI
  exact strLitToConstructor_defeq_plan_wf context.collisionFree
    (context.plan s.prims (hcanonical hI) value) methods hmethods hI

/-- Expanding a compact String literal and accepting the recursive comparison
is sound.  Every non-String source returns `false` without touching state. -/
theorem tryStringLitExpansion_wf
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {Delta : KVLCtx} {state : TcState .anon}
    {source other : KExpr .anon} {sourceV otherV : VExpr}
    (context : DefEqStringContext trProj world support)
    (hcanonical : CanonicalPrimitiveStates layer semantics trProj world
      support uvars)
    (hsourceSupport : support source) (hotherSupport : support other)
    (hsource : TrKExprS world.venv uvars world.nameOf trProj Delta source
      sourceV)
    (hother : TrKExprS world.venv uvars world.nameOf trProj Delta other
      otherV) :
    RecM.WF layer semantics trProj world support uvars Delta state
      (tryStringLitExpansion source other)
      (fun answer _ => answer = true →
        world.venv.IsDefEqU uvars Delta.toCtx sourceV otherV) := by
  cases hsource <;> simp only [tryStringLitExpansion]
  all_goals first
    | exact RecM.WF.pure fun _ hanswer => by contradiction
    | skip
  rename_i value blob info hcontains
  apply RecM.WF.bind (strLitToConstructor_defeq_wf context hcanonical)
  intro expanded after hExpanded
  exact isDefEqCall_wf hExpanded.1 hotherSupport hExpanded.2 hother

namespace DefEqAfterStringExpansion

/-- Semantic contract for the recursive tiers following literal String
expansion. -/
def WF (layer : WhnfLayer) (semantics : CacheSemantics)
    (trProj : RawProjRel) (world : VerifyWorld) (support : RunSupport)
    (uvars : Nat) : Prop :=
  ∀ {Delta state a b aV bV},
    support a → support b →
    TrKExprS world.venv uvars world.nameOf trProj Delta a aV →
    TrKExprS world.venv uvars world.nameOf trProj Delta b bV →
    RecM.WF layer semantics trProj world support uvars Delta state
      (isDefEqInnerAfterStringExpansion a b)
      (fun answer _ => answer = true →
        world.venv.IsDefEqU uvars Delta.toCtx aV bV)

/-- Discharge both ordered String-expansion attempts.  The second attempt's
recursive equality is reversed semantically before it is returned for the
original `(a,b)` order. -/
theorem closesAfterBoolTrue
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat}
    (context : DefEqStringContext trProj world support)
    (hcanonical : CanonicalPrimitiveStates layer semantics trProj world
      support uvars)
    (htail : WF layer semantics trProj world support uvars) :
    DefEqAfterBoolTrue.WF layer semantics trProj world support uvars := by
  intro Delta state a b aV bV haSupport hbSupport ha hb
  unfold isDefEqInnerAfterBoolTrue
  cases hguard : hasStringLiteralPair a b with
  | false =>
      simp only [Bool.false_eq_true, if_false]
      exact htail haSupport hbSupport ha hb
  | true =>
      simp only [if_true]
      apply RecM.WF.bind
        (tryStringLitExpansion_wf context hcanonical
          haSupport hbSupport ha hb)
      intro acceptedAB afterAB hacceptedAB
      cases acceptedAB with
      | true =>
          simp only [if_true]
          exact RecM.WF.pure fun _ _ => hacceptedAB rfl
      | false =>
          simp only [Bool.false_eq_true, if_false]
          apply RecM.WF.bind
            (tryStringLitExpansion_wf context hcanonical
              hbSupport haSupport hb ha)
          intro acceptedBA afterBA hacceptedBA
          cases acceptedBA with
          | true =>
              simp only [if_true]
              exact RecM.WF.pure fun _ _ => (hacceptedBA rfl).symm
          | false =>
              simp only [Bool.false_eq_true, if_false]
              exact htail haSupport hbSupport ha hb

/-- Assemble structural comparison, eager Bool reduction, and literal String
expansion, leaving the post-String recursive tail explicit. -/
theorem closesInner
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat}
    (theory : WhnfTheory trProj world uvars)
    (hcollision : support.CollisionFree)
    (hsorts : SortComponentResources support)
    (hstructural : QuickDefEqResources support)
    (boolContext : BoolTruePrimitiveContext world)
    (stringContext : DefEqStringContext trProj world support)
    (hcanonical : CanonicalPrimitiveStates layer semantics trProj world
      support uvars)
    (hwhnf : DefEqDirectWhnf.WFAt layer semantics trProj world support
      uvars)
    (htail : WF layer semantics trProj world support uvars) :
    ∀ {Delta state a b aV bV},
      support a → support b →
      TrKExprS world.venv uvars world.nameOf trProj Delta a aV →
      TrKExprS world.venv uvars world.nameOf trProj Delta b bV →
      RecM.WF layer semantics trProj world support uvars Delta state
        (isDefEqInner a b)
        (fun answer _ => answer = true →
          world.venv.IsDefEqU uvars Delta.toCtx aV bV) :=
  DefEqAfterBoolTrue.closesInner theory hcollision hsorts hstructural
    boolContext hcanonical hwhnf
    (closesAfterBoolTrue stringContext hcanonical htail)

end DefEqAfterStringExpansion

end RecM

end Ix.Tc
