import Ix.Tc.Verify.Whnf.Iota.NatRuleLayout

/-!
# Checked Nat-iota reduction through typed suffixes

NatRuleLayout retains every application after the literal major instead of silently
discarding an over-application.  This slice gives that suffix its semantic
eliminator.  A definitionally equal replacement for the through-major prefix
can be retranslated under the same concrete arguments, and application
congruence transports the equality to the complete source.

The selected iota pattern still needs two explicit inputs: its checks must
hold for the constructed capture map, and a concrete reducer result must
translate to `pattern.rhs.apply`.  Those are precisely the remaining
inductive-admission/RHS obligations; neither follows from rule-slot existence
or from a successful pattern match alone.
-/

namespace Ix.Tc

open Lean4Lean (VExpr)

namespace RecM
namespace TrAppSuffix

/-- The start of a typed suffix is itself typed whenever the complete
application is typed.  For a nonempty suffix, the first applicable function
type is recovered by walking backward through the snoc derivation. -/
theorem startHasType
    {env : Lean4Lean.VEnv} {uvars : Nat}
    {nameOf : Address → Option Lean.Name} {trProj : RawProjRel}
    {Delta : KVLCtx} {start : VExpr}
    {args : List (KExpr .anon)} {resultV resultType : VExpr}
    (h : TrAppSuffix env uvars nameOf trProj Delta start args resultV)
    (hresult : env.HasType uvars Delta.toCtx resultV resultType) :
    ∃ startType, env.HasType uvars Delta.toCtx start startType := by
  induction h generalizing resultType with
  | nil => exact ⟨resultType, hresult⟩
  | app hsuffix hfun _ _ ih => exact ih hfun

/-- Replace the translated start of a suffix by a definitionally equal
concrete expression.  Every original argument is reattached in production
order, and the complete old and new applications remain definitionally
equal.  In particular, the result expression contains `args`; this theorem
cannot justify dropping a trailing application. -/
theorem rebase
    {env : Lean4Lean.VEnv} {uvars : Nat}
    {nameOf : Address → Option Lean.Name} {trProj : RawProjRel}
    {Delta : KVLCtx} {start : VExpr}
    {args : List (KExpr .anon)} {resultV : VExpr}
    (h : TrAppSuffix env uvars nameOf trProj Delta start args resultV)
    (henv : env.WF) (hDelta : KVLCtx.WF env uvars Delta)
    {replacement : KExpr .anon} {replacementV : VExpr}
    (hreplacementTr :
      TrKExprS env uvars nameOf trProj Delta replacement replacementV)
    (hreplacement :
      env.IsDefEqU uvars Delta.toCtx start replacementV) :
    ∃ resultV',
      TrKExprS env uvars nameOf trProj Delta
          (args.foldl KExpr.mkApp replacement) resultV' ∧
        env.IsDefEqU uvars Delta.toCtx resultV resultV' := by
  induction h generalizing replacement replacementV with
  | nil => exact ⟨replacementV, hreplacementTr, hreplacement⟩
  | @app args current arg argV A B hsuffix hfun harg hargTr ih =>
      obtain ⟨currentV', hcurrentTr, hcurrentEq⟩ :=
        ih hreplacementTr hreplacement
      have hcurrentType :
          env.HasType uvars Delta.toCtx currentV' (.forallE A B) :=
        hfun.defeqU_l henv hDelta.toCtx hcurrentEq
      have hcurrentEqAt :
          env.IsDefEq uvars Delta.toCtx current currentV' (.forallE A B) :=
        hcurrentEq.of_l henv hDelta.toCtx hfun
      refine ⟨.app currentV' argV, ?_, ?_⟩
      · rw [List.foldl_append]
        simp only [List.foldl_cons, List.foldl_nil]
        rw [KExpr.mkApp_shape]
        exact .app hcurrentType harg hcurrentTr hargTr
      · exact (Lean4Lean.VEnv.IsDefEq.appDF hcurrentEqAt harg).toU

end TrAppSuffix
end RecM

namespace RawRecursorRulePatternRel

/-- Apply the soundness component of an admitted iota pattern in the current
environment.  A match is deliberately insufficient: the pattern's explicit
definitional-equality checks must also be discharged. -/
theorem checkedReduction
    {env : Lean4Lean.VEnv} {catalog : Catalog}
    {nameOf : Address → Option Lean.Name}
    {id : KId .anon} {recursor : KConst .anon} {rule : RecRule .anon}
    {pattern : RecursorRulePattern}
    (hpattern : RawRecursorRulePatternRel env catalog nameOf id recursor
      rule pattern)
    (henv : env.WF)
    {uvars : Nat} {Gamma : List VExpr} {source A : VExpr}
    {levels : List Lean4Lean.VLevel}
    {captures : (RecursorIotaPattern pattern.recursorName pattern.majorIdx
      pattern.constructorName
      (pattern.constructorParams.toNat +
        pattern.constructorFields.toNat)).Path → VExpr}
    (hGamma : Lean4Lean.OnCtx Gamma (env.IsType uvars))
    (hmatch : Lean4Lean.Pattern.Matches
      (RecursorIotaPattern pattern.recursorName pattern.majorIdx
        pattern.constructorName
        (pattern.constructorParams.toNat +
          pattern.constructorFields.toNat))
      source levels captures)
    (htype : env.HasType uvars Gamma source A)
    (hchecks : pattern.checks.OK (env.IsDefEqU uvars Gamma)
      levels captures) :
    env.IsDefEqU uvars Gamma source
      (pattern.rhs.apply levels captures) := by
  rcases hpattern with
    ⟨_, _, _, _, _, _, _, hsound⟩
  exact hsound Lean4Lean.VEnv.LE.rfl henv hGamma hmatch htype hchecks

end RawRecursorRulePatternRel

namespace RecM
namespace NatRecLiteralTranslationSplit

/-- Turn a checked iota match at NatRuleLayout's exact through-major boundary into a
semantic replacement of the complete source.  The concrete RHS is rebuilt
under every retained trailing argument, so the conclusion is valid for both
exactly applied and over-applied recursors.

This theorem isolates the final admission-side obligations as `hchecks` and
`hrhsTr`: the current generic inductive oracle supplies conditional pattern
soundness, but it does not prove that a successful match passes its checks or
identify the concrete rule-body application with `pattern.rhs.apply`. -/
theorem checkedRhsSuffix
    {trProj : RawProjRel} {world : VerifyWorld}
    {uvars : Nat} {Delta : KVLCtx}
    (hDelta : KVLCtx.WF world.venv uvars Delta)
    {id : KId .anon} {source : KExpr .anon}
    {parts : NatRecLiteralParts .anon} {majorIdx : Nat}
    {sourceV : VExpr} {priorArgs laterArgs : List (KExpr .anon)}
    {priorV : VExpr}
    (hsplit : NatRecLiteralTranslationSplit world.venv uvars world.nameOf
      trProj Delta id source parts majorIdx sourceV priorArgs laterArgs
      priorV)
    {recursor : KConst .anon} {rule : RecRule .anon}
    {pattern : RecursorRulePattern}
    (hpattern : RawRecursorRulePatternRel world.venv world.catalog
      world.nameOf id recursor rule pattern)
    {levels : List Lean4Lean.VLevel}
    {captures : (RecursorIotaPattern pattern.recursorName pattern.majorIdx
      pattern.constructorName
      (pattern.constructorParams.toNat +
        pattern.constructorFields.toNat)).Path → VExpr}
    (hmatch : Lean4Lean.Pattern.Matches
      (RecursorIotaPattern pattern.recursorName pattern.majorIdx
        pattern.constructorName
        (pattern.constructorParams.toNat +
          pattern.constructorFields.toNat))
      (.app priorV (.natLit parts.major)) levels captures)
    {sourceType : VExpr}
    (hsourceType : world.venv.HasType uvars Delta.toCtx sourceV sourceType)
    (hchecks : pattern.checks.OK
      (world.venv.IsDefEqU uvars Delta.toCtx) levels captures)
    {rhs : KExpr .anon}
    (hrhsTr : TrKExprS world.venv uvars world.nameOf trProj Delta rhs
      (pattern.rhs.apply levels captures)) :
    ∃ resultV,
      TrKExprS world.venv uvars world.nameOf trProj Delta
          (laterArgs.foldl KExpr.mkApp rhs) resultV ∧
        world.venv.IsDefEqU uvars Delta.toCtx sourceV resultV := by
  rcases hsplit with
    ⟨_, _, _, _, _, _, _, _, hthroughTr, hsuffix⟩
  obtain ⟨throughType, hthroughType⟩ :=
    hsuffix.startHasType hsourceType
  have hthroughEq :=
    hpattern.checkedReduction world.venvWF hDelta.toCtx hmatch hthroughType
      hchecks
  exact hsuffix.rebase world.venvWF hDelta hrhsTr hthroughEq

end NatRecLiteralTranslationSplit
end RecM
end Ix.Tc
