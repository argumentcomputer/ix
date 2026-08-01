import Ix.Tc.Verify.Whnf.Iota.RuleInstantiation

/-!
# Quotient-aware registered RHS suffix transport

NatReduction's suffix rebasing theorem required a structural `TrKExprS` witness for
the replacement expression.  RuleInstantiation necessarily produces the quotient relation
`TrKExpr`: universe-instantiation smart constructors preserve Theory meaning,
but need not preserve the exact Theory syntax chosen by the admission record.

This slice removes that impedance mismatch without strengthening either
relation.  It selects the structural representative already carried by
`TrKExpr`, transports the through-major equality to that representative, and
then reuses NatReduction's typed application induction.  Consequently a checked iota
reduction can now consume a quotient-translated concrete RHS while retaining
every trailing application.

The theorem still does not identify an instantiated registered body with
`pattern.rhs.apply`.  Ordinary iota's prefix and constructor-field application
sequence remains an explicit subsequent obligation.
-/

namespace Ix.Tc

open Lean4Lean (VExpr)

namespace RecM
namespace TrAppSuffix

/-- Rebase a typed application suffix from a quotient-translated concrete
replacement.  The quotient contains a structural representative; composing
the caller's equality with the representative equality is enough to invoke
the structural suffix theorem.

The result is structural again.  In particular, all original concrete suffix
arguments remain visible in `args.foldl KExpr.mkApp replacement`. -/
theorem rebaseQuot
    {env : Lean4Lean.VEnv} {uvars : Nat}
    {nameOf : Address → Option Lean.Name} {trProj : RawProjRel}
    {Delta : KVLCtx} {start : VExpr}
    {args : List (KExpr .anon)} {resultV : VExpr}
    (h : TrAppSuffix env uvars nameOf trProj Delta start args resultV)
    (henv : env.WF) (hDelta : KVLCtx.WF env uvars Delta)
    {replacement : KExpr .anon} {replacementV : VExpr}
    (hreplacementTr :
      TrKExpr env uvars nameOf trProj Delta replacement replacementV)
    (hreplacement :
      env.IsDefEqU uvars Delta.toCtx start replacementV) :
    ∃ resultV',
      TrKExprS env uvars nameOf trProj Delta
          (args.foldl KExpr.mkApp replacement) resultV' ∧
        env.IsDefEqU uvars Delta.toCtx resultV resultV' := by
  obtain ⟨replacementS, hreplacementS, hreplacementSEq⟩ := hreplacementTr
  have hstartS :
      env.IsDefEqU uvars Delta.toCtx start replacementS :=
    hreplacement.trans henv hDelta.toCtx hreplacementSEq.symm
  exact h.rebase henv hDelta hreplacementS hstartS

end TrAppSuffix
end RecM

namespace RecM
namespace NatRecLiteralTranslationSplit

/-- Quotient form of `checkedRhsSuffix`.  This is the consumer shape needed
by RuleInstantiation's universe-instantiated registered RHS theorem: exact structural
Theory syntax is unnecessary, while typing and every trailing application
remain explicit. -/
theorem checkedRhsSuffixQuot
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
    (hrhsTr : TrKExpr world.venv uvars world.nameOf trProj Delta rhs
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
  exact hsuffix.rebaseQuot world.venvWF hDelta hrhsTr hthroughEq

end NatRecLiteralTranslationSplit
end RecM

end Ix.Tc
