import Ix.Tc.Verify.Whnf.Beta.LambdaPeeling

/-!
# Typed splitting at the multi-beta consumption boundary

`consumeBetaLams` identifies an exact prefix of the production application
spine.  This slice cuts the typed `TrAppSuffix` derivation at that same
position, retaining both the applications consumed by beta and every
unconsumed application rebuilt afterward.
-/

namespace Ix.Tc
namespace RecM
namespace TrAppSuffix

/-- Transport the starting expression of a typed suffix across Theory
definitional equality while retaining the suffix as a `TrAppSuffix`.  Unlike
`rebase`, this form is intended for a second structural transformation of the
replacement prefix before the original trailing arguments are reattached. -/
theorem rebaseStart
    {env : Lean4Lean.VEnv} {uvars : Nat}
    {nameOf : Address -> Option Lean.Name} {trProj : RawProjRel}
    {Delta : KVLCtx} {start : Lean4Lean.VExpr}
    {args : List (KExpr .anon)} {resultV : Lean4Lean.VExpr}
    (h : TrAppSuffix env uvars nameOf trProj Delta start args resultV)
    (henv : env.WF) (hDelta : KVLCtx.WF env uvars Delta)
    {replacementV : Lean4Lean.VExpr}
    (hreplacement : env.IsDefEqU uvars Delta.toCtx start replacementV) :
    exists resultV',
      TrAppSuffix env uvars nameOf trProj Delta replacementV args resultV' /\
        env.IsDefEqU uvars Delta.toCtx resultV resultV' := by
  induction h generalizing replacementV with
  | nil => exact ⟨replacementV, .nil, hreplacement⟩
  | @app args current arg argV A B hsuffix hfun harg hargTr ih =>
      obtain ⟨currentV', hcurrentSuffix, hcurrentEq⟩ := ih hreplacement
      have hcurrentType :
          env.HasType uvars Delta.toCtx currentV' (.forallE A B) :=
        hfun.defeqU_l henv hDelta.toCtx hcurrentEq
      have hcurrentEqAt :
          env.IsDefEq uvars Delta.toCtx current currentV' (.forallE A B) :=
        hcurrentEq.of_l henv hDelta.toCtx hfun
      exact ⟨.app currentV' argV,
        .app hcurrentSuffix hcurrentType harg hargTr,
        (Lean4Lean.VEnv.IsDefEq.appDF hcurrentEqAt harg).toU⟩

/-- Split a typed application suffix after exactly `n` arguments.  Both
pieces retain their original typing derivations and production order. -/
theorem splitAt
    {env : Lean4Lean.VEnv} {uvars : Nat}
    {nameOf : Address -> Option Lean.Name} {trProj : RawProjRel}
    {Delta : KVLCtx} {start : Lean4Lean.VExpr}
    {args : List (KExpr .anon)} {resultV : Lean4Lean.VExpr}
    (h : TrAppSuffix env uvars nameOf trProj Delta start args resultV)
    (n : Nat) (hn : n <= args.length) :
    exists middleV,
      TrAppSuffix env uvars nameOf trProj Delta start (args.take n) middleV /\
        TrAppSuffix env uvars nameOf trProj Delta middleV (args.drop n)
          resultV := by
  induction h generalizing n with
  | nil =>
      have hn0 : n = 0 := by simpa using hn
      subst n
      exact ⟨start, .nil, .nil⟩
  | @app args current arg argV A B hprefix hfun harg hargTr ih =>
      by_cases hwhole : n = (args ++ [arg]).length
      · subst n
        refine ⟨.app current argV, ?_, ?_⟩
        · rw [List.take_length]
          exact TrAppSuffix.app hprefix hfun harg hargTr
        · rw [List.drop_length]
          exact .nil
      · have hnPrefix : n <= args.length := by
          simp only [List.length_append, List.length_singleton] at hn hwhole
          omega
        obtain ⟨middleV, htake, hdrop⟩ := ih n hnPrefix
        refine ⟨middleV, ?_, ?_⟩
        · rw [List.take_append_of_le_length hnPrefix]
          exact htake
        · rw [List.drop_append_of_le_length hnPrefix]
          exact TrAppSuffix.app hdrop hfun harg hargTr

/-- Cut a complete typed application spine at production's certified
`consumeBetaLams` result.  The first derivation contains exactly the peeled
arguments; the second contains exactly the `Array.extract` rebuilt by
`finishAppResult`. -/
theorem splitConsume
    {env : Lean4Lean.VEnv} {uvars : Nat}
    {nameOf : Address -> Option Lean.Name} {trProj : RawProjRel}
    {Delta : KVLCtx} {startV resultV : Lean4Lean.VExpr}
    {start body : KExpr .anon} {args consumed : Array (KExpr .anon)}
    (hconsume : consumeBetaLams start args = (body, consumed))
    (h : TrAppSuffix env uvars nameOf trProj Delta startV args.toList
      resultV) :
    exists middleV,
      BetaPeel start consumed.toList body /\
        TrAppSuffix env uvars nameOf trProj Delta startV consumed.toList
          middleV /\
        TrAppSuffix env uvars nameOf trProj Delta middleV
          (args.extract consumed.size args.size).toList resultV := by
  obtain ⟨hpeel, hprefix, hsize⟩ := BetaPeel.of_consume hconsume
  obtain ⟨middleV, hbefore, hafter⟩ :=
    h.splitAt consumed.size (by simpa using hsize)
  refine ⟨middleV, hpeel, ?_, ?_⟩
  · rw [hprefix]
    exact hbefore
  · rw [BetaPeel.remaining_eq_drop hconsume]
    exact hafter

end TrAppSuffix
end RecM
end Ix.Tc
