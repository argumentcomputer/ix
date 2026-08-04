import Ix.Tc.Verify.Check.PreTranslationIngress
import Lean4Lean.Theory.Typing.Strong

/-!
# Compatibility of raw and typed structural translations

A cache hit can supply a typed translation produced by an earlier checked
run, while the current `checkConst` ingress supplies only `PreTrKExprS`.
This theorem reconciles the two witnesses.  It keeps the exact Theory term
chosen by the current raw translation and borrows only the typing evidence
from the checked witness.
-/

namespace Ix.Tc

open Lean4Lean (VExpr VEnv)

/-- Upgrade a raw structural translation using any typed translation of the
same kernel expression in a pairwise-definitionally-equal context. -/
theorem PreTrKExprS.upgradeOfTyped
    {env : VEnv} {uvars : Nat}
    {nameOf : Address → Option Lean.Name}
    {trProj : RawProjRel}
    (henv : VEnv.WF env)
    (hlit : ∀ l, env.ContainsLits l →
      VExpr.WF env uvars [] (VExpr.trLiteral l))
    (htp : TrProjOK env uvars trProj)
    {DeltaRaw DeltaTyped : KVLCtx} {source : KExpr .anon}
    {rawV typedV : VExpr}
    (hDelta : KVLCtx.IsDefEq env uvars DeltaRaw DeltaTyped)
    (Hraw : PreTrKExprS env uvars nameOf trProj DeltaRaw source rawV)
    (Htyped : TrKExprS env uvars nameOf trProj DeltaTyped source typedV) :
    TrKExprS env uvars nameOf trProj DeltaRaw source rawV := by
  induction Hraw generalizing DeltaTyped typedV with
  | var hfind => exact .var hfind
  | fvar hfind => exact .fvar hfind
  | sort hlevel => exact .sort hlevel
  | const hname hlookup hlevels harity =>
      exact .const hname hlookup hlevels harity
  | app hrawFn hrawArg ihFn ihArg =>
      let .app hfnType hargType htypedFn htypedArg := Htyped
      have hfn := ihFn hDelta htypedFn
      have harg := ihArg hDelta htypedArg
      have hfnEq := hfn.uniq henv hlit htp hDelta htypedFn
      have hargEq := harg.uniq henv hlit htp hDelta htypedArg
      have hfnType := hfnType.defeqDFC henv (hDelta.symm henv).defeqCtx
      have hargType := hargType.defeqDFC henv (hDelta.symm henv).defeqCtx
      exact .app
        (hfnType.defeqU_l henv hDelta.wf.toCtx hfnEq.symm)
        (hargType.defeqU_l henv hDelta.wf.toCtx hargEq.symm)
        hfn harg
  | lam hrawType hrawBody ihType ihBody =>
      let .lam htypeType htypedType htypedBody := Htyped
      have htype := ihType hDelta htypedType
      have htypeEq := htype.uniq henv hlit htp hDelta htypedType
      have htypeType :=
        htypeType.defeqDFC henv (hDelta.symm henv).defeqCtx
      have hrawTypeType :=
        htypeType.defeqU_l henv hDelta.wf.toCtx htypeEq.symm
      obtain ⟨_, hrawTypeHasType⟩ := hrawTypeType
      have htypeEq' :=
        htypeEq.of_l henv hDelta.wf.toCtx hrawTypeHasType
      have hbodyDelta : KVLCtx.IsDefEq env uvars
          ((none, .vlam _) :: _) ((none, .vlam _) :: _) :=
        hDelta.cons nofun (.vlam htypeEq')
      have hbody := ihBody hbodyDelta htypedBody
      exact .lam ⟨_, hrawTypeHasType⟩ htype hbody
  | all hrawType hrawBody ihType ihBody =>
      let .all htypeType hbodyType htypedType htypedBody := Htyped
      have htype := ihType hDelta htypedType
      have htypeEq := htype.uniq henv hlit htp hDelta htypedType
      have htypeType :=
        htypeType.defeqDFC henv (hDelta.symm henv).defeqCtx
      have hrawTypeType :=
        htypeType.defeqU_l henv hDelta.wf.toCtx htypeEq.symm
      obtain ⟨_, hrawTypeHasType⟩ := hrawTypeType
      have htypeEq' :=
        htypeEq.of_l henv hDelta.wf.toCtx hrawTypeHasType
      have hbodyDelta : KVLCtx.IsDefEq env uvars
          ((none, .vlam _) :: _) ((none, .vlam _) :: _) :=
        hDelta.cons nofun (.vlam htypeEq')
      have hbody := ihBody hbodyDelta htypedBody
      have hbodyEq := hbody.uniq henv hlit htp hbodyDelta htypedBody
      have hbodyType :=
        hbodyType.defeqDFC henv (hbodyDelta.symm henv).defeqCtx
      have hrawBodyType :=
        hbodyType.defeqU_l henv hbodyDelta.wf.toCtx hbodyEq.symm
      exact .all ⟨_, hrawTypeHasType⟩ hrawBodyType htype hbody
  | letE hrawType hrawValue hrawBody ihType ihValue ihBody =>
      let .letE hvalueType htypedType htypedValue htypedBody := Htyped
      have htype := ihType hDelta htypedType
      have hvalue := ihValue hDelta htypedValue
      have htypeEq := htype.uniq henv hlit htp hDelta htypedType
      have hvalueEq := hvalue.uniq henv hlit htp hDelta htypedValue
      have hvalueType :=
        hvalueType.defeqDFC henv (hDelta.symm henv).defeqCtx
      have hrawValueType :=
        (hvalueType.defeqU_l henv hDelta.wf.toCtx hvalueEq.symm).defeqU_r
          henv hDelta.wf.toCtx htypeEq.symm
      have hvalueEq' := hvalueEq.of_l henv hDelta.wf.toCtx hrawValueType
      obtain ⟨_, hrawTypeHasType⟩ :=
        hrawValueType.isType henv hDelta.wf.toCtx
      have htypeEq' :=
        htypeEq.of_l henv hDelta.wf.toCtx hrawTypeHasType
      have hbodyDelta : KVLCtx.IsDefEq env uvars
          ((none, .vlet _ _) :: _) ((none, .vlet _ _) :: _) :=
        hDelta.cons nofun (.vlet hvalueEq' htypeEq')
      have hbody := ihBody hbodyDelta htypedBody
      exact .letE hrawValueType htype hvalue hbody
  | prj hname hrawValue hprojection ihValue =>
      let .prj _ htypedValue _ := Htyped
      have hvalue := ihValue hDelta htypedValue
      exact .prj hname hvalue hprojection
  | nat hlit => exact .nat hlit
  | str hlit => exact .str hlit

/-- Binder-core pre-translation can be upgraded from well-formedness of its
exact Theory target.  Strong inversion supplies precisely the application
and binder typing premises omitted by `PreTrKExprS`; the core restriction
excludes lets and projections, whose result well-formedness alone would not
recover all child judgments. -/
theorem PreTrKExprS.upgradeBinderCoreOfWF
    {env : VEnv} {uvars : Nat}
    {nameOf : Address → Option Lean.Name} {trProj : RawProjRel}
    (henv : VEnv.WF env)
    {Delta : KVLCtx} (hDelta : KVLCtx.WF env uvars Delta)
    {source : KExpr .anon} {sourceV : VExpr}
    (hcore : source.binderCore = true)
    (hpre : PreTrKExprS env uvars nameOf trProj Delta source sourceV)
    (hwf : VExpr.WF env uvars Delta.toCtx sourceV) :
    TrKExprS env uvars nameOf trProj Delta source sourceV := by
  induction hpre with
  | var hfind => exact .var hfind
  | fvar => simp [KExpr.binderCore] at hcore
  | sort hlevel => exact .sort hlevel
  | const hname hlookup hlevels harity =>
      exact .const hname hlookup hlevels harity
  | app hpreFn hpreArg ihFn ihArg =>
      simp only [KExpr.binderCore, Bool.and_eq_true] at hcore
      obtain ⟨type, body, hfnType, hargType⟩ :=
        Lean4Lean.VExpr.WF.app_inv henv.ordered hDelta.toCtx hwf
      exact .app hfnType hargType
        (ihFn hDelta hcore.1 ⟨_, hfnType⟩)
        (ihArg hDelta hcore.2 ⟨_, hargType⟩)
  | lam hpreType hpreBody ihType ihBody =>
      simp only [KExpr.binderCore, Bool.and_eq_true] at hcore
      obtain ⟨htype, hbody⟩ :=
        Lean4Lean.VExpr.WF.lam_inv henv.ordered hDelta.toCtx hwf
      have htypeWF : VExpr.WF env uvars _ _ :=
        ⟨_, htype.choose_spec⟩
      exact .lam htype
        (ihType hDelta hcore.1 htypeWF)
        (ihBody ⟨hDelta, nofun, htype⟩ hcore.2 hbody)
  | all hpreType hpreBody ihType ihBody =>
      simp only [KExpr.binderCore, Bool.and_eq_true] at hcore
      obtain ⟨_, hwhole⟩ := hwf
      obtain ⟨htype, hbody⟩ :=
        Lean4Lean.VEnv.HasType.forallE_inv henv.ordered hwhole
      have htypeWF : VExpr.WF env uvars _ _ :=
        ⟨_, htype.choose_spec⟩
      have hbodyWF : VExpr.WF env uvars _ _ :=
        ⟨_, hbody.choose_spec⟩
      exact .all htype hbody
        (ihType hDelta hcore.1 htypeWF)
        (ihBody ⟨hDelta, nofun, htype⟩ hcore.2 hbodyWF)
  | letE => simp [KExpr.binderCore] at hcore
  | prj => simp [KExpr.binderCore] at hcore
  | nat => simp [KExpr.binderCore] at hcore
  | str => simp [KExpr.binderCore] at hcore

end Ix.Tc
