import Ix.Tc.Verify.Whnf.Delta.ClosedTranslation

/-!
# Universe-count monotonicity for structural translation

`instantiateUnivParams` deliberately returns a parameter-free body unchanged
when its universe array is empty.  Its admitted translation is indexed by
universe count zero, while the caller may itself have universe parameters.
This module proves the required monotonicity instead of modeling the skipped
walker as an execution.

The Theory proof is obtained by instantiating a typing derivation with its own
parameter list and then observing that well-formed levels are unchanged.
Structural translation follows by induction, carrying the source mixed
context's well-formedness through binder cases.
-/

namespace Ix.Tc

open Lean4Lean (OnCtx VEnv VExpr VLevel)

/-- A well-formed universe level remains well-formed when the available
parameter count grows. -/
private theorem vlevelWF_mono {before after : Nat} (hle : before ≤ after) :
    ∀ {level : VLevel}, level.WF before → level.WF after := by
  intro level h
  induction level with
  | zero => trivial
  | succ level ih => exact ih h
  | max left right ihLeft ihRight =>
      exact ⟨ihLeft h.1, ihRight h.2⟩
  | imax left right ihLeft ihRight =>
      exact ⟨ihLeft h.1, ihRight h.2⟩
  | param index => exact Nat.lt_of_lt_of_le h hle

/-- A well-formed Theory context has universe-well-formed entry types. -/
private theorem ctx_levelWF {env : VEnv} {uvars : Nat} :
    ∀ {ctx : List VExpr},
      OnCtx ctx (env.IsType uvars) →
        OnCtx ctx (fun _ type => type.LevelWF uvars)
  | [], _ => trivial
  | type :: ctx, h => by
      rcases h with ⟨hctx, level, htype⟩
      have hctxLevels := ctx_levelWF hctx
      exact ⟨hctxLevels, (htype.levelWF hctxLevels).1⟩

/-- Instantiating a universe-well-formed context with its own parameters is
the identity. -/
private theorem ctx_instParams_eq {uvars : Nat} :
    ∀ {ctx : List VExpr},
      OnCtx ctx (fun _ type => type.LevelWF uvars) →
        ctx.map (VExpr.instL (VLevel.params uvars)) = ctx
  | [], _ => rfl
  | type :: ctx, h => by
      rcases h with ⟨hctx, htype⟩
      simp only [List.map_cons, ctx_instParams_eq hctx, htype.instL_id]

/-- Theory definitional equality is monotone in the number of available
universe parameters. -/
private theorem isDefEq_monoU {env : VEnv} {before after : Nat}
    (hle : before ≤ after) {ctx : List VExpr} {left right type : VExpr}
    (hctx : OnCtx ctx (env.IsType before))
    (h : env.IsDefEq before ctx left right type) :
    env.IsDefEq after ctx left right type := by
  have hlevels : ∀ level ∈ VLevel.params before, level.WF after := by
    intro level hlevel
    exact vlevelWF_mono hle (VLevel.params_wf hlevel)
  have hctxLevels := ctx_levelWF hctx
  have hterms := h.levelWF hctxLevels
  have hinst := h.instL hlevels
  rw [ctx_instParams_eq hctxLevels,
    hterms.1.instL_id,
    hterms.2.1.instL_id,
    hterms.2.2.instL_id] at hinst
  exact hinst

private theorem hasType_monoU {env : VEnv} {before after : Nat}
    (hle : before ≤ after) {ctx : List VExpr} {term type : VExpr}
    (hctx : OnCtx ctx (env.IsType before))
    (h : env.HasType before ctx term type) :
    env.HasType after ctx term type :=
  isDefEq_monoU hle hctx h

private theorem isType_monoU {env : VEnv} {before after : Nat}
    (hle : before ≤ after) {ctx : List VExpr} {type : VExpr}
    (hctx : OnCtx ctx (env.IsType before))
    (h : env.IsType before ctx type) :
    env.IsType after ctx type := by
  obtain ⟨level, htype⟩ := h
  exact ⟨level, isDefEq_monoU hle hctx htype⟩

namespace TrKExprS

/-- Structural translation remains valid when the universe-parameter budget
grows.  The source mixed context is required to be well-formed at the smaller
budget so the embedded Theory typing premises can be transported. -/
theorem monoU {env : VEnv} {before after : Nat}
    {nameOf : Address → Option Lean.Name}
    {trProj : List VExpr → Lean.Name → Nat → VExpr → VExpr → Prop}
    (hle : before ≤ after)
    {m : Mode} {Delta : KVLCtx} {e : KExpr m} {e' : VExpr}
    (H : TrKExprS env before nameOf trProj Delta e e')
    (hDelta : KVLCtx.WF env before Delta) :
    TrKExprS env after nameOf trProj Delta e e' := by
  induction H with
  | var h =>
      exact .var h
  | fvar h =>
      exact .fvar h
  | sort h =>
      exact .sort (vlevelWF_mono hle h)
  | const hname hlookup hlevels harity =>
      exact .const hname hlookup
        (fun level hlevel =>
          vlevelWF_mono hle (hlevels level hlevel))
        harity
  | @app Delta f arg info f' arg' A B
      hfunTy hargTy hfun harg ihfun iharg =>
      exact .app (A := A) (B := B)
        (hasType_monoU hle hDelta.toCtx hfunTy)
        (hasType_monoU hle hDelta.toCtx hargTy)
        (ihfun hDelta) (iharg hDelta)
  | @lam Delta name bi ty body info ty' body'
      hty htyTr hbodyTr ihty ihbody =>
      have hbodyDelta :
          KVLCtx.WF env before ((none, .vlam ty') :: Delta) :=
        ⟨hDelta, nofun, hty⟩
      exact .lam
        (isType_monoU hle hDelta.toCtx hty)
        (ihty hDelta)
        (ihbody hbodyDelta)
  | @all Delta name bi ty body info ty' body'
      hty hbodyTy htyTr hbodyTr ihty ihbody =>
      have hbodyDelta :
          KVLCtx.WF env before ((none, .vlam ty') :: Delta) :=
        ⟨hDelta, nofun, hty⟩
      exact .all
        (isType_monoU hle hDelta.toCtx hty)
        (isType_monoU hle hbodyDelta.toCtx hbodyTy)
        (ihty hDelta)
        (ihbody hbodyDelta)
  | @letE Delta name ty value body nondep info ty' value' body'
      hvalueTy htyTr hvalueTr hbodyTr ihty ihvalue ihbody =>
      have hbodyDelta :
          KVLCtx.WF env before ((none, .vlet ty' value') :: Delta) :=
        ⟨hDelta, nofun, hvalueTy⟩
      exact .letE
        (hasType_monoU hle hDelta.toCtx hvalueTy)
        (ihty hDelta)
        (ihvalue hDelta)
        (ihbody hbodyDelta)
  | prj hname hvalue hproj ihvalue =>
      exact .prj hname (ihvalue hDelta) hproj
  | nat h =>
      exact .nat h
  | str h =>
      exact .str h

end TrKExprS

end Ix.Tc
