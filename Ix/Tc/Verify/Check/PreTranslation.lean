import Ix.Tc.Verify.Check.Scoped
import Ix.Tc.Verify.Decl
import Ix.Tc.Verify.Trans

/-!
# Untyped structural translation for checker ingress

`TrKExprS` is intentionally strong: its application and binder constructors
already contain the typing facts which make reduction and infer-only
soundness useful.  That makes it the wrong precondition for `checkConst`,
whose job is to establish those very facts.

`PreTrKExprS` is the non-circular bridge.  It retains exact variable
resolution, universe bounds, constant resolution/arity, literal availability,
and projection interpretation, but contains no `HasType` or `IsType`
premise.  Successful full inference will upgrade this relation to
`TrKExprS`; merely constructing a value of this relation cannot admit a
declaration.
-/

namespace Ix.Tc

open Lean4Lean (VExpr VEnv VConstant)

variable (env : VEnv) (uvars : Nat)
    (nameOf : Address → Option Lean.Name) (trProj : RawProjRel) in
/-- Syntax-directed, well-scoped, but deliberately untyped translation. -/
inductive PreTrKExprS : KVLCtx → KExpr .anon → VExpr → Prop
  | var {Delta : KVLCtx} {idx : UInt64} {name : Mode.anon.F Name}
      {info : ExprInfo .anon} {value type : VExpr} :
    Delta.find? (.inl idx.toNat) = some (value, type) →
    PreTrKExprS Delta (.var idx name info) value
  | fvar {Delta : KVLCtx} {fv : FVarId} {name : Mode.anon.F Name}
      {info : ExprInfo .anon} {value type : VExpr} :
    Delta.find? (.inr fv) = some (value, type) →
    PreTrKExprS Delta (.fvar fv name info) value
  | sort {Delta : KVLCtx} {u : KUniv .anon} {info : ExprInfo .anon} :
    u.toVLevel.WF uvars →
    PreTrKExprS Delta (.sort u info) (.sort u.toVLevel)
  | const {Delta : KVLCtx} {id : KId .anon}
      {levels : Array (KUniv .anon)} {info : ExprInfo .anon}
      {name : Lean.Name} {ci : VConstant} :
    nameOf id.addr = some name →
    env.constants name = some ci →
    (∀ level ∈ levels, level.toVLevel.WF uvars) →
    levels.size = ci.uvars →
    PreTrKExprS Delta (.const id levels info)
      (.const name (levels.toList.map KUniv.toVLevel))
  | app {Delta : KVLCtx} {fn arg : KExpr .anon}
      {info : ExprInfo .anon} {fnV argV : VExpr} :
    PreTrKExprS Delta fn fnV →
    PreTrKExprS Delta arg argV →
    PreTrKExprS Delta (.app fn arg info) (.app fnV argV)
  | lam {Delta : KVLCtx} {name : Mode.anon.F Name}
      {bi : Mode.anon.F Lean.BinderInfo} {type body : KExpr .anon}
      {info : ExprInfo .anon} {typeV bodyV : VExpr} :
    PreTrKExprS Delta type typeV →
    PreTrKExprS ((none, .vlam typeV) :: Delta) body bodyV →
    PreTrKExprS Delta (.lam name bi type body info) (.lam typeV bodyV)
  | all {Delta : KVLCtx} {name : Mode.anon.F Name}
      {bi : Mode.anon.F Lean.BinderInfo} {type body : KExpr .anon}
      {info : ExprInfo .anon} {typeV bodyV : VExpr} :
    PreTrKExprS Delta type typeV →
    PreTrKExprS ((none, .vlam typeV) :: Delta) body bodyV →
    PreTrKExprS Delta (.all name bi type body info) (.forallE typeV bodyV)
  | letE {Delta : KVLCtx} {name : Mode.anon.F Name}
      {type value body : KExpr .anon} {nonDep : Bool}
      {info : ExprInfo .anon} {typeV valueV bodyV : VExpr} :
    PreTrKExprS Delta type typeV →
    PreTrKExprS Delta value valueV →
    PreTrKExprS ((none, .vlet typeV valueV) :: Delta) body bodyV →
    PreTrKExprS Delta (.letE name type value body nonDep info) bodyV
  | prj {Delta : KVLCtx} {id : KId .anon} {field : UInt64}
      {value : KExpr .anon} {info : ExprInfo .anon}
      {name : Lean.Name} {valueV resultV : VExpr} :
    nameOf id.addr = some name →
    PreTrKExprS Delta value valueV →
    trProj Delta.toCtx name field.toNat valueV resultV →
    PreTrKExprS Delta (.prj id field value info) resultV
  | nat {Delta : KVLCtx} {value : Nat} {blob : Address}
      {info : ExprInfo .anon} :
    env.ContainsLits (.natVal value) →
    PreTrKExprS Delta (.nat value blob info) (.natLit value)
  | str {Delta : KVLCtx} {value : String} {blob : Address}
      {info : ExprInfo .anon} :
    env.ContainsLits (.strVal value) →
    PreTrKExprS Delta (.str value blob info) (.trLiteral (.strVal value))

namespace TrKExprS

/-- Forget only the typing premises of a checked structural translation. -/
theorem pre
    {env : VEnv} {uvars : Nat} {nameOf : Address → Option Lean.Name}
    {trProj : RawProjRel} {Delta : KVLCtx} {source : KExpr .anon}
    {sourceV : VExpr}
    (h : TrKExprS env uvars nameOf trProj Delta source sourceV) :
    PreTrKExprS env uvars nameOf trProj Delta source sourceV := by
  induction h with
  | var h => exact .var h
  | fvar h => exact .fvar h
  | sort h => exact .sort h
  | const hname hlookup hlevels harity =>
      exact .const hname hlookup hlevels harity
  | app _ _ _ _ ihfn iharg => exact .app ihfn iharg
  | lam _ _ _ ihtype ihbody => exact .lam ihtype ihbody
  | all _ _ _ _ ihtype ihbody => exact .all ihtype ihbody
  | letE _ _ _ _ ihtype ihvalue ihbody =>
      exact .letE ihtype ihvalue ihbody
  | prj hname _ hproj ihvalue => exact .prj hname ihvalue hproj
  | nat hlit => exact .nat hlit
  | str hlit => exact .str hlit

end TrKExprS

end Ix.Tc
