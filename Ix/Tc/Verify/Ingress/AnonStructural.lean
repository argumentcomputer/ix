import Ix.Tc.Const
import Ix.Tc.Verify.Expr

/-!
# Structural equality for anonymous kernel values

Production `BEq` on kernel expressions and universes deliberately compares
content addresses.  Closed representation fixtures instead need to decide
genuine inductive equality without assuming that Blake3 is injective.

The shapes below retain every semantic anonymous-mode field and erase only
metadata fields whose type is definitionally `Unit`.  Each shape has a
left-inverse back to the production datatype.  Equality reflected through
that left-inverse is therefore structural equality, not hash equality.
-/

namespace Ix.Tc
namespace AnonStructural

def addressDecidableEq : DecidableEq Address :=
  fun left right =>
    if h : left == right then
      .isTrue (eq_of_beq h)
    else
      .isFalse fun equality => h (by
        cases equality
        exact beq_self_eq_true left)

local instance : DecidableEq Address := addressDecidableEq

deriving instance DecidableEq for Lean.ReducibilityHints

inductive Univ where
  | zero (addr : Address)
  | succ (u : Univ) (addr : Address)
  | max (left right : Univ) (addr : Address)
  | imax (left right : Univ) (addr : Address)
  | param (idx : UInt64) (addr : Address)
  deriving DecidableEq

def Univ.ofKernel : KUniv .anon → Univ
  | .zero addr => .zero addr
  | .succ u addr => .succ (ofKernel u) addr
  | .max left right addr => .max (ofKernel left) (ofKernel right) addr
  | .imax left right addr => .imax (ofKernel left) (ofKernel right) addr
  | .param idx _ addr => .param idx addr

def Univ.toKernel : Univ → KUniv .anon
  | .zero addr => .zero addr
  | .succ u addr => .succ u.toKernel addr
  | .max left right addr => .max left.toKernel right.toKernel addr
  | .imax left right addr => .imax left.toKernel right.toKernel addr
  | .param idx addr => .param idx () addr

@[simp] theorem Univ.roundtrip (u : KUniv .anon) :
    (ofKernel u).toKernel = u := by
  induction u <;> simp [ofKernel, toKernel, *]

structure ExprInfo where
  addr : Address
  lbr : UInt64
  count0 : UInt64
  hasFVars : Bool
  deriving DecidableEq

def ExprInfo.ofKernel (info : Ix.Tc.ExprInfo .anon) : ExprInfo :=
  ⟨info.addr, info.lbr, info.count0, info.hasFVars⟩

def ExprInfo.toKernel (info : ExprInfo) : Ix.Tc.ExprInfo .anon :=
  ⟨info.addr, info.lbr, info.count0, info.hasFVars, (), (), ()⟩

@[simp] theorem ExprInfo.roundtrip (info : Ix.Tc.ExprInfo .anon) :
    (ofKernel info).toKernel = info := by
  cases info
  rfl

inductive Expr where
  | var (idx : UInt64) (info : ExprInfo)
  | fvar (id : FVarId) (info : ExprInfo)
  | sort (u : Univ) (info : ExprInfo)
  | const (id : Address) (us : Array Univ) (info : ExprInfo)
  | app (fn arg : Expr) (info : ExprInfo)
  | lam (type body : Expr) (info : ExprInfo)
  | all (type body : Expr) (info : ExprInfo)
  | letE (type value body : Expr) (nonDep : Bool) (info : ExprInfo)
  | prj (id : Address) (field : UInt64) (value : Expr) (info : ExprInfo)
  | nat (value : Nat) (blob : Address) (info : ExprInfo)
  | str (value : String) (blob : Address) (info : ExprInfo)
  deriving DecidableEq

def Expr.ofKernel : KExpr .anon → Expr
  | .var idx _ info => .var idx (ExprInfo.ofKernel info)
  | .fvar id _ info => .fvar id (ExprInfo.ofKernel info)
  | .sort u info => .sort (Univ.ofKernel u) (ExprInfo.ofKernel info)
  | .const id us info =>
      .const id.addr (us.map Univ.ofKernel) (ExprInfo.ofKernel info)
  | .app fn arg info =>
      .app (ofKernel fn) (ofKernel arg) (ExprInfo.ofKernel info)
  | .lam _ _ type body info =>
      .lam (ofKernel type) (ofKernel body) (ExprInfo.ofKernel info)
  | .all _ _ type body info =>
      .all (ofKernel type) (ofKernel body) (ExprInfo.ofKernel info)
  | .letE _ type value body nonDep info =>
      .letE (ofKernel type) (ofKernel value) (ofKernel body) nonDep
        (ExprInfo.ofKernel info)
  | .prj id field value info =>
      .prj id.addr field (ofKernel value) (ExprInfo.ofKernel info)
  | .nat value blob info => .nat value blob (ExprInfo.ofKernel info)
  | .str value blob info => .str value blob (ExprInfo.ofKernel info)

def Expr.toKernel : Expr → KExpr .anon
  | .var idx info => .var idx () info.toKernel
  | .fvar id info => .fvar id () info.toKernel
  | .sort u info => .sort u.toKernel info.toKernel
  | .const id us info =>
      .const ⟨id, ()⟩ (us.map Univ.toKernel) info.toKernel
  | .app fn arg info => .app fn.toKernel arg.toKernel info.toKernel
  | .lam type body info => .lam () () type.toKernel body.toKernel info.toKernel
  | .all type body info => .all () () type.toKernel body.toKernel info.toKernel
  | .letE type value body nonDep info =>
      .letE () type.toKernel value.toKernel body.toKernel nonDep info.toKernel
  | .prj id field value info =>
      .prj ⟨id, ()⟩ field value.toKernel info.toKernel
  | .nat value blob info => .nat value blob info.toKernel
  | .str value blob info => .str value blob info.toKernel

@[simp] theorem Expr.roundtrip (expr : KExpr .anon) :
    (ofKernel expr).toKernel = expr := by
  induction expr <;>
    simp [ofKernel, toKernel, Array.map_map, Function.comp_def, *,
      Univ.roundtrip, ExprInfo.roundtrip]

structure RecRule where
  fields : UInt64
  rhs : Expr
  deriving DecidableEq

def RecRule.ofKernel (rule : Ix.Tc.RecRule .anon) : RecRule :=
  ⟨rule.fields, Expr.ofKernel rule.rhs⟩

def RecRule.toKernel (rule : RecRule) : Ix.Tc.RecRule .anon :=
  ⟨(), rule.fields, rule.rhs.toKernel⟩

@[simp] theorem RecRule.roundtrip (rule : Ix.Tc.RecRule .anon) :
    (ofKernel rule).toKernel = rule := by
  cases rule
  simp [ofKernel, toKernel]

inductive Const where
  | defn (kind : Ix.DefKind) (safety : Ix.DefinitionSafety)
      (hints : Lean.ReducibilityHints) (lvls : UInt64)
      (type value : Expr) (block : Address)
  | recr (k isUnsafe : Bool) (lvls params indices motives minors : UInt64)
      (block : Address) (memberIdx : UInt64) (type : Expr)
      (rules : Array RecRule)
  | axio (isUnsafe : Bool) (lvls : UInt64) (type : Expr)
  | quot (kind : Ix.QuotKind) (lvls : UInt64) (type : Expr)
  | indc (lvls params indices : UInt64) (isUnsafe : Bool)
      (block : Address) (memberIdx : UInt64) (type : Expr)
      (ctors : Array Address)
  | ctor (isUnsafe : Bool) (lvls : UInt64) (induct : Address)
      (cidx params fields : UInt64) (type : Expr)
  deriving DecidableEq

def Const.ofKernel : KConst .anon → Const
  | .defn _ _ kind safety hints lvls type value _ block =>
      .defn kind safety hints lvls (Expr.ofKernel type) (Expr.ofKernel value)
        block.addr
  | .recr _ _ k isUnsafe lvls params indices motives minors block memberIdx
      type rules _ =>
      .recr k isUnsafe lvls params indices motives minors block.addr memberIdx
        (Expr.ofKernel type) (rules.map RecRule.ofKernel)
  | .axio _ _ isUnsafe lvls type =>
      .axio isUnsafe lvls (Expr.ofKernel type)
  | .quot _ _ kind lvls type => .quot kind lvls (Expr.ofKernel type)
  | .indc _ _ lvls params indices isUnsafe block memberIdx type ctors _ =>
      .indc lvls params indices isUnsafe block.addr memberIdx
        (Expr.ofKernel type) (ctors.map KId.addr)
  | .ctor _ _ isUnsafe lvls induct cidx params fields type =>
      .ctor isUnsafe lvls induct.addr cidx params fields (Expr.ofKernel type)

def Const.toKernel : Const → KConst .anon
  | .defn kind safety hints lvls type value block =>
      .defn () () kind safety hints lvls type.toKernel value.toKernel ()
        ⟨block, ()⟩
  | .recr k isUnsafe lvls params indices motives minors block memberIdx type
      rules =>
      .recr () () k isUnsafe lvls params indices motives minors ⟨block, ()⟩
        memberIdx type.toKernel (rules.map RecRule.toKernel) ()
  | .axio isUnsafe lvls type => .axio () () isUnsafe lvls type.toKernel
  | .quot kind lvls type => .quot () () kind lvls type.toKernel
  | .indc lvls params indices isUnsafe block memberIdx type ctors =>
      .indc () () lvls params indices isUnsafe ⟨block, ()⟩ memberIdx
        type.toKernel (ctors.map fun addr => ⟨addr, ()⟩) ()
  | .ctor isUnsafe lvls induct cidx params fields type =>
      .ctor () () isUnsafe lvls ⟨induct, ()⟩ cidx params fields type.toKernel

@[simp] theorem Const.roundtrip (constant : KConst .anon) :
    (ofKernel constant).toKernel = constant := by
  cases constant <;>
    simp [ofKernel, toKernel, Array.map_map, Function.comp_def,
      Expr.roundtrip, RecRule.roundtrip]

def decidableEqOfRoundtrip {original view : Type} [DecidableEq view]
    (encode : original → view) (decode : view → original)
    (roundtrip : ∀ value, decode (encode value) = value) :
    DecidableEq original := fun left right =>
  if h : encode left = encode right then
    .isTrue <| by rw [← roundtrip left, ← roundtrip right, h]
  else
    .isFalse fun equality => h (congrArg encode equality)

def idDecidableEq : DecidableEq (KId .anon) :=
  decidableEqOfRoundtrip KId.addr (fun addr => ⟨addr, ()⟩) (by
    intro id
    cases id with
    | mk addr name =>
        cases name
        rfl)

/-- Structural anonymous-expression equality.  This compares the complete
inductive representation through `Expr`, not only production content
addresses. -/
def exprDecidableEq : DecidableEq (KExpr .anon) :=
  decidableEqOfRoundtrip Expr.ofKernel Expr.toKernel Expr.roundtrip

def constDecidableEq : DecidableEq (KConst .anon) :=
  decidableEqOfRoundtrip Const.ofKernel Const.toKernel Const.roundtrip

end AnonStructural
end Ix.Tc
