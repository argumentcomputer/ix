module
public import Ix.Ixon.Wire
import all Ix.Ixon.Wire
import all Ix.Ixon.Codec

public section

namespace Ixon.WireCheck

/-- Retain the successor-prefix count while checking each universe once. -/
structure UnivSummary (u : Univ) where
  count : Nat
  count_eq : count = u.succCountNat
  valid : u.wireWF

def checkUniv : (u : Univ) → Option (UnivSummary u)
  | .zero => some ⟨0, rfl, True.intro⟩
  | .var _ => some ⟨0, rfl, True.intro⟩
  | .succ inner => do
    let child ← checkUniv inner
    if h : child.count + 1 < UInt64.size then
      return ⟨child.count + 1,
        by simp [Univ.succCountNat, child.count_eq, Nat.add_comm],
        by exact ⟨by simpa [child.count_eq, Univ.succCountNat, Nat.add_comm] using h,
          child.valid⟩⟩
    else none
  | .max left right => do
    let left ← checkUniv left
    let right ← checkUniv right
    return ⟨0, rfl, left.valid, right.valid⟩
  | .imax left right => do
    let left ← checkUniv left
    let right ← checkUniv right
    return ⟨0, rfl, left.valid, right.valid⟩

/-- Telescope counts travel with the recursive result, avoiding repeated
traversals of application and binder spines. All proof fields erase. -/
structure ExprSummary (e : Expr) where
  apps : Nat
  lams : Nat
  alls : Nat
  apps_eq : apps = e.appCount
  lams_eq : lams = e.lamCount
  alls_eq : alls = e.allCount
  valid : e.wireWF

def checkExpr : (e : Expr) → Option (ExprSummary e)
  | .sort _ => some ⟨0, 0, 0, rfl, rfl, rfl, True.intro⟩
  | .var _ => some ⟨0, 0, 0, rfl, rfl, rfl, True.intro⟩
  | .str _ => some ⟨0, 0, 0, rfl, rfl, rfl, True.intro⟩
  | .nat _ => some ⟨0, 0, 0, rfl, rfl, rfl, True.intro⟩
  | .share _ => some ⟨0, 0, 0, rfl, rfl, rfl, True.intro⟩
  | .ref _ idxs =>
    if h : idxs.size < UInt64.size then some ⟨0, 0, 0, rfl, rfl, rfl, h⟩ else none
  | .recur _ idxs =>
    if h : idxs.size < UInt64.size then some ⟨0, 0, 0, rfl, rfl, rfl, h⟩ else none
  | .prj _ _ value => do
    let value ← checkExpr value
    return ⟨0, 0, 0, rfl, rfl, rfl, value.valid⟩
  | .app fn arg => do
    let fn ← checkExpr fn
    let arg ← checkExpr arg
    if h : fn.apps + 1 < UInt64.size then
      return ⟨fn.apps + 1, 0, 0, by simp [Expr.appCount, fn.apps_eq], rfl, rfl,
        fn.valid, arg.valid, by simpa [fn.apps_eq] using h⟩
    else none
  | .lam _ ty body => do
    let ty ← checkExpr ty
    let body ← checkExpr body
    if h : body.lams + 1 < UInt64.size then
      return ⟨0, body.lams + 1, 0, rfl, by simp [Expr.lamCount, body.lams_eq], rfl,
        ty.valid, body.valid, by simpa [body.lams_eq] using h⟩
    else none
  | .all _ _ ty body => do
    let ty ← checkExpr ty
    let body ← checkExpr body
    if h : body.alls + 1 < UInt64.size then
      return ⟨0, 0, body.alls + 1, rfl, rfl, by simp [Expr.allCount, body.alls_eq],
        ty.valid, body.valid, by simpa [body.alls_eq] using h⟩
    else none
  | .letE _ ty value body => do
    let ty ← checkExpr ty
    let value ← checkExpr value
    let body ← checkExpr body
    return ⟨0, 0, 0, rfl, rfl, rfl, ty.valid, value.valid, body.valid⟩

def validUniv (u : Univ) : Bool := (checkUniv u).isSome
def validExpr (e : Expr) : Bool := (checkExpr e).isSome

def validArray (values : Array α) (valid : α → Bool) : Bool :=
  decide (values.size < UInt64.size) && values.all valid

def validDefinition (d : Definition) : Bool := validExpr d.typ && validExpr d.value

def validRecursor (r : Recursor) : Bool :=
  validExpr r.typ && validArray r.rules (fun rule => validExpr rule.rhs)

def validInductive (i : Inductive) : Bool :=
  validExpr i.typ && validArray i.ctors (fun ctor => validExpr ctor.typ)

def validMutConst : MutConst → Bool
  | .defn d => validDefinition d
  | .indc i => validInductive i
  | .recr r => validRecursor r

def validInfo : ConstantInfo → Bool
  | .defn d => validDefinition d
  | .recr r => validRecursor r
  | .axio a => validExpr a.typ
  | .quot q => validExpr q.typ
  | .cPrj p => p.block.hash.size == 32
  | .rPrj p => p.block.hash.size == 32
  | .iPrj p => p.block.hash.size == 32
  | .dPrj p => p.block.hash.size == 32
  | .muts members => validArray members validMutConst

/-- Decide exactly the production wire domain, including all side tables.
This checks representation; it does not assert typing or canonical block order. -/
def validConstant (constant : Constant) : Bool :=
  validInfo constant.info && validArray constant.sharing validExpr &&
    validArray constant.refs (fun address => address.hash.size == 32) &&
    validArray constant.univs validUniv

end Ixon.WireCheck
