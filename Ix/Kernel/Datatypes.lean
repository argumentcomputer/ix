/-
  Kernel Datatypes: TypeInfo, TypedExpr, TypedConst.

  Simplified for environment-based kernel (no Value/Neutral/ValEnv).
  Parameterized over MetaMode for compile-time metadata erasure.
-/
import Ix.Kernel.Types

namespace Ix.Kernel

/-! ## TypeInfo -/

inductive TypeInfo (m : MetaMode) where
  | unit | proof | none
  | sort : Level m → TypeInfo m
  deriving Inhabited

/-! ## AddInfo -/

structure AddInfo (Info Body : Type) where
  info : Info
  body : Body
  deriving Inhabited

/-! ## TypedExpr -/

abbrev TypedExpr (m : MetaMode) := AddInfo (TypeInfo m) (Expr m)

/-! ## TypedConst -/

inductive TypedConst (m : MetaMode) where
  | «axiom»     : (type : TypedExpr m) → TypedConst m
  | «theorem»   : (type value : TypedExpr m) → TypedConst m
  | «inductive» : (type : TypedExpr m) → (struct : Bool) → TypedConst m
  | «opaque»    : (type value : TypedExpr m) → TypedConst m
  | definition  : (type value : TypedExpr m) → (part : Bool) → TypedConst m
  | constructor : (type : TypedExpr m) → (idx fields : Nat) → TypedConst m
  | recursor    : (type : TypedExpr m) → (params motives minors indices : Nat) → (k : Bool)
                  → (indAddr : Address) → (rules : Array (Nat × TypedExpr m)) → TypedConst m
  | quotient    : (type : TypedExpr m) → (kind : QuotKind) → TypedConst m
  deriving Inhabited

def TypedConst.type : TypedConst m → TypedExpr m
  | «axiom»     type ..
  | «theorem»   type ..
  | «inductive» type ..
  | «opaque»    type ..
  | definition  type ..
  | constructor type ..
  | recursor    type ..
  | quotient    type .. => type

/-! ## Accessors -/

namespace AddInfo

def expr (t : TypedExpr m) : Expr m := t.body

end AddInfo

/-! ## TypedExpr helpers -/

partial def TypedExpr.toImplicitLambda : TypedExpr m → TypedExpr m
  | .mk _ (.lam _ body _ _) => toImplicitLambda ⟨default, body⟩
  | x => x

/-! ## TypeInfo helpers -/

def TypeInfo.pp : TypeInfo m → String
  | .unit => ".unit"
  | .proof => ".proof"
  | .none => ".none"
  | .sort _ => ".sort"

end Ix.Kernel
