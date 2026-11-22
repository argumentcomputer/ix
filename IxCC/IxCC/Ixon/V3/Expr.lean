import IxCC.Ixon.Univ
import IxCC.Ixon.V3.Contracts

/-! Ixon v5 expressions. Binder modes live in the record's binder-data section
(`Constant.binders`), while `let` carries its dependency flag and `LetMode`
directly on the expression node. Their canonical bytes are the Ixon v5 encoding
of `IxCC.Ixon.V3.Wire`, read and written by ix's codec. -/

namespace IxCC.Ixon.V3

inductive Expr where
  | sort : UInt64 → Expr
  | var : UInt64 → Expr
  | ref : UInt64 → Array UInt64 → Expr
  | recur : UInt64 → Array UInt64 → Expr
  | prj : UInt64 → UInt64 → Expr → Expr
  | str : UInt64 → Expr
  | nat : UInt64 → Expr
  | app : Expr → Expr → Expr
  | lam : Expr → Expr → Expr
  | all : Expr → Expr → Expr
  | letE : (nonDep : Bool) → LetMode → Expr → Expr → Expr → Expr
  | share : UInt64 → Expr
  deriving BEq, DecidableEq, Repr, Inhabited, Hashable

namespace Expr

def leanLam (ty body : Expr) : Expr := .lam ty body
def leanAll (ty body : Expr) : Expr := .all ty body
def leanLet (nonDep : Bool) (ty val body : Expr) : Expr := .letE nonDep (.value .many) ty val body

def codecSize : Expr → Nat
  | .sort _ | .var _ | .ref _ _ | .recur _ _ | .str _ | .nat _ | .share _ => 1
  | .prj _ _ e => e.codecSize + 1
  | .app f a => f.codecSize + a.codecSize + 1
  | .lam d b | .all d b => d.codecSize + b.codecSize + 1
  | .letE _ _ t v b => t.codecSize + v.codecSize + b.codecSize + 1

/-- Wire telescopes can contain many AST binders at one parser depth.
Check semantic depth with bounded recursion before canonical reencoding. -/
def withinDepth : Nat → Expr → Bool
  | 0, _ => false
  | fuel + 1, e => match e with
    | .prj _ _ e => withinDepth fuel e
    | .app f a => withinDepth fuel f && withinDepth fuel a
    | .lam t b | .all t b => withinDepth fuel t && withinDepth fuel b
    | .letE _ _ t v b => withinDepth fuel t && withinDepth fuel v && withinDepth fuel b
    | _ => true

def appCount : Expr → Nat
  | .app f _ => f.appCount + 1
  | _ => 0

def lamCount : Expr → Nat
  | .lam _ b => b.lamCount + 1
  | _ => 0

def allCount : Expr → Nat
  | .all _ b => b.allCount + 1
  | _ => 0

/-- Whether every `let` inside `e` carries the default mode (`value .many`).
Binder modes on `lam` and `all` live in the record's binder-data section. -/
def leanFragment : Expr → Bool
  | .lam d b | .all d b => leanFragment d && leanFragment b
  | .letE _ m t v b => m.isDefault && leanFragment t && leanFragment v && leanFragment b
  | .app f a => leanFragment f && leanFragment a
  | .prj _ _ e => leanFragment e
  | _ => true

def collectLam : Expr → List Expr × Expr
  | .lam t b =>
    let (doms, body) := collectLam b
    (t :: doms, body)
  | e => ([], e)

def collectAll : Expr → List Expr × Expr
  | .all t b =>
    let (doms, body) := collectAll b
    (t :: doms, body)
  | e => ([], e)

end Expr

end IxCC.Ixon.V3
