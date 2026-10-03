import Compilatrix.Ixon.Expr
import Compilatrix.Ixon.V3.Contracts

/-! Ixon expressions with all committed source contracts (the data model
introduced by Ixon v3 and kept by v4). Their canonical bytes are the Ixon v4
encoding of `Compilatrix.Ixon.V3.Wire`, read and written by ix's codec. -/

namespace Compilatrix.Ixon.V3

inductive Expr where
  | sort : UInt64 → Expr
  | var : UInt64 → Expr
  | ref : UInt64 → Array UInt64 → Expr
  | recur : UInt64 → Array UInt64 → Expr
  | prj : UInt64 → UInt64 → Expr → Expr
  | str : UInt64 → Expr
  | nat : UInt64 → Expr
  | app : Expr → Expr → Expr
  | lam : BinderContract → Expr → Expr → Expr
  | all : BinderContract → ValueContract → Expr → Expr → Expr
  | letE : LetContract → Expr → Expr → Expr → Expr
  | share : UInt64 → Expr
  deriving BEq, DecidableEq, Repr, Inhabited, Hashable

namespace Expr

def codecSize : Expr → Nat
  | .sort _ | .var _ | .ref _ _ | .recur _ _ | .str _ | .nat _ | .share _ => 1
  | .prj _ _ e => e.codecSize + 1
  | .app f a => f.codecSize + a.codecSize + 1
  | .lam _ d b | .all _ _ d b => d.codecSize + b.codecSize + 1
  | .letE _ t v b => t.codecSize + v.codecSize + b.codecSize + 1

/-- Wire telescopes can contain many AST binders at one parser depth.
Check semantic depth with bounded recursion before canonical reencoding. -/
def withinDepth : Nat → Expr → Bool
  | 0, _ => false
  | fuel + 1, e => match e with
    | .prj _ _ e => withinDepth fuel e
    | .app f a => withinDepth fuel f && withinDepth fuel a
    | .lam _ t b | .all _ _ t b => withinDepth fuel t && withinDepth fuel b
    | .letE _ t v b => withinDepth fuel t && withinDepth fuel v && withinDepth fuel b
    | _ => true

def appCount : Expr → Nat
  | .app f _ => f.appCount + 1
  | _ => 0

def lamCount : Expr → Nat
  | .lam _ _ b => b.lamCount + 1
  | _ => 0

def allCount : Expr → Nat
  | .all _ _ _ b => b.allCount + 1
  | _ => 0

/-- Ordinary source has many/shared/unrestricted inputs and results, with
ordinary lets. An erased/implicit binder is not inferred from its position. -/
def leanFragment : Expr → Bool
  | .lam c d b => c == .many && leanFragment d && leanFragment b
  | .all c r d b => c == .many && r == .shared && leanFragment d && leanFragment b
  | .letE c t v b => c.kind == .value && c.binder == .many &&
      leanFragment t && leanFragment v && leanFragment b
  | .app f a => leanFragment f && leanFragment a
  | .prj _ _ e => leanFragment e
  | _ => true

def collectLam : Expr → List (BinderContract × Expr) × Expr
  | .lam c t b =>
    let (binders, body) := collectLam b
    ((c, t) :: binders, body)
  | e => ([], e)

end Expr

end Compilatrix.Ixon.V3
