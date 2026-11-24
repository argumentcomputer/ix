module

public import IxCK.Kernel.Env
public import IxCK.Kernel.ExprOps

@[expose] public section

/-! # Executable wrapper and let-shape checks

The semantic relations and their soundness proofs remain in
`Semantics/Inductives/WrapRel` and `WrapRelFacts`.
-/

namespace Ix.Kernel.Semantics

open Ix.Kernel (Key Expr Level LevelParam ConstantInfo Literal)

/-- The arity of a value `λ x₁ … xₖ, x₁` (`k ≥ 1`) whose binders' zero-ness data are all `never`
(the λs are functions, never proofs), after `n` binders already passed. -/
def lamFirstArity : Expr md → Nat → Option Nat
  | .lam _ b m, n => if m.pw.isNever then lamFirstArity b (n + 1) else none
  | .bvar i, n => if 0 < n && i == n - 1 then some n else none
  | _, _ => none

/-- **A wrapper**: a constant stored as a definition whose value is `λ x₁ … xₖ, x₁`; its arity. -/
def wrapperArity (find? : Key md → Option (ConstantInfo md)) (w : Key md) : Option Nat :=
  match find? w with
  | some (.defnInfo _ v _) => lamFirstArity v 0
  | _ => none

/-- **One consumption**: a wrapper applied to exactly its arity leaves its first argument. -/
def consumeWrapper (find? : Key md → Option (ConstantInfo md)) (t : Expr md) : Option (Expr md) :=
  match t.getAppFn, t.getAppArgs with
  | .const w _, a :: rest => if wrapperArity find? w == some (rest.length + 1) then some a else none
  | _, _ => none

/-! ## A syntactic recognizer -/

/-- The number of nodes of a term. -/
def exprSize : Expr md → Nat
  | .fvar _ t => exprSize t + 1
  | .app f a => exprSize f + exprSize a + 1
  | .lam t b _ => exprSize t + exprSize b + 1
  | .forallE t b _ => exprSize t + exprSize b + 1
  | .letE t v b _ => exprSize t + exprSize v + exprSize b + 1
  | .proj _ _ e => exprSize e + 1
  | _ => 1

mutual

/-- `WrapRel`, at a budget of recursive steps. -/
def wrapRelB (find? : Key md → Option (ConstantInfo md)) : Nat → Expr md → Expr md → Bool
  | 0, _, _ => false
  | fuel + 1, g, d =>
    match g, d with
    | .letE t v b l, .letE t' v' b' _ =>
      (wrapRelB find? fuel t t' && wrapRelB find? fuel v v' && wrapRelB find? fuel b b') ||
        wrapRelB find? fuel (.letE t v b l) (b'.instantiate1Lift v')
    | g, .letE _ v' b' _ => wrapRelB find? fuel g (b'.instantiate1Lift v')
    | .bvar i, .bvar j => i == j
    | .fvar i t, .fvar j t' => i == j && wrapRelB find? fuel t t'
    | .sort u, .sort v => u == v
    | .const n us, .const n' us' => n == n' && us == us'
    | .lit l, .lit l' => l == l'
    | .app f a, .app f' a' => wrapRelB find? fuel f f' && wrapRelB find? fuel a a'
    | .lam t b m, .lam t' b' m' =>
      m.pw == m'.pw && wrapDomB find? fuel t t' && wrapRelB find? fuel b b'
    | .forallE t b m, .forallE t' b' m' =>
      m.pw == m'.pw && wrapDomB find? fuel t t' && wrapRelB find? fuel b b'
    | .proj s i e, .proj s' i' e' => s == s' && i == i' && wrapRelB find? fuel e e'
    | _, _ => false

/-- `WrapDom`, at a budget of recursive steps. -/
def wrapDomB (find? : Key md → Option (ConstantInfo md)) : Nat → Expr md → Expr md → Bool
  | 0, _, _ => false
  | fuel + 1, t, t' =>
    wrapRelB find? fuel t t' ||
      match consumeWrapper find? t with
      | some a => wrapDomB find? fuel a t'
      | none => false

end

/-- A sound incomplete recognizer for `WrapRel`, requiring syntactic level equality and using
a budget based on both terms' sizes. -/
def wrapRelOk (find? : Key md → Option (ConstantInfo md)) (g d : Expr md) : Bool :=
  wrapRelB find? (2 * (exprSize g + exprSize d) + 2) g d

/-- No `let` node (a free variable's type is not looked into). -/
def letFree : Expr md → Bool
  | .letE .. => false
  | .app f a => letFree f && letFree a
  | .lam t b _ => letFree t && letFree b
  | .forallE t b _ => letFree t && letFree b
  | .proj _ _ e => letFree e
  | _ => true


end Ix.Kernel.Semantics
