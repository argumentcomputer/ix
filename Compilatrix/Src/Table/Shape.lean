import Compilatrix.Src.Pinned

/-! Shared equation shape and binder-domain checks. -/

namespace Compilatrix.Src.Table

open Compilatrix.Ixon

/-- `param 0 … param (n-1)`. -/
def paramUnivs (n : Nat) : List Univ := (List.range n).map fun i => .var i.toUInt64

/-- `#(k-1) … #0`. -/
def boundVars (k : Nat) : List Term := (List.range k).reverse.map Term.var

def safeDefn? (p : Program) (c : CId) : Option (Nat × Term × Term) :=
  match p.decl? c with
  | some (.defn .defn .safe lvls type value) => some (lvls, type, value)
  | _ => none

/-- Match `app* (const Eq [l]) [B, lhs, rhs]` over the pinned `Eq`. -/
def eqApp? (p : Program) (t : Term) : Option (Term × Term × Term) :=
  match t.spine with
  | (.const c [_], [(ty, _), (lhs, _), (rhs, _)]) =>
    if some c == p.known.eq then some (ty, lhs, rhs) else none
  | _ => none

/-- Peel exactly `k` leading Π binders. -/
def peelPis : Nat → Term → Option (List (Binder × Term) × Term)
  | 0, t => some ([], t)
  | k + 1, .pi b _ d t => do
    let (bs, body) ← peelPis k t
    return ((b, d) :: bs, body)
  | _ + 1, _ => none

/-! ## Binder wrappers

Lean's `eq_def` states its binders without the `autoParam`/`optParam`
wrappers the definition's type may carry. A wrapper is recognised by its
body, not its address: a safe definition whose value is exactly `λ _. #0` or
`λ _ _. #1`, so one δ step and β give its first argument, and the two domains
are definitionally equal (the bridge's R6 step takes that δ step). -/

/-- Arity of an identity-like wrapper definition. -/
def wrapperArity? (p : Program) (c : CId) : Option Nat :=
  match safeDefn? p c with
  | some (_, _, .lam _ _ (.var 0)) => some 1
  | some (_, _, .lam _ _ (.lam _ _ (.var 1))) => some 2
  | _ => none

/-- Contract an application node whose (already stripped) spine is a
wrapper applied to exactly its arity. -/
def contractWrapper (p : Program) (t : Term) : Term :=
  match t.spine with
  | (.const c _, args) =>
    match wrapperArity? p c, args.head? with
    | some n, some (first, _) => if args.length == n then first else t
    | _, _ => t
  | _ => t

/-- Remove saturated wrapper applications everywhere, bottom-up. -/
def stripWrappers (p : Program) : Term → Term
  | .app f a m r => contractWrapper p (.app (stripWrappers p f) (stripWrappers p a) m r)
  | .lam b d t => .lam b (stripWrappers p d) (stripWrappers p t)
  | .pi b r d t => .pi b r (stripWrappers p d) (stripWrappers p t)
  | .letE c r ty v b => .letE c r (stripWrappers p ty) (stripWrappers p v) (stripWrappers p b)
  | .proj s i e => .proj s i (stripWrappers p e)
  | t => t

/-- Domain agreement of check 3: equal once binder wrappers are removed. -/
def domainEqv (p : Program) (a b : Term) : Bool :=
  a.eqv b || (stripWrappers p a).eqv (stripWrappers p b)

end Compilatrix.Src.Table
