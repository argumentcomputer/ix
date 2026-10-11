module
public import Ix.Environment
public section

namespace Ix.Compile.Image.TotalSpec

open Ix (Expr)

/-! Total specifications of the four fuel-free development helpers.
These clauses are copied exactly from the existing proved conversion core;
the separate bridge proves equality to those original definitions. -/

/-- `Ix.Compile.Image.looseRange` without its table. -/
def looseRangeP : Expr → Nat
  | .bvar i _ => i + 1
  | .app f a _ => max (looseRangeP f) (looseRangeP a)
  | .lam _ t b _ _ => max (looseRangeP t) (looseRangeP b - 1)
  | .forallE _ t b _ _ => max (looseRangeP t) (looseRangeP b - 1)
  | .letE _ t v b _ _ => max (max (looseRangeP t) (looseRangeP v)) (looseRangeP b - 1)
  | .proj _ _ s _ => looseRangeP s
  | .mdata _ s _ => looseRangeP s
  | .fvar .. | .mvar .. | .sort .. | .const .. | .lit .. => 0

/-- `Ix.Compile.Image.liftM` without its table. -/
def liftP (e : Expr) (n c : Nat) : Expr :=
  if n == 0 then e else if looseRangeP e ≤ c then e else
  match e with
  | .bvar i _ => if i ≥ c then Expr.mkBVar (i + n) else e
  | .app f a _ => Expr.mkApp (liftP f n c) (liftP a n c)
  | .lam nm t b bi _ => Expr.mkLam nm (liftP t n c) (liftP b n (c + 1)) bi
  | .forallE nm t b bi _ => Expr.mkForallE nm (liftP t n c) (liftP b n (c + 1)) bi
  | .letE nm t v b nd _ => Expr.mkLetE nm (liftP t n c) (liftP v n c) (liftP b n (c + 1)) nd
  | .proj nm i s _ => Expr.mkProj nm i (liftP s n c)
  | .mdata md x _ => Expr.mkMData md (liftP x n c)
  | .fvar .. | .mvar .. | .sort .. | .const .. | .lit .. => e

/-- `Ix.Compile.Image.lowerM` without its table. -/
def lowerP (e : Expr) (n c : Nat) : Expr :=
  if n == 0 then e else if looseRangeP e ≤ c then e else
  match e with
  | .bvar i _ => if i ≥ c + n then Expr.mkBVar (i - n) else e
  | .app f a _ => Expr.mkApp (lowerP f n c) (lowerP a n c)
  | .lam nm t b bi _ => Expr.mkLam nm (lowerP t n c) (lowerP b n (c + 1)) bi
  | .forallE nm t b bi _ => Expr.mkForallE nm (lowerP t n c) (lowerP b n (c + 1)) bi
  | .letE nm t v b nd _ => Expr.mkLetE nm (lowerP t n c) (lowerP v n c) (lowerP b n (c + 1)) nd
  | .proj nm i s _ => Expr.mkProj nm i (lowerP s n c)
  | .mdata md x _ => Expr.mkMData md (lowerP x n c)
  | .fvar .. | .mvar .. | .sort .. | .const .. | .lit .. => e

/-- `Ix.Compile.Image.occursM` without its table. -/
def occursP (e : Expr) (k : Nat) : Bool :=
  if looseRangeP e ≤ k then false else
  match e with
  | .bvar i _ => i == k
  | .app f a _ => occursP f k || occursP a k
  | .lam _ t b _ _ => occursP t k || occursP b (k + 1)
  | .forallE _ t b _ _ => occursP t k || occursP b (k + 1)
  | .letE _ t v b _ _ => occursP t k || occursP v k || occursP b (k + 1)
  | .proj _ _ s _ => occursP s k
  | .mdata _ s _ => occursP s k
  | .fvar .. | .mvar .. | .sort .. | .const .. | .lit .. => false

end Ix.Compile.Image.TotalSpec
