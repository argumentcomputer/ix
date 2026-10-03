/-
  Ix.Compile.Image.Develop: the development (design document §4.3, decision
  Q10) as hereditary substitution.

  `hinst v k e` substitutes `v` for the loose variable `bvar k` of `e` and
  contracts exactly the redexes that the substitution forms at the
  substituted positions, hereditarily:

  * **β**: an application whose head becomes a λ (`x a₁ … aₙ` with
    `x := λ y. b`) is contracted by substituting `a₁` in `b` with `hinst`
    again, so the redexes *that* substitution forms are contracted too, and
    so on (`happ`);
  * **projection of a constructor**: `.proj PProd i s` / `.proj And i s`
    where `s` became `PProd.mk α β a b` / `And.intro p q a b` ↦ the field;
  * **η**: `λ y. x a₁ … aₙ y` with `x := g` (not a λ) and `y ∉ g a₁ … aₙ`
    ↦ `g a₁ … aₙ`.

  Nothing else is reduced: redexes already present in `e` or in `v` are left
  as they are, and recursor applications are never ι-reduced (`ρ … (c fs)`
  stays), so a user's `T.rec … (c fs)` is still a redex of the user's after
  the rewrite.

  Termination is the typed argument of the design document (each hereditary
  step substitutes at a strictly smaller type). The functions are untyped, so
  they carry an explicit bound (`fuel`, decreasing on every call, i.e. a bound
  on the recursion depth) and fail loudly when it is exhausted; on well-typed
  input the depth is the term's depth plus the nesting of the motive and minor
  types, far below `defaultFuel`.

  The image construction uses this to instantiate the canonical recursor's
  motives in its minor types (`substFVars`), so that the image is created
  already developed (P3a); A3's call-site rewrite uses `instantiate` to
  replace `img(a) args` by the image body at `args` (P3b).
-/
module
public import Ix.Environment
public import Ix.Compile.Canon.Expr
public import Ix.Compile.Image.Expr
public section

namespace Ix.Compile.Image

open Ix (Name Level Expr)
open Ix.Compile.Canon (liftLoose lowerLoose getAppFnArgs mkAppN)

/-- How the head of a substituted term was formed. -/
inductive Created where
  /-- Not by the substitution. -/
  | no
  /-- It is the substituted value itself (possibly applied). -/
  | direct
  /-- It results from a contraction the substitution formed. -/
  | reduced
  deriving BEq, Inhabited

/-- `.proj S i (S.mk α β a b) ↦ a or b` for `PProd` and `And`. -/
def projCtor? (s : Name) (i : Nat) (e : Expr) : Option Expr :=
  let (h, args) := getAppFnArgs e
  match h with
  | .const c _ _ =>
    if args.size == 4 && i < 2 &&
        ((s == nPProd && c == nPProdMk) || (s == nAnd && c == nAndIntro)) then
      args[2 + i]?
    else none
  | _ => none

mutual
/-- `e[bvar k := v]`, contracting the redexes formed at the substituted
positions. `v`'s loose variables refer to the context outside `e`'s
binders; it is lifted under them. -/
def hinst : Nat → Expr → Nat → Expr → Except String (Expr × Created)
  | 0, _, _, _ => throw "development: out of fuel"
  | fuel + 1, v, k, e =>
    match e with
    | .bvar i _ =>
      if i == k then pure (liftLoose v k, .direct)
      else if i > k then pure (Expr.mkBVar (i - 1), .no)
      else pure (e, .no)
    | .app .. => do
      let (h, args) := getAppFnArgs e
      let mut args' : Array Expr := #[]
      for a in args do
        args' := args'.push (← hinst fuel v k a).1
      let (h', c) ← hinst fuel v k h
      match c, h' with
      | .no, _ => pure (mkAppN h' args', .no)
      | _, .lam .. => pure ((← happ fuel h' args'.toList), .reduced)
      | c, _ => pure (mkAppN h' args', c)
    | .proj s i x _ => do
      let (x', c) ← hinst fuel v k x
      match c with
      | .no => pure (Expr.mkProj s i x', .no)
      | _ =>
        match projCtor? s i x' with
        | some f => pure (f, .reduced)
        | none => pure (Expr.mkProj s i x', .no)
    | .lam n t b bi _ => do
      let (t', _) ← hinst fuel v k t
      let (b', c) ← hinst fuel v (k + 1) b
      match c, b' with
      | .direct, .app f (.bvar 0 _) _ =>
        if !hasLooseBVar f 0 then pure (lowerLoose f 1 0, .direct)
        else pure (Expr.mkLam n t' b' bi, .no)
      | _, _ => pure (Expr.mkLam n t' b' bi, .no)
    | .forallE n t b bi _ => do
      let (t', _) ← hinst fuel v k t
      let (b', _) ← hinst fuel v (k + 1) b
      pure (Expr.mkForallE n t' b' bi, .no)
    | .letE n t x b nd _ => do
      let (t', _) ← hinst fuel v k t
      let (x', _) ← hinst fuel v k x
      let (b', _) ← hinst fuel v (k + 1) b
      pure (Expr.mkLetE n t' x' b' nd, .no)
    | .mdata md x _ => do
      let (x', c) ← hinst fuel v k x
      pure (Expr.mkMData md x', c)
    | _ => pure (e, .no)

/-- `f a₁ … aₙ` with the β-redexes at the head contracted hereditarily. -/
def happ : Nat → Expr → List Expr → Except String Expr
  | 0, _, _ => throw "development: out of fuel"
  | fuel + 1, .lam _ _ b _ _, a :: rest => do
    let (b', _) ← hinst fuel a 0 b
    happ fuel b' rest
  | _ + 1, f, args => pure (mkAppN f args.toArray)
end

/-- A bound on the recursion depth of the development. -/
def defaultFuel : Nat := 1 <<< 16

/-- The developed application `f args` (P3b at a call site: `f` is the
image body, `args` the occurrence's arguments; arguments beyond `f`'s λs stay
applied). -/
def instantiate (f : Expr) (args : Array Expr) : Except String Expr :=
  happ defaultFuel f args.toList

/-- `e[xs := vs]` for free variables, developed. The values are locally
closed and do not mention `xs`. -/
def substFVars (xs : Array Name) (vs : Array Expr) (e : Expr) : Except String Expr := do
  if xs.size != vs.size then throw "substFVars: arity mismatch"
  let mut acc := abstractFVars xs e
  for i in (List.range xs.size).reverse do
    acc := (← hinst defaultFuel vs[i]! 0 acc).1
  return acc

end Ix.Compile.Image

end
