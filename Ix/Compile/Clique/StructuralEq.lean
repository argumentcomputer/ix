/-
  Regenerate a structural member's equation proof over the transported
  definitions. The old proof is deliberately not an input to the recipe:
  its brecOn.go/eq, packed tuples and splitter motives use the source order.

  The first supported recipe splits an unindexed recursive argument using
  its actual casesOn declaration and closes every branch by conversion and
  Eq.refl. Trailing dependent binders stay inside the motive. Indexed or
  otherwise unsupported telescopes, missing input declarations and failed
  conversion checks return an error; Structural keeps its existing refusal.
  This is a bounded proof constructor, not a new source-domain restriction.
-/
module
public import Ix.Compile.Clique.Telescope
public import Ix.Compile.Clique.Whnf
public section

namespace Ix.Compile.Clique

open Ix (Name Level Expr ConstantInfo)
open Ix.Compile.Canon (getAppFnArgs mkAppN stripMdata substLevels)
open Ix.Compile.Image (Local)

/-- Proof admission never treats a cached digest as an equality witness. -/
def eqDefNameEq : Name → Name → Bool
  | .anonymous _, .anonymous _ => true
  | .str a x _, .str b y _ => x == y && eqDefNameEq a b
  | .num a x _, .num b y _ => x == y && eqDefNameEq a b
  | _, _ => false

def eqDefLevelEq : Level → Level → Bool
  | .zero _, .zero _ => true
  | .succ a _, .succ b _ => eqDefLevelEq a b
  | .max a b _, .max c d _ | .imax a b _, .imax c d _ =>
    eqDefLevelEq a c && eqDefLevelEq b d
  | .param a _, .param b _ | .mvar a _, .mvar b _ => eqDefNameEq a b
  | _, _ => false

def eqDefLevelsEq (a b : Array Level) : Bool :=
  a.size == b.size && (a.zip b).all (fun (x, y) => eqDefLevelEq x y)

/-- Alpha equality with structural names/levels, ignoring metadata and all
stored hashes. No memo hit can admit an unequal proof branch. -/
def eqDefExprEq : Expr → Expr → Bool
  | .mdata _ a _, b => eqDefExprEq a b
  | a, .mdata _ b _ => eqDefExprEq a b
  | .bvar a _, .bvar b _ => a == b
  | .fvar a _, .fvar b _ | .mvar a _, .mvar b _ => eqDefNameEq a b
  | .sort a _, .sort b _ => eqDefLevelEq a b
  | .const a us _, .const b vs _ => eqDefNameEq a b && eqDefLevelsEq us vs
  | .app f a _, .app g b _ => eqDefExprEq f g && eqDefExprEq a b
  | .lam _ a b _ _, .lam _ c d _ _ | .forallE _ a b _ _, .forallE _ c d _ _ =>
    eqDefExprEq a c && eqDefExprEq b d
  | .letE _ t v b _ _, .letE _ t' v' b' _ _ =>
    eqDefExprEq t t' && eqDefExprEq v v' && eqDefExprEq b b'
  | .lit a _, .lit b _ => a == b
  | .proj s i a _, .proj t j b _ => i == j && eqDefNameEq s t && eqDefExprEq a b
  | _, _ => false

/-- A sufficient conversion check, using only beta/delta/zeta/iota and
projection reduction from the existing structural reducer. Exhaustion or
an unsupported conversion refuses the branch; it never assumes equality.
Equal subterms are compared before delta reduction, keeping shared recursive
calls opaque when their actual syntax already agrees. -/
def eqDefConvertible (const? : Name → Option ConstantInfo) : Nat → Expr → Expr → Bool
  | 0, _, _ => false
  | fuel + 1, a, b =>
    if eqDefExprEq a b then true else
    let a := whnf const? whnfFuel a
    let b := whnf const? whnfFuel b
    if eqDefExprEq a b then true else
    match stripMdata a, stripMdata b with
    | .app f x _, .app g y _ =>
      eqDefConvertible const? fuel f g && eqDefConvertible const? fuel x y
    | .lam _ t x _ _, .lam _ u y _ _ | .forallE _ t x _ _, .forallE _ u y _ _ =>
      eqDefConvertible const? fuel t u && eqDefConvertible const? fuel x y
    | .proj s i x _, .proj t j y _ =>
      i == j && eqDefNameEq s t && eqDefConvertible const? fuel x y
    | _, _ => false

/-- Read a proposition after reduction; retain its exact equality universe. -/
def eqDefEquality (const? : Name → Option ConstantInfo) (type : Expr) :
    Except String (Array Level × Array Expr) := do
  let some (head, us, args) := constApp? (whnf const? whnfFuel type)
    | throw "structural eq_def: branch is not an equality"
  unless eqDefNameEq head (leanName ``Eq) && us.size == 1 && args.size == 3 do
    throw "structural eq_def: branch is not an equality"
  return (us, args)

/-- Introduce the actual alternative fields and trailing dependent binders,
then generate reflexivity only after checking both sides by conversion. -/
def eqDefReflLeaf (const? : Name → Option ConstantInfo) : Nat → Expr → TM Expr
  | 0, _ => throw "structural eq_def: branch telescope bound exhausted"
  | fuel + 1, type => do
    let type := whnf const? whnfFuel type
    match stripMdata type with
    | .forallE nm dom body bi _ =>
      let fvar ← freshFVar
      let x : Local := { fvar, userName := nm, type := dom, bi }
      let proof ← eqDefReflLeaf const? fuel (instantiateRev body #[x.expr])
      return mkLambda #[x] proof
    | _ =>
      let (us, args) ← liftE (eqDefEquality const? type)
      unless eqDefConvertible const? 256 args[1]! args[2]! do
        throw "structural eq_def: constructor branch does not close by conversion"
      return mkAppN (Expr.mkConst (leanName ``Eq.refl) us) #[args[0]!, args[1]!]

/-- Regenerate `member.eq_def` over a lookup containing all transported
members and functionals. The unchanged statement must apply that exact member
to its complete ordered telescope. No source proof syntax is transported.
Only this new path has the stated grammar; all other cases retain the existing
compiler fallback, rather than narrowing any public compiler property. -/
def regenerateStructuralEq (const? : Name → Option ConstantInfo)
    (member equation : Decl) (newName : Name) (majorPos : Nat) : TM Decl := do
  unless equation.isThm && eqDefNameEq equation.name (Name.mkStr member.name "eq_def") do
    throw "structural eq_def: not the member's unfolding theorem"
  unless equation.levelParams.size == member.levelParams.size &&
      (equation.levelParams.zip member.levelParams).all (fun (a, b) => eqDefNameEq a b) do
    throw "structural eq_def: universe parameters differ from the member"
  let arity := Ix.Compile.Image.forallArity equation.type
  unless majorPos < arity do throw "structural eq_def: recursive binder is absent"
  let (_, conclusion) := Ix.Compile.Canon.peelForalls arity equation.type #[]
  let (_, eqArgs) ← liftE (eqDefEquality const? conclusion)
  let some (owner, levels, args) := constApp? eqArgs[1]!
    | throw "structural eq_def: left side is not the member application"
  unless eqDefNameEq owner member.name &&
      eqDefLevelsEq levels (member.levelParams.map Level.mkParam) && args.size == arity &&
      (args.zipIdx).all (fun (a, i) => eqDefExprEq a (Expr.mkBVar (arity - 1 - i))) do
    throw "structural eq_def: left side is not the complete ordered member application"
  unless (const? (leanName ``Eq.refl)).isSome do
    throw "structural eq_def: Eq.refl is not in the input"
  let (prefix, goal) ← openBinders false (majorPos + 1) equation.type
  let major := prefix[majorPos]!
  let some (ind, indLevels, params) := constApp? (whnf const? whnfFuel major.type)
    | throw "structural eq_def: recursive argument has no inductive head"
  let some (.inductInfo iv) := const? ind
    | throw "structural eq_def: recursive argument is not an input inductive"
  unless iv.numIndices == 0 && params.size == iv.numParams do
    throw "structural eq_def: indexed recursive telescope needs dependent generalization"
  let casesName := Name.mkStr ind "casesOn"
  let some ci := const? casesName | throw "structural eq_def: casesOn is not in the input"
  let cv := ci.getCnst
  let casesLevels ←
    if cv.levelParams.size == indLevels.size + 1 then pure (#[Level.mkZero] ++ indLevels)
    else if cv.levelParams.size == indLevels.size then pure indLevels
    else throw "structural eq_def: casesOn universe telescope differs"
  let mut type := substLevels cv.levelParams casesLevels cv.type
  type ← liftE (Ix.Compile.Image.instForall type params)
  let .forallE _ motiveType _ _ _ := stripMdata type
    | throw "structural eq_def: casesOn has no motive"
  unless eqDefConvertible const? 256 motiveType (mkForall #[major] (Expr.mkSort Level.mkZero)) do
    throw "structural eq_def: casesOn motive is not the recursive-argument predicate"
  let motive := mkLambda #[major] goal
  type ← liftE (Ix.Compile.Image.instForall type #[motive])
  let .forallE _ majorType _ _ _ := stripMdata type
    | throw "structural eq_def: casesOn has no major"
  unless eqDefConvertible const? 256 majorType major.type do
    throw "structural eq_def: casesOn major type differs"
  type ← liftE (Ix.Compile.Image.instForall type #[major.expr])
  let mut proofArgs := params ++ #[motive, major.expr]
  for _ in iv.ctors do
    let .forallE _ alternative _ _ _ := stripMdata type
      | throw "structural eq_def: casesOn has too few alternatives"
    let proof ← eqDefReflLeaf const? 256 alternative
    proofArgs := proofArgs.push proof
    type ← liftE (Ix.Compile.Image.instForall type #[proof])
  unless eqDefConvertible const? 256 type goal do
    throw "structural eq_def: casesOn result differs from the full statement"
  let value ← liftE (closeBinders true prefix (mkAppN (Expr.mkConst casesName casesLevels) proofArgs))
  return { equation with name := newName, value }

end Ix.Compile.Clique

end
