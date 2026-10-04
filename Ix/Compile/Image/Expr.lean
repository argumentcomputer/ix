/-
  Ix.Compile.Image.Expr: the locally nameless toolkit of the image generator.

  The generator works on the compiler's own terms (`Ix.Expr`, the hashed
  mirror of `Lean.Expr` that `CompileM` compiles), as Pass 1 does. Binders are
  opened with fresh free variables (`Ix.Expr.fvar` with names under the
  reserved root `_img_fvar`, drawn from a counter in `GenM`), exactly the
  discipline of `MetaM`'s telescopes, but with the types carried by the
  generator itself (`Local`) instead of a local context: nothing here infers
  a type, reduces, or consults the kernel.

  * `GenM`: a counter for fresh variables over `Except String`;
  * `telescope`: open the leading `∀`s of a type (`forallTelescope`);
  * `mkLambda`/`mkForall`: close them again (`mkLambdaFVars`);
  * `alphaEq`: equality up to binder names and binder info (Lean's
    `Expr.eqv`, which the prototype's `==` used);
  * `etaReduce`: Lean's `Expr.eta`, by structural recursion;
  * `usedConstants` / `findApp?`: Lean's `Expr.getUsedConstants` and
    `Expr.find?` orders (pre-order, function before argument), which fix the
    candidate order of the eliminator choice (design document §4.1);
  * level helpers (`isAlwaysZero`, `motiveLevel`, `stripSort`).

  Every function is total: structural recursion, or recursion on an explicit
  bound with an error when it is exhausted.
-/
module
public import Ix.Environment
public import Ix.Compile.Canon.Expr
public section

namespace Ix.Compile.Image

open Ix (Name Level Expr ConstantInfo)
open Ix.Compile.Canon (peelForalls instantiateRev liftLoose lowerLoose getAppFnArgs mkAppN
  stripMdata)

/-! ## Names of the constants the construction uses -/

def leanName (n : Lean.Name) : Name := Ix.Name.fromLeanName n

def nPProd : Name := leanName ``PProd
def nPProdMk : Name := leanName ``PProd.mk
def nAnd : Name := leanName ``And
def nAndIntro : Name := leanName ``And.intro
def nTrue : Name := leanName ``True
def nTrueIntro : Name := leanName ``True.intro
def nEq : Name := leanName ``Eq
def nEqRefl : Name := leanName ``Eq.refl

def lvlZero : Level := Level.mkZero
def lvlOne : Level := Level.mkSucc Level.mkZero

/-! ## The generator monad -/

/-- The generator's state: a counter for fresh variables and a trace of the
eliminator choices (for the tests' logs). -/
structure GenState where
  next : Nat := 0
  log : Array String := #[]

/-- Fresh variables and a trace over `Except String`. Pure. -/
abbrev GenM := StateT GenState (Except String)

def GenM.run' {α} (x : GenM α) : Except String α := StateT.run' x {}

def GenM.trace (s : String) : GenM Unit := modify fun st => { st with log := st.log.push s }

def liftExcept {α} (x : Except String α) : GenM α :=
  match x with
  | .ok a => pure a
  | .error e => throw e

/-- A7 (D8): total array access in the generator: out of range is a named
error (the image of the block fails), never `default`. -/
def GenM.idx {α} (a : Array α) (i : Nat) (what : String) : GenM α :=
  match a[i]? with
  | some x => pure x
  | none => throw s!"image: {what}: index {i} out of range (size {a.size})"

/-- The reserved root of the generator's free variables. Inputs are closed
terms, so no input mentions it. -/
def fvarRoot : Name := Ix.Name.mkStr Ix.Name.mkAnon "_img_fvar"

def freshName : GenM Name :=
  modifyGet fun st => (Ix.Name.mkNat fvarRoot st.next, { st with next := st.next + 1 })

/-- An opened binder: its free variable, the user's binder name and info,
and its type (over earlier free variables). -/
structure Local where
  fvar : Name
  userName : Name
  type : Expr
  bi : Lean.BinderInfo
  deriving Inhabited

def Local.expr (l : Local) : Expr := Expr.mkFVar l.fvar

/-- The index of the free variable `e` among `xs`. -/
def fvarIdx? (xs : Array Local) (e : Expr) : Option Nat :=
  match e with
  | .fvar n _ => xs.findIdx? (·.fvar == n)
  | _ => none

/-! ## Opening and closing binders -/

/-- Number of leading `∀`s (through `mdata`). -/
def forallArity : Expr → Nat
  | .forallE _ _ b _ _ => forallArity b + 1
  | .mdata _ e _ => forallArity e
  | _ => 0

/-- Instantiate the loose variables of `e` with `xs`, the last one for
`bvar 0` (Lean's `instantiateRev`). -/
def instLocals (e : Expr) (xs : Array Expr) : Expr := instantiateRev e xs.reverse

/-- Open up to `n` leading `∀`s of `e` with fresh variables
(`forallBoundedTelescope`); `n` defaults to all of them. -/
def telescope (e : Expr) (n : Nat := forallArity e) : GenM (Array Local × Expr) := do
  let (bs, body) := peelForalls n e #[]
  let mut ls : Array Local := #[]
  for (nm, t, bi) in bs do
    let t' := instLocals t (ls.map (·.expr))
    let f ← freshName
    ls := ls.push { fvar := f, userName := nm, type := t', bi }
  return (ls, instLocals body (ls.map (·.expr)))

/-- The body of `∀ x₁ … xₙ, b` at the values `vs` (`instantiateForall`):
plain instantiation, no reduction. Fails when there are fewer binders. -/
def instForall (e : Expr) (vs : Array Expr) : Except String Expr := do
  let (bs, body) := peelForalls vs.size e #[]
  if bs.size != vs.size then throw "instForall: too few binders"
  return instLocals body vs

/-- Replace the free variables `xs` by loose bound variables, `xs.back` the
innermost (`Expr.abstract`). The term is locally closed. -/
def abstractFVars (xs : Array Name) (e : Expr) : Expr :=
  if xs.isEmpty then e else go e 0
where
  go : Expr → Nat → Expr
    | e@(.fvar n _), d =>
      match xs.idxOf? n with
      | some i => Expr.mkBVar (d + (xs.size - 1 - i))
      | none => e
    | .app f a _, d => Expr.mkApp (go f d) (go a d)
    | .lam nm t b bi _, d => Expr.mkLam nm (go t d) (go b (d + 1)) bi
    | .forallE nm t b bi _, d => Expr.mkForallE nm (go t d) (go b (d + 1)) bi
    | .letE nm t v b nd _, d => Expr.mkLetE nm (go t d) (go v d) (go b (d + 1)) nd
    | .proj nm i s _, d => Expr.mkProj nm i (go s d)
    | .mdata md x _, d => Expr.mkMData md (go x d)
    | e, _ => e

/-- `λ xs, b` (`isLam`) or `∀ xs, b`, binder types abstracted over the
earlier binders (`mkLambdaFVars`/`mkForallFVars`). -/
def mkBinders (isLam : Bool) (xs : Array Local) (b : Expr) : Expr := Id.run do
  let names := xs.map (·.fvar)
  let mut acc := abstractFVars names b
  for (x, i) in xs.zipIdx.reverse do
    let ty := abstractFVars (names.extract 0 i) x.type
    acc := if isLam then Expr.mkLam x.userName ty acc x.bi
      else Expr.mkForallE x.userName ty acc x.bi
  return acc

def mkLambda (xs : Array Local) (b : Expr) : Expr := mkBinders true xs b
def mkForall (xs : Array Local) (b : Expr) : Expr := mkBinders false xs b

/-! ## Comparisons and small reductions -/

/-- Equality up to binder names and binder info (Lean's `Expr.eqv`). -/
def alphaEq : Expr → Expr → Bool
  | .bvar i _, .bvar j _ => i == j
  | .fvar a _, .fvar b _ => a == b
  | .mvar a _, .mvar b _ => a == b
  | .sort u _, .sort v _ => u == v
  | .const a us _, .const b vs _ => a == b && us == vs
  | .app f a _, .app g b _ => alphaEq f g && alphaEq a b
  | .lam _ t b _ _, .lam _ t' b' _ _ => alphaEq t t' && alphaEq b b'
  | .forallE _ t b _ _, .forallE _ t' b' _ _ => alphaEq t t' && alphaEq b b'
  | .letE _ t v b _ _, .letE _ t' v' b' _ _ => alphaEq t t' && alphaEq v v' && alphaEq b b'
  | .lit a _, .lit b _ => a == b
  | .mdata _ a _, .mdata _ b _ => alphaEq a b
  | .proj s i a _, .proj s' i' b _ => s == s' && i == i' && alphaEq a b
  | _, _ => false

/-- `bvar i` occurs loose in `e`. -/
def hasLooseBVar (e : Expr) (i : Nat) : Bool := go e i
where
  go : Expr → Nat → Bool
    | .bvar j _, k => j == k
    | .app f a _, k => go f k || go a k
    | .lam _ t b _ _, k | .forallE _ t b _ _, k => go t k || go b (k + 1)
    | .letE _ t v b _ _, k => go t k || go v k || go b (k + 1)
    | .proj _ _ s _, k | .mdata _ s _, k => go s k
    | _, _ => false

/-- Lean's `Expr.eta`: `λ x. f x ↦ f` when `x ∉ f`, inner binders first. -/
def etaReduce : Expr → Expr
  | .lam n d b bi _ =>
    let b' := etaReduce b
    match b' with
    | .app f (.bvar 0 _) _ =>
      if !hasLooseBVar f 0 then lowerLoose f 1 0 else Expr.mkLam n d b' bi
    | _ => Expr.mkLam n d b' bi
  | e => e

/-- The head constant of an application spine. -/
def headConst? (e : Expr) : Option (Name × Array Level) :=
  match (getAppFnArgs e).1 with
  | .const n us _ => some (n, us)
  | _ => none

/-- The last argument of an application. -/
def appArg? : Expr → Option Expr
  | .app _ a _ => some a
  | _ => none

/-- Constants of `e` in first-occurrence order of a pre-order walk, function
before argument (Lean's `Expr.getUsedConstants`). -/
def usedConstants (e : Expr) : Array Name := (go e (#[], {})).1
where
  go : Expr → Array Name × Std.HashSet Name → Array Name × Std.HashSet Name
    | .const n _ _, (acc, seen) => if seen.contains n then (acc, seen) else (acc.push n, seen.insert n)
    | .app f a _, s => go a (go f s)
    | .lam _ t b _ _, s | .forallE _ t b _ _, s => go b (go t s)
    | .letE _ t v b _ _, s => go b (go v (go t s))
    | .proj _ _ x _, s | .mdata _ x _, s => go x s
    | _, s => s

/-- The first of two optional results (evaluated eagerly; both are cheap). -/
def first2 {α} : Option α → Option α → Option α
  | some a, _ => some a
  | none, b => b

/-- The first subterm satisfying `p` in a pre-order walk, function before
argument (Lean's `Expr.find?`). -/
def findSub? (p : Expr → Bool) (e : Expr) : Option Expr :=
  if p e then some e else
  match e with
  | .app f a _ => first2 (findSub? p f) (findSub? p a)
  | .lam _ t b _ _ => first2 (findSub? p t) (findSub? p b)
  | .forallE _ t b _ _ => first2 (findSub? p t) (findSub? p b)
  | .letE _ t v b _ _ => first2 (findSub? p t) (first2 (findSub? p v) (findSub? p b))
  | .proj _ _ x _ => findSub? p x
  | .mdata _ x _ => findSub? p x
  | _ => none

/-! ## Levels and sorts -/

/-- Lean's `Level.isAlwaysZero`. -/
def isAlwaysZero : Level → Bool
  | .zero _ => true
  | .max a b _ => isAlwaysZero a && isAlwaysZero b
  | .imax _ b _ => isAlwaysZero b
  | _ => false

/-- The sort at the end of a motive type (`motiveLevel`, prototype
`Lib.lean:131-134`). -/
def motiveLevel : Expr → Level
  | .forallE _ _ b _ _ => motiveLevel b
  | .mdata _ b _ => motiveLevel b
  | .sort l _ => l
  | _ => lvlZero

/-- A motive type with its sort replaced by `Sort 0` (`stripSort`), so that
motive types are compared up to their universe. -/
def stripSort : Expr → Expr
  | .forallE n t b bi _ => Expr.mkForallE n t (stripSort b) bi
  | .mdata _ b _ => stripSort b
  | .sort _ _ => Expr.mkSort lvlZero
  | e => e

/-- `.sort u ↦ u`. -/
def sortLevel? : Expr → Option Level
  | .sort u _ => some u
  | .mdata _ e _ => sortLevel? e
  | _ => none

end Ix.Compile.Image

end
