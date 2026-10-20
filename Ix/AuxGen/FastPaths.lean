/-
  Ix.AuxGen.FastPaths: what AuxGen's IxC arm answers from the input's
  declarations alone, without the Source service (AuxGen M2, M4).

  * `fastLevel`: the `inferAppType` fast path of `getLevel` (a constant
    applied to as many arguments as its type has leading `∀`s, whose body
    is a sort), spelled as `Ix.Tc` spells it (M2);
  * `stuckHead`: a term that is its own weak head normal form by its head
    alone (M4);
  * `recursorsMayAsk`: whether the recursor generator or the elimination
    decision can ask a block's question past these fast paths (M4's asks):
    the run-ahead folds such blocks ahead of their tails.

  Nothing here is trusted: a fast path answers only what the kernel would,
  by the kernels' own rules (`Ix.Tc`'s `tryInferAppSortLevel`, `whnfCore`'s
  stuck heads), and the shadow compares every answer with `Ix.Tc`'s.
-/
module
public import Ix.AuxGen.ExprUtils
public import Ix.AuxGen.Levels
public import Ix.AuxGen.LevelEgress
public section

namespace Ix.AuxGen.Ixc

/-! ## The fast path -/

/-- `Ix.Tc`'s `isNotZeroLevel`. -/
def isNotZero : Level → Bool
  | .succ _ _ => true
  | .max a b _ => isNotZero a || isNotZero b
  | .imax _ b _ => isNotZero b
  | _ => false

/-- `Ix.Tc`'s `kunivToLevelWithConstLevels` on a Lean level in `Ix.Tc`'s
shape (`Egress.normalize`): the head constant's level parameter `cLps[i]` is
its argument `us[i]`, `max` through `levelMax`, `imax` by Lean's `mk_imax`
rules. A parameter that is not the head's, or has no argument, is refused. -/
def constLevelSubst (cLps : Array Name) (us : Array Level) : Level → Except String Level
  | .zero _ => pure Level.mkZero
  | .succ u _ => return Level.mkSucc (← constLevelSubst cLps us u)
  | .max a b _ => return levelMax (← constLevelSubst cLps us a) (← constLevelSubst cLps us b)
  | .imax a b _ => do
    let la ← constLevelSubst cLps us a
    let lb ← constLevelSubst cLps us b
    return if isNotZero lb then levelMax la lb
      else if lb matches .zero _ then lb
      else if la matches .zero _ then lb
      else if la matches .succ (.zero _) _ then lb
      else if la == lb then la
      else Level.mkIMax la lb
  | .param n _ =>
    match cLps.findIdx? (· == n) with
    | some i =>
      match us[i]? with
      | some l => pure l
      | none => throw s!"fast path: constant universe argument index {i} out of range"
    | none => throw s!"fast path: level parameter {n.pretty} is not the head constant's"
  | .mvar _ _ => throw "fast path: level metavariable"

/-- A term with its metadata wrappers removed. -/
def stripMData : Expr → Expr
  | .mdata _ e _ => stripMData e
  | e => e

/-- **The `inferAppType` fast path** on the head's Lean type: `some` level
when `ty` is a constant applied to as many arguments as its type has leading
∀s and the body is a sort. -/
def fastLevel (get? : Name → Option ConstantInfo) (ty : Expr) : Except String (Option Level) := do
  let (head, args) := decomposeApps ty
  let .const name us _ := head | return none
  let some ci := get? name | return none
  let cv := ci.getCnst
  let mut cur := stripMData cv.type
  for _ in [0:args.size] do
    match cur with
    | .forallE _ _ body _ _ => cur := stripMData body
    | _ => return none
  let .sort u _ := cur | return none
  return some (← constLevelSubst cv.levelParams us (Egress.normalize u))

/-- A head constant no head reduction unfolds. -/
def stuckConst : Option ConstantInfo → Bool
  | some (.inductInfo _) | some (.ctorInfo _) | some (.axiomInfo _) | some (.opaqueInfo _) => true
  | some (.quotInfo q) => (q.kind matches .type)
  | _ => false

/-- **Whether `e` is its own weak head normal form by its head alone**: a
free variable, a sort, a `∀`, a literal, an unapplied `λ`, or a constant
that no head reduction unfolds (an inductive, a constructor, an axiom, an
opaque, the quotient type). A theorem, a definition, a recursor, a
projection, a `let` or a β-redex is not. -/
def stuckHead (get? : Name → Option ConstantInfo) (e : Expr) : Bool :=
  let (head, args) := decomposeApps (stripMData e)
  match stripMData head with
  | .fvar .. | .sort .. | .forallE .. | .lit .. => true
  | .lam .. => args.isEmpty
  | .const c _ _ => stuckConst (get? c)
  | _ => false

/-! ## M4's asks -/

/-- Whether `e` names a constant `isMember` holds of. -/
def mentionsConst (e : Expr) (isMember : Name → Bool) : Bool :=
  match e with
  | .const n _ _ => isMember n
  | .app f a _ => mentionsConst f isMember || mentionsConst a isMember
  | .lam _ t b _ _ | .forallE _ t b _ _ => mentionsConst t isMember || mentionsConst b isMember
  | .letE _ t v b _ _ =>
    mentionsConst t isMember || mentionsConst v isMember || mentionsConst b isMember
  | .mdata _ x _ | .proj _ _ x _ => mentionsConst x isMember
  | _ => false

/-- `stuckHead` on a term with loose bound variables, which stand for the
generator's free variables (stuck). -/
def stuckOpen (get? : Name → Option ConstantInfo) (e : Expr) : Bool :=
  match (decomposeApps (stripMData e)).1 with
  | .bvar .. => true
  | _ => stuckHead get? e

/-- The body of a term's syntactic `∀` telescope, with the binder domains,
outermost first. -/
def peelForalls (e : Expr) (doms : Array Expr := #[]) : Expr × Array Expr :=
  match e with
  | .mdata _ x _ => peelForalls x doms
  | .forallE _ d b _ _ => peelForalls b (doms.push d)
  | e => (e, doms)

/-- `fastLevel` on a term with loose bound variables over `doms`
(outermost first): a constant head as `fastLevel`, or a bound variable
whose binder's domain is syntactically a sort. -/
def fastOpen (get? : Name → Option ConstantInfo) (doms : Array Expr) (e : Expr) : Bool :=
  match (decomposeApps (stripMData e)).1 with
  | .bvar i _ => isSortDom (doms[doms.size - 1 - i]?)
  | _ => fastSome (fastLevel get? e)
where
  isSortDom : Option Expr → Bool
    | some d => ((stripMData d) matches .sort ..)
    | none => false
  fastSome : Except String (Option Level) → Bool
    | .ok (some _) => true
    | _ => false

/-- **Whether the recursor generator or the elimination decision can ask
block `members` a question past the fast paths** (AuxGen M4's asks, so the
run-ahead folds the block ahead of its tail):
* a mutual or nested block (its canonical layout may not be Lean's, so the
  canonical block is installed and checked);
* an inductive's type telescope ending in a head that is not stuck (an
  arity alias: `decomposeInductiveType`'s `whnf`);
* a constructor field that names a member of the block and whose domain's
  telescope ends in a head that is not stuck (`findRecTarget`'s and the IH
  builders' `whnf`; a field naming none is skipped);
* the elimination decision's field probe (a single inductive whose sort may
  be zero, with one constructor that has fields) on a field whose level the
  fast path cannot read.
A block this misses still gets its answers: its tail folds its groups on
its own copy of the snapshot at its first question (a "late ask"). -/
def recursorsMayAsk (get? : Name → Option ConstantInfo) (members : Array Name) : Bool := Id.run do
  let inds := members.filterMap fun n => match get? n with
    | some (.inductInfo v) => some v
    | _ => none
  if inds.isEmpty then return false
  if inds.size > 1 || inds.any (·.numNested > 0) then return true
  let blockNames := inds.foldl (init := (#[] : Array Name)) fun acc iv => acc ++ iv.all
  let isBlock (n : Name) : Bool := blockNames.any (Ix.Compile.ExactKey.nameEq · n)
  for iv in inds do
    let (target, _) := peelForalls iv.cnst.type
    if !(stripMData target matches .sort ..) && !stuckOpen get? target then return true
    let ctors := iv.ctors.filterMap fun c => match get? c with
      | some (.ctorInfo cv) => some cv
      | _ => none
    if ctors.size != iv.ctors.size then return true
    for cv in ctors do
      let (_, doms) := peelForalls cv.cnst.type
      for i in [cv.numParams:doms.size] do
        let dom := doms[i]?.getD (Expr.mkSort Level.mkZero)
        -- a field naming no member of the block is not asked about (AuxGen M4:
        -- `findRecTarget` skips it)
        if mentionsConst dom isBlock then
          let (body, _) := peelForalls dom
          if !stuckOpen get? body then return true
    -- the elimination decision's field probe
    let .sort u _ := stripMData target | return true
    if !isNotZero (Egress.normalize u) && ctors.size == 1 then
      if let some cv := ctors[0]? then
        let (_, doms) := peelForalls cv.cnst.type
        for i in [cv.numParams:doms.size] do
          if let some d := doms[i]? then
            if !fastOpen get? (doms.extract 0 i) d then return true
  return false

end Ix.AuxGen.Ixc

end
