import IxCCGrounding.Check
import Std.Data.HashMap

/-!
# The direct route, decided (`IxCCGrounding.Direct.Check`)

**A Boolean check that every application site SrcEval may evaluate is typed**, read off stored
types and conversion, without a typing derivation: the hypothesis `SitesOk` of the landed
theorems, discharged where this check accepts (`IxCCGrounding.Direct.Sites`). Denotes-free, so
`tests-grounding` runs it on closure bytes, beside `groundCheck` (not one of its conjuncts).

* **Profiles.** A run term is checked once against the set of profiles of its constant's level
  parameters at which it is evaluated (which parameters are zero); every decision that reads a
  level assignment (a binder datum, a level's zero-ness) is required at each of them.
* **Spines.** Each maximal evaluated application spine is walked once, left to right, from its
  head's type (`dStep` per argument); the sites of its prefixes are accepted in order until the
  first refusal. A spine's width costs no fuel, nor does a telescope's (the arguments fitted
  against a `∀`-telescope, `fitsWith`; β through a λ-telescope, `betaStar`); a nested argument
  costs two levels (its check and its type's inference).
* **The reading by key** (`KTab`): a hash map built once per closure; `Env.find?` walks the
  reading's list of constants.
* **Conversion** (`convD`): syntactic equality; equality up to what the denotation does not read
  (`eqUpTo`: levels by `lvlEq`, binder data at the profiles, a literal against its constructor
  form); β with each argument checked; δ (`Laws.defn_value`); the projection of a constructor whose
  arguments fit its type, at a structure that is never a proposition (`Laws.proj_ctor`); ι at a
  recursor of an inductive without indices whose major premise reduces to a constructor or a
  literal (`Laws.iota_rule`, `iotaStep`); a `Nat` primitive on literals (`Laws.nat_accel`,
  `primStep`).
* **Literals.** A `Nat` literal has type `Nat`; a `String` literal the type of its constructor form
  (`Denotes.strLit`).
* **Bounds.** A constant with more than `maxDirectParams` (8) level parameters has all its sites
  refused; levels of more than `maxLevelSize` (32) nodes are compared only syntactically (otherwise
  after `Level.simplify` and the `imax a a` collapse, or by max-plus forms: polynomial). The cost
  on a hostile closure is not otherwise bounded: every function is total, by a fuel
  (`directFuel`, a nesting depth).
-/

namespace IxCC.Grounding

open Ix.Kernel
open IxCC.Src (Value Slot Term CId Program Levels)

/-! ## Part 1. Profiles

A run term is checked once against the **set** of profiles of its constant's level parameters at
which it is evaluated (which of them are zero), as `okClosedB` checks per profile. Everything the
checker reads of an assignment is a binder datum's value (and a level's zero-ness, which is one),
and those depend only on the profile; every such decision is required at each profile of the set. -/

/-- The assignment a profile stands for on the parameters `lps`: zero where the profile says so
(at a parameter's first position), one elsewhere. -/
def φOf : List Nat → IxCC.Src.Profile → LevelParam → Nat
  | [], _, _ => 1
  | q :: qs, prof, p => if q == p then (if prof.headD false then 0 else 1) else φOf qs prof.tail p

/-- `φ` is zero on `lps` exactly where the profile says. -/
def ProfAt (φ : LevelParam → Nat) (lps : List Nat) (prof : IxCC.Src.Profile) : Prop :=
  ∀ i p, lps[i]? = some p → (φ p = 0 ↔ prof.getD i false = true)

/-- A binder datum's value at the profile, when its parameters are among `lps`. -/
def pwAt (lps : List Nat) (prof : IxCC.Src.Profile) (pw : PropWhen) : Option Bool :=
  if pw.paramsDefined lps then some (pw.holds (φOf lps prof)) else none

/-! ## Part 2. The direct route, decided (Denotes-free)

`dInfer` reads a type off stored types (`mem`) and context types; an application's type comes
from one walk along its spine (`walkArgs` with `dStep`: the function's type reduced to a `∀`, the
argument checked against the domain, the codomain instantiated), so a spine's width costs no
fuel. `convD` compares two types up to what the denotation does not read (`eqUpTo`), β (each
argument checked against its λ's domain), δ at a head (`defn_value`), the projection of a
constructor whose arguments fit its type (`proj_ctor`) and a literal against its constructor
form. Every function takes a fuel (a recursion depth) and is total. -/

/-- **The kernel's reading by key**: a hash map from each key to its constant, built once per
closure. `Env.find?` walks the reading's list of constants, so with it every lookup costs the
reading's length (1,054 constants on `tags125`): half of the check's time, interpreted, before
this table. The first constant of a key wins, as `Env.find?` reads it (`KTab.get_of`). -/
abbrev KTab := Std.HashMap KKey (ConstantInfo .anon)

/-- The table of a reading. -/
def KTab.of (env : KEnv) : KTab := env.consts.foldr (fun ci m => m.insert ci.name ci) {}

/-- What the checker reads besides the term: the kernel's reading (by key, `KTab.of` of it), the
level parameters of the run term's constant, and the profiles at which the term is evaluated. -/
structure DCtx where
  tab : KTab
  lps : List Nat
  profs : List IxCC.Src.Profile

/-- A constant of the reading. -/
def DCtx.find? (x : DCtx) (k : KKey) : Option (ConstantInfo .anon) := x.tab[k]?

/-- A projection-table entry (`Env.findProj?` through the table). -/
def DCtx.findProj? (x : DCtx) (T : KKey) (i : Nat) : Option (ProjEntry .anon) :=
  match x.find? (projTableName T) with
  | some (.projInfo tbl) => if i < tbl.numFields then some (tbl.entry i) else none
  | _ => none

/-- `neverPropB` through the table. -/
def DCtx.neverProp (x : DCtx) (D : KKey) : Bool :=
  match x.find? D with
  | some (.indInfo cvD _) =>
    match finalSort cvD.type with
    | some s => decide (Level.zeronessOf s = PropWhen.never)
    | none => false
  | _ => false

/-- A binder datum holds at none of the profiles (the graph regime at each). -/
def DCtx.pwFalse (x : DCtx) (pw : PropWhen) : Bool :=
  x.profs.all fun prof => pwAt x.lps prof pw == some false

/-- Two binder data alike at every profile. -/
def DCtx.pwEq (x : DCtx) (p q : PropWhen) : Bool :=
  p == q || x.profs.all fun prof =>
    match pwAt x.lps prof p, pwAt x.lps prof q with
    | some a, some b => a == b
    | _, _ => false

/-- The `∀` rule's side condition: the binder's datum is its codomain sort's zero condition, at
every profile. -/
def DCtx.zeroAt (x : DCtx) (pw : PropWhen) (v : Level) : Bool :=
  x.profs.all fun prof =>
    match pwAt x.lps prof pw, pwAt x.lps prof (Level.zeronessOf v) with
    | some a, some b => a == b
    | _, _ => false

/-- A level's node count. -/
def lvlSize : Level → Nat
  | .zero | .param _ => 1
  | .succ l => lvlSize l + 1
  | .max a b | .imax a b => lvlSize a + lvlSize b + 1

/-- The largest level the check simplifies. -/
def maxLevelSize : Nat := 32

/-- **A level without `imax` as a maximum of a constant and of parameters plus offsets**: its
value at `φ` is `ts.foldr (fun (p, k) m => max (φ p + k) m) c` (`none` at an `imax`). -/
def maxPlus : Level → Option (Nat × List (Nat × Nat))
  | .zero => some (0, [])
  | .param p => some (0, [(p, 0)])
  | .succ l => (maxPlus l).map fun (c, ts) => (c + 1, ts.map fun (p, k) => (p, k + 1))
  | .max a b =>
    match maxPlus a, maxPlus b with
    | some (c1, t1), some (c2, t2) => some (max c1 c2, t1 ++ t2)
    | _, _ => none
  | .imax _ _ => none

/-- One max-plus form is at most another at every assignment: its constant is at most the
other's constant or offsets, and each of its terms is dominated by a term of the same parameter. -/
def maxPlusLe : Nat × List (Nat × Nat) → Nat × List (Nat × Nat) → Bool
  | (c, ts), (d, us) =>
    decide (c ≤ us.foldr (fun pk m => max pk.2 m) d) &&
      ts.all fun (p, k) => us.any fun (q, l) => q == p && decide (k ≤ l)

/-- **`imax a a` is `a`**, bottom up: an `imax` whose two sides are syntactically equal (once
collapsed) is its side. Equal at every assignment (`Level.eval`'s `imax` is `0` at a zero right
side, else the maximum). Each node compares its two collapsed sides once, so the cost is at most
quadratic in the level's size. -/
def imaxCollapse : Level → Level
  | .succ l => .succ (imaxCollapse l)
  | .max a b => .max (imaxCollapse a) (imaxCollapse b)
  | .imax a b =>
    if imaxCollapse a == imaxCollapse b then imaxCollapse a
    else .imax (imaxCollapse a) (imaxCollapse b)
  | l => l

/-- The form `lvlEq` compares: `Level.simplify`, then `imax a a` collapsed to `a`. -/
def lvlNorm (u : Level) : Level := imaxCollapse (Level.simplify u)

/-- **Two levels evaluate alike everywhere**: syntactically equal, or, for levels of at most
`maxLevelSize` nodes, equal after `Level.simplify` and the `imax a a` collapse (`lvlNorm`; sound
by `eval_simplify` and `eval_imaxCollapse`) or after them with equal max-plus forms (each at most
the other; polynomial, unlike `Level.isEquiv`). -/
def lvlEq (u v : Level) : Bool :=
  u == v || (decide (lvlSize u ≤ maxLevelSize) && decide (lvlSize v ≤ maxLevelSize) &&
    (lvlNorm u == lvlNorm v ||
      match maxPlus (lvlNorm u), maxPlus (lvlNorm v) with
      | some a, some b => maxPlusLe a b && maxPlusLe b a
      | _, _ => false))

def lvlsEq : List Level → List Level → Bool
  | [], [] => true
  | u :: us, v :: vs => lvlEq u v && lvlsEq us vs
  | _, _ => false

/-- A `Nat` literal against a term: the literal itself, or its constructor form, layer by layer. -/
def litEqE : Nat → KExpr → Bool
  | a, .lit (.natVal b) => a == b
  | 0, e => e == .const natZeroName []
  | a + 1, .app g b => g == .const natSuccName [] && litEqE a b
  | _, _ => false

/-- **Equality up to what the denotation does not read**: levels by `lvlEq`, a binder's fields
other than its datum, the datum up to its value at the profiles, a `Nat` literal against its
constructor form. Structural, no fuel. -/
def eqUpTo (x : DCtx) : KExpr → KExpr → Bool
  | .bvar i, .bvar j => i == j
  | .sort u, .sort v => lvlEq u v
  | .const k us, .const k' vs => k == k' && lvlsEq us vs
  | .app f a, .app g b => eqUpTo x f g && eqUpTo x a b
  | .lam d b m, .lam d' b' m' => x.pwEq m.pw m'.pw && eqUpTo x d d' && eqUpTo x b b'
  | .forallE d b m, .forallE d' b' m' => x.pwEq m.pw m'.pw && eqUpTo x d d' && eqUpTo x b b'
  | .proj s i e, .proj s' i' e' => s == s' && i == i' && eqUpTo x e e'
  | .lit (.natVal a), e => litEqE a e
  | e, .lit (.natVal b) => litEqE b e
  | e, e' => e == e'

/-- A constructor application: its key, levels, parameter and field counts, arguments. -/
def ctorApp? (look : KKey → Option (ConstantInfo .anon)) (e : KExpr) :
    Option (KKey × List Level × Nat × Nat × List KExpr) :=
  match e.getAppFn with
  | .const k us =>
    match look k with
    | some (.ctorInfo _ np nf) => some (k, us, np, nf, e.getAppArgs)
    | _ => none
  | _ => none

/-- `step` along the arguments, from `T`: the type reached, or `none` at the first refusal. -/
def walkArgs (step : KExpr → KExpr → Option KExpr) : KExpr → List KExpr → Option KExpr
  | T, [] => some T
  | T, a :: as =>
    match step T a with
    | some T' => walkArgs step T' as
    | none => none

/-- **β through a λ-telescope**, each argument checked against its λ's domain by `c`: the number
of β-steps taken (until the head is not a λ, the arguments run out or `c` refuses) and the
reduct. Head reduction takes the whole telescope at one fuel, so a recursor's rule (a λ over its
parameters, motives, minor premises and fields: 127 binders at a 125-constructor enumeration)
reduces at the fuel a two-constructor one does. -/
def betaStar (c : KExpr → KExpr → Bool) : KExpr → List KExpr → Nat × KExpr
  | .lam D b m, a :: rest =>
    if c a D then
      let r := betaStar c (b.instantiate1Lift a 0) rest
      (r.1 + 1, r.2)
    else (0, Expr.mkAppN (.lam D b m) (a :: rest))
  | h, args => (0, Expr.mkAppN h args)

/-- `as` fit the `∀`-telescope `T`, each argument checked against its domain by `c`, the earlier
ones substituted; the telescope has a `∀` for every argument before substitution. -/
def fitsWith (c : KExpr → KExpr → Bool) : KExpr → List KExpr → Bool
  | _, [] => true
  | .forallE A B _, a :: as =>
    decide (as.length ≤ kPis B) && c a A && fitsWith c (B.instantiate1Lift a 0) as
  | _, _ :: _ => false

/-- How many arguments `step` takes, from `T`, before its first refusal. -/
def walkCount (step : KExpr → KExpr → Option KExpr) : KExpr → List KExpr → Nat
  | _, [] => 0
  | T, a :: as =>
    match step T a with
    | some T' => walkCount step T' as + 1
    | none => 0

/-- A type as a `∀`: itself when it is one, else what `w` (head reduction) makes of it. -/
def headPi (w : KExpr → Option KExpr) (T : KExpr) : Option KExpr :=
  match T with
  | .forallE .. => some T
  | _ => w T

/-- **One application along a spine**, given head reduction `w` and checking `c` at one fuel: the
function's type `T`, reduced at its head to a `∀` when it is not one; the argument checks against
the domain, and with `site` the binder's datum holds at none of the profiles (`pf`, the graph
regime). The codomain at the argument. -/
def stepWith (pf : PropWhen → Bool) (w : KExpr → Option KExpr) (c : KExpr → KExpr → Bool)
    (site : Bool) (T a : KExpr) : Option KExpr :=
  match headPi w T with
  | some (.forallE A B m) => if (!site || pf m.pw) && c a A then some (B.instantiate1Lift a 0) else none
  | _ => none

/-- The `Nat` primitive whose role key `k` is, if any. -/
def primOfKey? (k : KKey) : Option IxCC.Src.PrimOp :=
  IxCC.Src.PrimOp.all.find? fun op => primKey op == k

/-- A literal major premise in its constructor form (`Nat.zero`, `Nat.succ (lit n)`), what
`Denotes` reads it as; any other term as it is. -/
def majorForm : KExpr → KExpr
  | .lit (.natVal v) => natLitToConstructor v
  | e => e

/-- **A `Nat` primitive on literals** (`Laws.nat_accel`): the role key of one of SrcEval's
fifteen operations, at no levels, applied to as many arguments as it takes, each of which `w`
(head reduction) makes a literal: the literal or `Bool` constructor of `PrimOp.eval2`'s value,
applied to the remaining arguments. `none` when the step does not apply. -/
def primStep (w : KExpr → Option KExpr) (k : KKey) (us : List Level) (args : List KExpr) :
    Option KExpr :=
  match primOfKey? k, us, args with
  | some op, [], a :: rest =>
    if op.arity == 1 then
      match w a with
      | some (.lit (.natVal va)) => some (Expr.mkAppN (primResultE (op.eval2 va 0)) rest)
      | _ => none
    else
      match rest with
      | b :: rest' =>
        match w a, w b with
        | some (.lit (.natVal va)), some (.lit (.natVal vb)) =>
          some (Expr.mkAppN (primResultE (op.eval2 va vb)) rest')
        | _, _ => none
      | [] => none
  | _, _, _ => none

/-- **ι at a recursor of an inductive without indices** (`Laws.iota_rule`): the recursor `k` at
levels `us` (as many as it has parameters), its major premise (argument `mI`, its rule prefix
`rP = mI`: no indices) made by `w` (head reduction) a constructor application or a literal (read
as its constructor form); the recursor's type, at `us`, has after `mI` binders a `∀` whose domain
is an inductive at the constructor's levels applied to the recursor's own parameters (the first
`np` binders); the arguments up to the major fit that type and the constructor's arguments its
own (`fits`); the major's parameters are the recursor's (`conv`); the constructor's codomain has
no index. The reduct: the matching rule's right-hand side at `us`, applied to the arguments before
the major, the constructor's fields and the arguments after the major. `none` when the step does
not apply. -/
def iotaStep (look : KKey → Option (ConstantInfo .anon)) (w : KExpr → Option KExpr)
    (fits : KExpr → List KExpr → Bool)
    (conv : List KExpr → List KExpr → Bool) (k : KKey) (us : List Level) (args : List KExpr) :
    Option KExpr :=
  match look k with
  | some (.recInfo cv mI rP rules) =>
    match args[mI]? with
    | some maj =>
      match w maj with
      | some maj' =>
        match ctorApp? look (majorForm maj'),
            piBody mI (cv.type.instantiateLevelParams cv.levelParams us) with
        | some (ck, cus, np, nf, cargs), .forallE dom _ _ =>
          match rules.find? (fun rl => rl.ctor == ck), look ck, dom.getAppFn with
          | some rl, some (.ctorInfo cvC _ _), .const _ ls =>
            if mI == rP && us.length == cv.levelParams.length && ls == cus &&
                dom.getAppArgs == bvarsFrom (mI - np) np && decide (np ≤ mI) &&
                cargs.length == np + nf &&
                decide ((piBody (np + nf)
                  (cvC.type.instantiateLevelParams cvC.levelParams cus)).getAppArgs.length ≤ np) &&
                fits (cv.type.instantiateLevelParams cv.levelParams us) (args.take (mI + 1)) &&
                fits (cvC.type.instantiateLevelParams cvC.levelParams cus) cargs &&
                conv (args.take np) (cargs.take np) then
              some (Expr.mkAppN (rl.rhs.instantiateLevelParams cv.levelParams us)
                (args.take rP ++ cargs.drop np ++ args.drop (mI + 1)))
            else none
          | _, _, _ => none
        | _, _ => none
      | none => none
    | none => none
  | _ => none

mutual

/-- **A type of `e` in the context `Γ`** (innermost first): a variable's context type, a stored
constant's type at its levels, a β-redex's reduct's (the argument checked against the domain), an
application's by one walk along its spine (`dStep`, at this fuel less one: a nested argument costs
two levels, this one and its check's), a `Nat` literal's `Nat`, a `String` literal's its
constructor form's (`Denotes.strLit`), a sort's successor sort, a `∀`'s `imax` sort when its datum
is its codomain sort's zero condition at the profiles, a λ whose datum holds at none of the
profiles its own `∀` over its body's type. -/
def dInfer (x : DCtx) : Nat → List KExpr → KExpr → Option KExpr
  | 0, _, _ => none
  | _ + 1, Γ, .bvar i => (Γ[i]?).map (·.liftLooseBVars (i + 1) 0)
  | _ + 1, _, .const k us =>
    match x.find? k with
    | some ci =>
      if us.length == ci.toConstantVal.levelParams.length &&
          ci.toConstantVal.type.allLevelParamsDefined ci.toConstantVal.levelParams then
        some (ci.toConstantVal.type.instantiateLevelParams ci.toConstantVal.levelParams us)
      else none
    | none => none
  | n + 1, Γ, .app f a =>
    match (Expr.app f a).getAppFn, (Expr.app f a).getAppArgs with
    | .lam D b _, a1 :: rest =>
      if dCheck x n Γ a1 D then dInfer x n Γ (Expr.mkAppN (b.instantiate1Lift a1 0) rest) else none
    | h, args =>
      match dInfer x n Γ h with
      | some T =>
        walkArgs (stepWith x.pwFalse (fun T => whnfD x n true Γ T) (fun a A => dCheck x n Γ a A)
          false) T args
      | none => none
  | _ + 1, _, .lit (.natVal _) => some (.const natName [])
  | n + 1, Γ, .lit (.strVal s) => dInfer x n Γ (strLitToConstructor s)
  | _ + 1, _, .sort u => some (.sort (.succ u))
  | n + 1, Γ, .forallE A B m =>
    match dSort x n Γ A, dSort x n (A :: Γ) B with
    | some u, some v => if x.zeroAt m.pw v then some (.sort (.imax u v)) else none
    | _, _ => none
  | n + 1, Γ, .lam D b m =>
    -- a λ whose datum holds at none of the profiles has its own `∀` as a type (`lamR_mem`)
    if x.pwFalse m.pw then (dInfer x n (D :: Γ) b).map fun T => .forallE D T m else none
  | _ + 1, _, _ => none

/-- `T`'s sort: its type, reduced at its head when it is not a sort. -/
def dSort (x : DCtx) : Nat → List KExpr → KExpr → Option Level
  | 0, _, _ => none
  | n + 1, Γ, T =>
    match dInfer x n Γ T with
    | some (.sort u) => some u
    | some S =>
      match whnfD x n true Γ S with
      | some (.sort u) => some u
      | _ => none
    | none => none

/-- **`a` checks against `A`** in `Γ`: a λ against a `∀` (the type reduced at its head if
needed; domains convertible, data alike at the profiles, the body against the codomain), anything
else by its inferred type, convertible to `A`. -/
def dCheck (x : DCtx) : Nat → List KExpr → KExpr → KExpr → Bool
  | 0, _, _, _ => false
  | n + 1, Γ, .lam A1 b m1, A =>
    match headPi (fun A => whnfD x n true Γ A) A with
    | some (.forallE A2 B2 m2) =>
      convD x n Γ A1 A2 && x.pwEq m1.pw m2.pw && dCheck x n (A1 :: Γ) b B2
    | _ => false
  | n + 1, Γ, a, A =>
    match dInfer x n Γ a with
    | some T => convD x n Γ T A
    | none => false

/-- `as` fit the `∀`-telescope `T` in `Γ`, read syntactically: each checked against its domain,
the earlier ones substituted (what the projection of a constructor and ι consume, as `Fits`); the
telescope has a `∀` for every argument before substitution (`Fits` reads it syntactically). Every
argument is checked at the same fuel (`fitsWith`): a telescope's width costs none, so ι at a
recursor with 125 minor premises fits its arguments at the fuel one with two does. -/
def dFits (x : DCtx) : Nat → List KExpr → KExpr → List KExpr → Bool
  | 0, _, _, _ => false
  | n + 1, Γ, T, as => fitsWith (fun a A => dCheck x n Γ a A) T as

/-- **Head reduction**: β through a λ-telescope at one fuel (`betaStar`, each argument checked
against its λ's domain), a `Nat` primitive on arguments that reduce to literals
(`Laws.nat_accel`), ι at a recursor of an inductive without indices whose major premise reduces
to a constructor or a literal (`Laws.iota_rule`; the recursor's arguments up to the major fit its
type, the constructor's arguments fit its own, the major's parameters are the recursor's), the
projection of a constructor whose arguments fit its type, at the projection table's constructor,
and with `delta`, δ (a definition at its levels). Returns the term itself when stuck; `none` only
when the fuel runs out. -/
def whnfD (x : DCtx) : Nat → Bool → List KExpr → KExpr → Option KExpr
  | 0, _, _, _ => none
  | n + 1, delta, Γ, e =>
    match e.getAppFn, e.getAppArgs with
    | .lam D b m, a1 :: rest =>
      match betaStar (fun a A => dCheck x n Γ a A) (.lam D b m) (a1 :: rest) with
      | (0, _) => some e
      | (_ + 1, e') => whnfD x n delta Γ e'
    | .const k us, args =>
      match primStep (fun a => whnfD x n true Γ a) k us args with
      | some e' => whnfD x n delta Γ e'
      | none =>
      match iotaStep x.find? (fun a => whnfD x n true Γ a) (fun T as => dFits x n Γ T as)
          (fun ps qs => convArgs x n Γ ps qs) k us args with
      | some e' => whnfD x n delta Γ e'
      | none =>
      match x.find? k with
      | some (.defnInfo cv val _) =>
        if delta && us.length == cv.levelParams.length &&
            val.allLevelParamsDefined cv.levelParams then
          whnfD x n delta Γ (Expr.mkAppN (val.instantiateLevelParams cv.levelParams us) args)
        else some e
      | _ => some e
    | .proj s i p, args =>
      match whnfD x n delta Γ p with
      | some p' =>
        match ctorApp? x.find? p', x.findProj? s i with
        | some (ck, cus, np, nf, cargs), some entry =>
          match x.find? ck, cargs[np + i]? with
          | some (.ctorInfo cvC _ _), some fi =>
            if entry.ctor == ck && x.neverProp s && i < nf && cargs.length == np + nf &&
                cus.length == cvC.levelParams.length &&
                cvC.type.allLevelParamsDefined cvC.levelParams &&
                dFits x n Γ (cvC.type.instantiateLevelParams cvC.levelParams cus) cargs then
              whnfD x n delta Γ (Expr.mkAppN fi args)
            else some e
          | _, _ => some e
        | _, _ => some e
      | none => none
    | _, _ => some e

/-- **Conversion**: syntactically equal, or equal up to what the denotation does not read, or so
after head reduction without δ, or structurally (binders, a literal against a constructor form,
equal heads with their arguments pairwise convertible), or after head reduction with δ. -/
def convD (x : DCtx) : Nat → List KExpr → KExpr → KExpr → Bool
  | 0, _, _, _ => false
  | n + 1, Γ, T, A =>
    T == A || eqUpTo x T A ||
    match whnfD x n false Γ T, whnfD x n false Γ A with
    | some T', some A' =>
      eqUpTo x T' A' || convStruct x n Γ T' A' ||
      match whnfD x n true Γ T', whnfD x n true Γ A' with
      | some T'', some A'' => (T'' != T' || A'' != A') && convD x n Γ T'' A''
      | _, _ => false
    | _, _ => false

def convStruct (x : DCtx) : Nat → List KExpr → KExpr → KExpr → Bool
  | 0, _, _, _ => false
  | n + 1, Γ, .forallE d b m, .forallE d' b' m' =>
    x.pwEq m.pw m'.pw && convD x n Γ d d' && convD x n (d :: Γ) b b'
  | n + 1, Γ, .lam d b m, .lam d' b' m' =>
    x.pwEq m.pw m'.pw && convD x n Γ d d' && convD x n (d :: Γ) b b'
  | n + 1, Γ, .lit (.natVal k), e => (ctorApp? x.find? e).isSome && convD x n Γ (natLitToConstructor k) e
  | n + 1, Γ, e, .lit (.natVal k) => (ctorApp? x.find? e).isSome && convD x n Γ e (natLitToConstructor k)
  | n + 1, Γ, T, A =>
    !T.getAppArgs.isEmpty && T.getAppArgs.length == A.getAppArgs.length &&
      eqUpTo x T.getAppFn A.getAppFn && convArgs x n Γ T.getAppArgs A.getAppArgs

def convArgs (x : DCtx) : Nat → List KExpr → List KExpr → List KExpr → Bool
  | 0, _, _, _ => false
  | _ + 1, _, [], [] => true
  | n + 1, Γ, p :: ps, q :: qs => convD x n Γ p q && convArgs x n Γ ps qs
  | _ + 1, _, _, _ => false

end

/-- **One application along a spine** at fuel `n` (`stepWith` with head reduction and checking at
`n`): the function's type `T`, reduced at its head (with δ) to a `∀` when it is not one; the
argument checks against the domain, and with `site` the binder's datum holds at none of the
profiles (the graph regime). The codomain at the argument. `dInfer` at `n + 1` walks an
application's spine with `dStep` at `n`. -/
def dStep (x : DCtx) (n : Nat) (site : Bool) (Γ : List KExpr) (T a : KExpr) : Option KExpr :=
  stepWith x.pwFalse (fun T => whnfD x n true Γ T) (fun a A => dCheck x n Γ a A) site T a

/-- The fuel the check gives every spine (a recursion depth; a spine's width costs none). -/
def directFuel : Nat := 64

/-- An application site: its context, function and argument. -/
abbrev Site := List KExpr × KExpr × KExpr

/-- The sites of the spine `mkAppN h args`, one per prefix, in order. -/
def spineSites (Γ : List KExpr) : KExpr → List KExpr → List Site
  | _, [] => []
  | h, a :: as => (Γ, h, a) :: spineSites Γ (.app h a) as

/-- **The direct route along one spine** `mkAppN h args` in `Γ`: how many of its sites, in order,
it accepts. At a λ head the first site by the λ's own domain and datum, the next ones from the
type of the β-reduct; otherwise from `h`'s type, one `dStep` per argument with the datum
required to hold at none of the profiles. -/
def spineAccepted (x : DCtx) (n : Nat) (Γ : List KExpr) (h : KExpr) : List KExpr → Nat
  | [] => 0
  | a1 :: rest =>
    match h with
    | .lam D b m =>
      if x.pwFalse m.pw && dCheck x n Γ a1 D then
        match rest with
        | [] => 1
        | _ :: _ =>
          match dInfer x n Γ (b.instantiate1Lift a1 0) with
          | some T => walkCount (fun T a => dStep x n true Γ T a) T rest + 1
          | none => 1
      else 0
    | _ =>
      match dInfer x n Γ h with
      | some T => walkCount (fun T a => dStep x n true Γ T a) T (a1 :: rest)
      | none => 0

/-- The sites of a spine the direct route refuses: from the first refused one on. -/
def spineRefused (x : DCtx) (n : Nat) (Γ : List KExpr) (h : KExpr) (args : List KExpr) :
    List Site :=
  (spineSites Γ h args).drop (spineAccepted x n Γ h args)

/-- **The sites of a run term the direct route refuses**, at the profiles `P` at which it is
evaluated (`acc`: the arguments of the enclosing applications, innermost first). Mirrors
`evalSites`: each maximal evaluated spine is walked once, at its head; each argument is entered
with the profiles at which it is relevant (none: not entered). -/
def termRefused (tab : KTab) (lps : List Nat) (n : Nat) :
    List IxCC.Src.Profile → List KExpr → Term → KExpr → List KExpr → List Site
  | P, Γ, .app f a _ r, .app f' a', acc =>
    let P' := P.filter fun prof => !r.irrP prof
    (if P'.isEmpty then [] else termRefused tab lps n P' Γ a a' []) ++
      termRefused tab lps n P Γ f f' (a' :: acc)
  | P, Γ, .lam _ _ body, .lam d' body' m, acc =>
    spineRefused { tab, lps, profs := P } n Γ (.lam d' body' m) acc ++
      termRefused tab lps n P (d' :: Γ) body body' []
  | P, Γ, .proj _ _ t, .proj s i e, acc =>
    spineRefused { tab, lps, profs := P } n Γ (.proj s i e) acc ++
      termRefused tab lps n P Γ t e []
  | P, Γ, _, e, acc => spineRefused { tab, lps, profs := P } n Γ e acc

/-- Every application site of a run term, at any level (relevant or not). -/
def allSites : List KExpr → Term → KExpr → List Site
  | Γ, .app f a _ _, .app f' a' => (Γ, f', a') :: (allSites Γ f f' ++ allSites Γ a a')
  | Γ, .lam _ _ body, .lam d' body' _ => allSites (d' :: Γ) body body'
  | Γ, .proj _ _ e, .proj _ _ e' => allSites Γ e e'
  | _, _, _ => []

/-- The run pairs of `c`, computed: its value against its stored value, or its `eqn` body
against the equation body read off the stored theorem (`RunPair`). -/
def runPairsB (p : Program) (env : KEnv) (κ : CId → KKey) (c : CId) : List (Term × KExpr) :=
  match p.table.resolveOf c with
  | none =>
    match p.decl? c, env.find? (κ c) with
    | some (.defn .defn .safe _ _ v), some (.defnInfo _ val _) => [(v, val)]
    | _, _ => []
  | some (.eqn thm body) =>
    match eqnData? env (κ c) (κ thm) with
    | some d => [(body, d.body)]
    | none => []
  | _ => []

/-- The most level parameters a constant may have for the check to decide its sites (it checks
against subsets of them); above, every site is refused. -/
def maxDirectParams : Nat := 8

/-- The profiles at which `Ok` admits `c`. -/
def okProfiles (p : Program) (ann : IxCC.Src.Relevance.Ann) (c : CId) : List IxCC.Src.Profile :=
  match constClass ann c with
  | some r => (profiles (lvlsOf p c)).filter fun prof => !r.irrP prof
  | none => []

/-- `runRefused` with the reading's table given (`sitesDirectB` builds it once per closure). -/
def runRefusedT (tab : KTab) (p : Program) (lpsOf : CId → List Nat) (ann : IxCC.Src.Relevance.Ann)
    (c : CId) (t : Term) (e : KExpr) : List Site :=
  if lvlsOf p c ≤ maxDirectParams then
    match okProfiles p ann c with
    | [] => []
    | P => termRefused tab (lpsOf c) directFuel P [] t e []
  else allSites [] t e

/-- **The sites of `c`'s run pair the direct route refuses**: walked at `c`'s `Ok` profiles; all
of them when `c` has more than `maxDirectParams` level parameters. -/
def runRefused (p : Program) (env : KEnv) (lpsOf : CId → List Nat) (ann : IxCC.Src.Relevance.Ann)
    (c : CId) (t : Term) (e : KExpr) : List Site :=
  runRefusedT (KTab.of env) p lpsOf ann c t e

/-- **`sitesDirect`**, the Boolean beside `groundCheck`: the direct route refuses no site of any
run pair of any constant of `Sl` (the reading's table built once). -/
def sitesDirectB (p : Program) (env : KEnv) (κ : CId → KKey) (lpsOf : CId → List Nat)
    (ann : IxCC.Src.Relevance.Ann) (Sl : List CId) : Bool :=
  let tab := KTab.of env
  Sl.all fun c => (runPairsB p env κ c).all fun (t, e) =>
    (runRefusedT tab p lpsOf ann c t e).isEmpty

end IxCC.Grounding
