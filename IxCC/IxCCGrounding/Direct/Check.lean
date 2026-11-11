import IxCCGrounding.Check

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
  first refusal. A spine's width costs no fuel.
* **Conversion** (`convD`): syntactic equality; equality up to what the denotation does not read
  (`eqUpTo`: levels by `lvlEq`, binder data at the profiles, a literal against its constructor
  form); β with the argument checked; δ (`Laws.defn_value`); the projection of a constructor whose
  arguments fit its type, at a structure that is never a proposition (`Laws.proj_ctor`).
* **Bounds.** A constant with more than `maxDirectParams` (8) level parameters has all its sites
  refused; levels of more than `maxLevelSize` (32) nodes are compared only syntactically. The cost
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

/-- What the checker reads besides the term: the kernel's reading, the level parameters of the
run term's constant, and the profiles at which the term is evaluated. -/
structure DCtx where
  env : KEnv
  lps : List Nat
  profs : List IxCC.Src.Profile

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

/-- **Two levels evaluate alike everywhere**: syntactically equal, or, for levels of at most
`maxLevelSize` nodes, equal after `Level.simplify` (sound by `eval_simplify`) or after it with
equal max-plus forms (each at most the other; polynomial, unlike `Level.isEquiv`). -/
def lvlEq (u v : Level) : Bool :=
  u == v || (decide (lvlSize u ≤ maxLevelSize) && decide (lvlSize v ≤ maxLevelSize) &&
    (Level.simplify u == Level.simplify v ||
      match maxPlus (Level.simplify u), maxPlus (Level.simplify v) with
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
def ctorApp? (env : KEnv) (e : KExpr) : Option (KKey × List Level × Nat × Nat × List KExpr) :=
  match e.getAppFn with
  | .const k us =>
    match env.find? k with
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

mutual

/-- **A type of `e` in the context `Γ`** (innermost first): a variable's context type, a stored
constant's type at its levels, a β-redex's reduct's (the argument checked against the domain), an
application's by one walk along its spine (`dStep`), a literal's `Nat`, a sort's successor sort, a
`∀`'s `imax` sort when its datum is its codomain sort's zero condition at the profiles, a λ whose
datum holds at none of the profiles its own `∀` over its body's type. -/
def dInfer (x : DCtx) : Nat → List KExpr → KExpr → Option KExpr
  | 0, _, _ => none
  | _ + 1, Γ, .bvar i => (Γ[i]?).map (·.liftLooseBVars (i + 1) 0)
  | _ + 1, _, .const k us =>
    match x.env.find? k with
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
      | some T => walkArgs (fun T a => dStep x n false Γ T a) T args
      | none => none
  | _ + 1, _, .lit (.natVal _) => some (.const natName [])
  | _ + 1, _, .sort u => some (.sort (.succ u))
  | n + 1, Γ, .forallE A B m =>
    match dSort x n Γ A, dSort x n (A :: Γ) B with
    | some u, some v => if x.zeroAt m.pw v then some (.sort (.imax u v)) else none
    | _, _ => none
  | n + 1, Γ, .lam D b m =>
    -- a λ whose datum holds at none of the profiles has its own `∀` as a type (`lamR_mem`)
    if x.pwFalse m.pw then (dInfer x n (D :: Γ) b).map fun T => .forallE D T m else none
  | _ + 1, _, _ => none

/-- **One application along a spine**: the function's type `T`, reduced at its head (with δ) to
a `∀` when it is not one; the argument checks against the domain, and with `site` the binder's
datum holds at none of the profiles (the graph regime). The codomain at the argument. -/
def dStep (x : DCtx) : Nat → Bool → List KExpr → KExpr → KExpr → Option KExpr
  | 0, _, _, _, _ => none
  | n + 1, site, Γ, T, a =>
    match headPi (fun T => whnfD x n true Γ T) T with
    | some (.forallE A B m) =>
      if (!site || x.pwFalse m.pw) && dCheck x n Γ a A then some (B.instantiate1Lift a 0) else none
    | _ => none

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
the earlier ones substituted (what the projection of a constructor consumes, as `Fits`); the
telescope has a `∀` for every argument before substitution (`Fits` reads it syntactically). -/
def dFits (x : DCtx) : Nat → List KExpr → KExpr → List KExpr → Bool
  | 0, _, _, _ => false
  | _ + 1, _, _, [] => true
  | n + 1, Γ, .forallE A B _, a :: as =>
    decide (as.length ≤ kPis B) && dCheck x n Γ a A && dFits x n Γ (B.instantiate1Lift a 0) as
  | _ + 1, _, _, _ :: _ => false

/-- **Head reduction**: β (the argument checked against the λ's domain), the projection of a
constructor whose arguments fit its type, at the projection table's constructor, and with
`delta`, δ (a definition at its levels). Returns the term itself when stuck; `none` only when the
fuel runs out. -/
def whnfD (x : DCtx) : Nat → Bool → List KExpr → KExpr → Option KExpr
  | 0, _, _, _ => none
  | n + 1, delta, Γ, e =>
    match e.getAppFn, e.getAppArgs with
    | .lam D b _, a1 :: rest =>
      if dCheck x n Γ a1 D then whnfD x n delta Γ (Expr.mkAppN (b.instantiate1Lift a1 0) rest)
      else some e
    | .const k us, args =>
      match x.env.find? k with
      | some (.defnInfo cv val _) =>
        if delta && us.length == cv.levelParams.length &&
            val.allLevelParamsDefined cv.levelParams then
          whnfD x n delta Γ (Expr.mkAppN (val.instantiateLevelParams cv.levelParams us) args)
        else some e
      | _ => some e
    | .proj s i p, args =>
      match whnfD x n delta Γ p with
      | some p' =>
        match ctorApp? x.env p', x.env.findProj? s i with
        | some (ck, cus, np, nf, cargs), some entry =>
          match x.env.find? ck, cargs[np + i]? with
          | some (.ctorInfo cvC _ _), some fi =>
            if entry.ctor == ck && neverPropB x.env s && i < nf && cargs.length == np + nf &&
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
  | n + 1, Γ, .lit (.natVal k), e => (ctorApp? x.env e).isSome && convD x n Γ (natLitToConstructor k) e
  | n + 1, Γ, e, .lit (.natVal k) => (ctorApp? x.env e).isSome && convD x n Γ e (natLitToConstructor k)
  | n + 1, Γ, T, A =>
    !T.getAppArgs.isEmpty && T.getAppArgs.length == A.getAppArgs.length &&
      eqUpTo x T.getAppFn A.getAppFn && convArgs x n Γ T.getAppArgs A.getAppArgs

def convArgs (x : DCtx) : Nat → List KExpr → List KExpr → List KExpr → Bool
  | 0, _, _, _ => false
  | _ + 1, _, [], [] => true
  | n + 1, Γ, p :: ps, q :: qs => convD x n Γ p q && convArgs x n Γ ps qs
  | _ + 1, _, _, _ => false

end

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
def termRefused (env : KEnv) (lps : List Nat) (n : Nat) :
    List IxCC.Src.Profile → List KExpr → Term → KExpr → List KExpr → List Site
  | P, Γ, .app f a _ r, .app f' a', acc =>
    let P' := P.filter fun prof => !r.irrP prof
    (if P'.isEmpty then [] else termRefused env lps n P' Γ a a' []) ++
      termRefused env lps n P Γ f f' (a' :: acc)
  | P, Γ, .lam _ _ body, .lam d' body' m, acc =>
    spineRefused { env, lps, profs := P } n Γ (.lam d' body' m) acc ++
      termRefused env lps n P (d' :: Γ) body body' []
  | P, Γ, .proj _ _ t, .proj s i e, acc =>
    spineRefused { env, lps, profs := P } n Γ (.proj s i e) acc ++
      termRefused env lps n P Γ t e []
  | P, Γ, _, e, acc => spineRefused { env, lps, profs := P } n Γ e acc

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

/-- **The sites of `c`'s run pair the direct route refuses**: walked at `c`'s `Ok` profiles; all
of them when `c` has more than `maxDirectParams` level parameters. -/
def runRefused (p : Program) (env : KEnv) (lpsOf : CId → List Nat) (ann : IxCC.Src.Relevance.Ann)
    (c : CId) (t : Term) (e : KExpr) : List Site :=
  if lvlsOf p c ≤ maxDirectParams then
    match okProfiles p ann c with
    | [] => []
    | P => termRefused env (lpsOf c) directFuel P [] t e []
  else allSites [] t e

/-- **`sitesDirect`**, the Boolean beside `groundCheck`: the direct route refuses no site of any
run pair of any constant of `Sl`. -/
def sitesDirectB (p : Program) (env : KEnv) (κ : CId → KKey) (lpsOf : CId → List Nat)
    (ann : IxCC.Src.Relevance.Ann) (Sl : List CId) : Bool :=
  Sl.all fun c => (runPairsB p env κ c).all fun (t, e) => (runRefused p env lpsOf ann c t e).isEmpty

end IxCC.Grounding
