/-
  Ix.Compile.Image.Develop: the development of an image as hereditary
  substitution.

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

  Termination is a typed argument (each hereditary step substitutes at a
  strictly smaller type). The functions are untyped, so they carry an
  explicit bound on the recursion depth (`developFuel`, decreasing on every
  call): exhausting it is an error naming the bound, never a partial result.
  On well-typed input the depth is the term's depth plus the nesting of the
  motive and minor types, far below the bound.

  `hinst`'s table is keyed by its inputs without the remaining fuel. A
  successful result does not depend on the fuel that reached it, so a hit can
  only turn a refusal at a smaller remaining bound into the result a larger
  one gives; it never changes a returned term. A hit is confirmed by exact
  comparison of the retained inputs (`RawExact.exprDecEq`): a digest only
  selects the bucket.

  The image construction uses this to instantiate the canonical recursor's
  motives in its minor types (`substFVars`), so that the image is created
  already developed; a call-site rewrite uses `instantiate` to replace
  `img(a) args` by the image body at `args`.
-/
module
public import Ix.Environment
public import Ix.Compile.Canon.Expr
public import Ix.Compile.Image.Expr
public import Ix.Compile.Image.TotalMemo
public section

namespace Ix.Compile.Image

open Ix (Name Level Expr)
open Ix.Compile.LibraryNames
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

/-! ## Memoised de Bruijn arithmetic

The terms substituted at a call site are the user's arguments: large, and
DAG-shaped (proof terms share subterms heavily). Every traversal below is
memoised per node. The four total tables (`TotalMemo`) retain exact input
keys and certified answers; `hinst`'s table retains its exact inputs. -/

/-- One entry of `hinst`'s table: the substitution's inputs, retained so
that a hit is confirmed by exact comparison, and its result. -/
structure InstEntry where
  value : Expr
  body : Expr
  depth : Nat
  result : Expr × Created

structure DevState where
  range : TotalMemo.RangeMemo := {}
  lifted : TotalMemo.LiftMemo := {}
  lowered : TotalMemo.LowerMemo := {}
  occurs : TotalMemo.OccursMemo := {}
  /-- `hinst`'s table, one entry per bucket (a later entry replaces it). -/
  insts : Std.HashMap UInt64 InstEntry := {}

abbrev DevM := StateT DevState (Except String)

/-- The bucket of `hinst v k e`: a digest of the inputs, a selector only. -/
def instBucket (v e : Expr) (k : Nat) : UInt64 :=
  mixHash (hash v) (mixHash (hash e) (hash k))

/-- `hinst v k e`'s retained result, when its bucket holds exactly these
inputs. -/
def instProbe (st : DevState) (v e : Expr) (k : Nat) : Option (Expr × Created) :=
  match st.insts.get? (instBucket v e k) with
  | some entry =>
    if entry.depth == k && RawExact.exprEq entry.body e && RawExact.exprEq entry.value v then
      some entry.result
    else none
  | none => none

/-- One more than the largest loose bound variable of `e` (`0`: closed). -/
def looseRange (e : Expr) : DevM Nat := fun st =>
  let r := TotalMemo.rangeGo hash e st.range
  .ok (r.value, { st with range := r.state })

/-- `liftLoose e n c`, with exact confirmed memo hits. -/
def liftM (e : Expr) (n c : Nat) : DevM Expr := fun st =>
  let r := TotalMemo.liftGo hash hash e n c ⟨st.range, st.lifted⟩
  .ok (r.value, { st with range := r.state.range, lifted := r.state.values })

/-- `lowerLoose e n c`, with exact confirmed memo hits. -/
def lowerM (e : Expr) (n c : Nat) : DevM Expr := fun st =>
  let r := TotalMemo.lowerGo hash hash e n c ⟨st.range, st.lowered⟩
  .ok (r.value, { st with range := r.state.range, lowered := r.state.values })

/-- `bvar k` occurs loose in `e`, with exact confirmed memo hits. -/
def occursM (e : Expr) (k : Nat) : DevM Bool := fun st =>
  let r := TotalMemo.occursGo hash hash e k ⟨st.range, st.occurs⟩
  .ok (r.value, { st with range := r.state.range, occurs := r.state.values })

/-- The bound on the development's recursion depth. -/
def developFuel : Nat := 1 <<< 16

/-- The error of an exhausted bound. -/
def developExhausted : String :=
  s!"development: recursion depth bound developFuel = {developFuel} exhausted"

mutual
/-- `e[bvar k := v]`, contracting the redexes formed at the substituted
positions. `v`'s loose variables refer to the context outside `e`'s
binders; it is lifted under them. -/
def hinst : Nat → Expr → Nat → Expr → DevM (Expr × Created)
  | 0, _, _, _ => throw developExhausted
  | fuel + 1, v, k, e => do
    if (← looseRange e) ≤ k then return (e, .no)
    if let some r := instProbe (← get) v e k then return r
    let r ← match e with
      | .bvar i _ =>
        if i == k then do pure (← liftM v k 0, .direct)
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
        | _, .lam .. => do pure ((← happ fuel h' args'.toList), .reduced)
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
          if !(← occursM f 0) then do pure (← lowerM f 1 0, .direct)
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
    modify fun st => { st with insts := st.insts.insert (instBucket v e k) ⟨v, e, k, r⟩ }
    return r

/-- `f a₁ … aₙ` with the β-redexes at the head contracted hereditarily. -/
def happ : Nat → Expr → List Expr → DevM Expr
  | 0, _, _ => throw developExhausted
  | fuel + 1, .lam _ _ b _ _, a :: rest => do
    let (b', _) ← hinst fuel a 0 b
    happ fuel b' rest
  | _ + 1, f, args => pure (mkAppN f args.toArray)
end

/-- The developed application `f args` (at a call site: `f` is the image
body, `args` the occurrence's arguments; arguments beyond `f`'s λs stay
applied). -/
def instantiate (f : Expr) (args : Array Expr) : Except String Expr :=
  (happ developFuel f args.toList).run' {}

/-- `instantiate` with the fuel-free tables of an earlier development carried
over (`range`, `lifted`, `lowered`, `occurs`: values of total functions of
their keys, so a carried entry is the entry this call would compute) and
`hinst`'s table fresh. Same result as `instantiate`; returns the tables for
the next call. -/
def instantiateWith (st : DevState) (f : Expr) (args : Array Expr) :
    Except String (Expr × DevState) :=
  (happ developFuel f args.toList).run { st with insts := {} }

/-- `e[xs := vs]` for free variables, developed. The values are locally
closed and do not mention `xs`. -/
def substFVars (xs : Array Name) (vs : Array Expr) (e : Expr) : Except String Expr := do
  if xs.size != vs.size then throw "substFVars: arity mismatch"
  let go : DevM Expr := do
    let mut acc := abstractFVars xs e
    for v in vs.reverse do
      acc := (← hinst developFuel v 0 acc).1
    return acc
  go.run' {}

end Ix.Compile.Image

end
