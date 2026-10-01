module

public import ConLeche.Kernel.FEnv
public import ConLeche.Cached.ExprOpsC

@[expose] public section

/-!
# The cached checker state and its operation wrappers

The per-declaration state: the converted-constant cache, the memo
caches for the five entry points, the level-operation memos and the
persistent bulk-instantiation memo, with the linear-update discipline
(detach a component from the state record before mutating it) each of
them is written in.

Task #198 removed the last of the arena's shape from this module: the
unit `CStore` and its twenty forwarding "methods", and the `withStore`
wrapper that ran a query against it.  The environment-index guards
below (`isUnitLikeTyC`, `isCtorAppC`, `headHintC`, `unfoldableHeadC`,
`sameConstHeadsC`, `rawNatLitC?`, `etaCtorShapeC`) are what the core
calls directly.

## Memo key discipline

Pointer identity is not available as a *key*, so the memo maps are
keyed on `Expr` values with:

* `Hashable Expr` = the cached hash field (`O(1)`, no traversal);
* `BEq Expr` = pointer identity, then the cached hashes, then
  structural descent.  Bucket comparisons therefore cost `O(1)` on
  the overwhelmingly common shared-subterm case (instantiation and
  abstraction return unchanged subterms *by reference*), and a hash
  mismatch rejects the rest without descending.

A hash-cons table is deliberately **not** used: it would reintroduce
the deleted arena's central data structure.  The `Level`-keyed and
`Name`-keyed caches (`lsimpC`, `eqvC`, `constTyAt`, …) are the one
place where structural hashing survives.
-/

namespace ConLeche.Cached

open ConLeche

/-! ## The environment-index guards -/

/-- `isUnitLikeTy` through the index, on a (whnf'd) `Expr`. -/
def isUnitLikeTyC (fe : FEnv) (e : Expr) : Bool :=
  match e with
  | .const cn _ .. =>
    -- task #161 item C1: the pinned-name test (see `isUnitLikeTy`)
    cn == punitName &&
    (match fe.find? punitName with
      | some (.indInfo _ _) => true
      | _ => false) &&
    (match fe.find? punitRecName with
      | some (.recInfo _ mI rP [r]) => mI == rP && r.nfields == 0
      | _ => false)
  | _ => false

/-- `isCtorApp` through the index. -/
def isCtorAppC (fe : FEnv) (e : Expr) : Bool :=
  match Expr.getAppFn e with
  | .const cn _ .. =>
    match fe.find? cn with
    | some (.ctorInfo _ _ _) => true
    | _ => false
  | _ => false

/-- `headHint` through the index. -/
def headHintC (fe : FEnv) (e : Expr) : ReducibilityHint :=
  match Expr.getAppFn e with
  | .const nm _ .. =>
    match fe.find? nm with
    | some (.defnInfo _ _ hint) => hint
    | _ => .opaque
  | _ => .opaque

/-- `unfoldableHead` through the index (the lazy-delta decision). -/
def unfoldableHeadC (fe : FEnv) (e : Expr) : Bool :=
  match Expr.getAppFn e with
  | .const nm us .. =>
    match fe.find? nm with
    | some (.defnInfo cv _ _) => us.length == cv.levelParams.length
    | _ => false
  | _ => false

/-- The cached `sameConstHeads`. -/
def sameConstHeadsC (a b : Expr) : Bool :=
  match a, b with
  | .app f₁ _ .., .app f₂ _ .. =>
    match Expr.getAppFn f₁, Expr.getAppFn f₂ with
    | .const n₁ _ .., .const n₂ _ .. => n₁ == n₂
    | _, _ => false
  | _, _ => false

/-- `rawNatLit?` on an `Expr`. -/
def rawNatLitC? (e : Expr) : Option Nat :=
  match e with
  | .lit (.natVal n) .. => some n
  | .const c [] .. => if c == natZeroName then some 0 else none
  | _ => none

/-- Twin of `etaCtorShape` (the audit's D13 gate; `Expr = Expr`). -/
def etaCtorShapeC (fe : FEnv) (e : Expr) : Bool :=
  match Expr.getAppFn e with
  | .const c _ =>
    match fe.find? c with
    | some (.ctorInfo _ cnP cnF) => (Expr.getAppArgs e).length == cnP + cnF
    | _ => false
  | _ => false

/-! ## The state -/

/-- One cached-environment entry: a stored constant's annotated type
and (for definitions/theorems/opaques) value converted to `Expr`,
each tagged with the very `Expr` object it came from.  A use validates
the tag by pointer equality (`Expr.exprPtrBEq`, reused), so the
conversion of a stored constant is paid once per declaration instead
of once per delta step. -/
structure CConstE where
  tyE : Expr
  ty : Expr
  val : Option (Expr × Expr) := none

/-- Per-declaration state: the converted-constant cache, the memo
caches for the five entry points, the lazy caches for
level-instantiated stored constants, the level-operation memos, and
the persistent bulk-instantiation memo (task #145). -/
structure CState where
  ienv : Std.HashMap Name CConstE := {}
  constTyAt : Std.HashMap (Name × List Level) Expr := {}
  constValAt : Std.HashMap (Name × List Level) Expr := {}
  ruleRhsAt : Std.HashMap (Name × Name × List Level) Expr := {}
  whnfCoreC : Std.HashMap Expr Expr := {}
  whnfC : Std.HashMap Expr Expr := {}
  inferC : Std.HashMap Expr Expr := {}
  /-- **The io-grade inference memo** (task #170 / #172 B4): results of
  the knot's `inferIO` slot at `mode.ioGate` (both modes), kept apart
  from `inferC` per the task-#170 memo
  ruling — *"since caching has no access to semantic reasoning (yet)
  we need two memos, one with and one without the flag"* — because an
  io entry witnesses fewer checks than the full-infer claims consume.
  Its invariant is the io claims' weaker (premise-form) one
  (`CSOK.inferIOC`, `Verify/Cached/DiscC1.lean`).  Official's own
  layout: the C++ kernel keys its infer cache by `infer_only`.  At
  `ioGate = false` (no mode any more) the slot shares `inferC` and
  this map stays empty. -/
  inferIOC : Std.HashMap Expr Expr := {}
  defeqC : Std.HashMap (Expr × Expr) Bool := {}
  annotC : Std.HashMap Expr Expr := {}
  lsimpC : Std.HashMap Level Level := {}
  lnzC : Std.HashMap Level Bool := {}
  eqvC : Std.HashMap (Level × Level) Bool := {}
  instC : Std.HashMap (Expr × List Expr × Nat) Expr := {}

instance : Inhabited CState := ⟨{}⟩

/-- Entry bound for the persistent bulk-instantiation memo (the
`instCCap` of the retired interned checker, reused unchanged). -/
def instCCapC : Nat := 32000000

/-- The cached checker's monad: the per-declaration memo state over
`CheckM`. -/
abbrev CheckCM := StateT CState CheckM

/-- Peel fuel of the binder-telescope loops.  A constant beyond any
real binder chain; the fuel is *semantically transparent*: on
exhaustion the leaf phase hands the residual chain back to the knot,
which is exactly the chained specification's next step. -/
def peelFuel : Nat := 16777216

@[inline] def peelFuelM : CheckCM Nat := pure peelFuel

/-- The per-node loose-bvar bound — an `O(1)` field read. -/
@[inline] def bvarBoundM (e : Expr) : CheckCM Nat := pure e.bvarB

/-! ## Syntactic operations (the `*M` wrappers) -/

/-- `Expr.instantiate1`; the identity — the same node, by reference —
when the target has no loose bvar at or above the cursor. -/
@[inline] def inst1M (e v : Expr) (d : Nat := 0) : CheckCM Expr :=
  pure (Expr.instantiate1C e v d)

/-- Bulk instantiation with the persistent result memo (task #145),
keyed by the whole argument tuple. -/
def instListM (e : Expr) (vs : List Expr) (d : Nat := 0) : CheckCM Expr :=
  modifyGet fun s =>
    if e.bvarB ≤ d then (e, s)
    else
      match s.instC[(e, vs, d)]? with
      | some r => (r, s)
      | none =>
        let mp := s.instC
        let s := { s with instC := {} }
        let mp := if mp.size < instCCapC then mp else {}
        let r := Expr.instantiateListC e vs d
        (r, { s with instC := mp.insert (e, vs, d) r })

/-- Bulk instantiation on a reversed accumulator array (deliberately
not memoized). -/
@[inline] def instListRevM (e : Expr) (vs : Array Expr) (d : Nat := 0) :
    CheckCM Expr :=
  pure (Expr.instantiateRev e vs d)

@[inline] def abstract1M (e : Expr) (d : Nat) : CheckCM Expr :=
  pure (Expr.abstract1C e d)

@[inline] def abstractRangeM (e : Expr) (d k : Nat) : CheckCM Expr :=
  pure (Expr.abstractRangeC e d k)

@[inline] def mkAppNM (f : Expr) (args : List Expr) : CheckCM Expr :=
  pure (Expr.mkAppN f args)

@[inline] def instSpineM (args : List Expr) (t : Nat) (e : Expr) :
    CheckCM Expr :=
  pure (Expr.instSpineC args t e)

@[inline] def piResidualM (e : Expr) (args : List Expr) :
    CheckCM (Option Expr) :=
  pure (Expr.piResidual e args)

@[inline] def instLevelParamsM (ks : List Name) (us : List Level)
    (e : Expr) : CheckCM Expr :=
  pure (Expr.instLevelParams ks us e)

/-! ## Level operations

Levels are plain trees here (there is no level arena), so the level
memos are keyed structurally — the one place a non-`O(1)` hash is
paid.  The *results* are cached (`lsimpC`, `lnzC`, `eqvC`), so a
decided comparison is never recomputed. -/

@[inline] def substLevelTreesM (ks : List Name) (us : List Level)
    (ls : List Level) : CheckCM (List Level) :=
  pure (ls.map (Level.subst ks us))

/-- `Level.simplify`, persistently memoized. -/
def simplifyLM (u : Level) : CheckCM Level :=
  modifyGet fun s =>
    match s.lsimpC[u]? with
    | some r => (r, s)
    | none =>
      let mp := s.lsimpC
      let s := { s with lsimpC := {} }
      let r := Level.simplify u
      (r, { s with lsimpC := mp.insert u r })

/-- `Level.isNonZero`, persistently memoized. -/
def isNonZeroLM (u : Level) : CheckCM Bool :=
  modifyGet fun s =>
    match s.lnzC[u]? with
    | some r => (r, s)
    | none =>
      let mp := s.lnzC
      let s := { s with lnzC := {} }
      let r := Level.isNonZero u
      (r, { s with lnzC := mp.insert u r })

/-- Level equivalence with a persistent result cache: simplify both
sides, compare, then the `leqCore` cascade both ways.

The `l == r` head test is official's `is_equivalent` disjunct
(`level.cpp:518`, task #176 P2) and is what makes the *shared* case —
the overwhelming majority: the parser hands one object per stream
level index — cost one pointer compare instead of a
`(Level × Level)`-keyed memo probe.  It writes no cache entry, so the
`CSOK.eqv` invariant is untouched. -/
def isEquivLM (l r : Level) : CheckCM (Option Bool) :=
  if l == r then pure (some true) else
  modifyGet fun s =>
    match s.eqvC[(l, r)]? with
    | some b => (some b, s)
    | none =>
      let mp := s.lsimpC
      let ec := s.eqvC
      let s := { s with lsimpC := {}, eqvC := {} }
      let (ls, mp) :=
        match mp[l]? with
        | some x => (x, mp)
        | none => let x := Level.simplify l; (x, mp.insert l x)
      let (rs, mp) :=
        match mp[r]? with
        | some x => (x, mp)
        | none => let x := Level.simplify r; (x, mp.insert r x)
      if ls == rs then
        (some true, { s with lsimpC := mp, eqvC := ec.insert (l, r) true })
      else
        match Level.leqCore Level.defaultFuel ls rs 0 with
        | some false =>
          (some false, { s with lsimpC := mp, eqvC := ec.insert (l, r) false })
        | some true =>
          match Level.leqCore Level.defaultFuel rs ls 0 with
          | some b =>
            (some b, { s with lsimpC := mp, eqvC := ec.insert (l, r) b })
          | none => (none, { s with lsimpC := mp, eqvC := ec })
        | none => (none, { s with lsimpC := mp, eqvC := ec })

/-- Pointwise `isEquivLM`. -/
def isEquivListLM : List Level → List Level → CheckCM (Option Bool)
  | [], [] => pure (some true)
  | l :: ls, r :: rs => do
    match ← isEquivLM l r with
    | none => pure none
    | some false => pure (some false)
    | some true => isEquivListLM ls rs
  | _, _ => pure (some false)

/-! ## Lazy stored-constant conversions -/

/-- The `Expr` of a stored constant's type: the cached entry when its
`Expr` tag validates by pointer equality, else a fresh conversion. -/
def storedTyIdxM (n : Name) (ty : Expr) : CheckCM Expr := do
  let ent? : Option CConstE ← modifyGet fun s => (s.ienv[n]?, s)
  match ent? with
  | some ent =>
    if Expr.exprPtrBEq ent.tyE ty then pure ent.ty
    else pure ty
  | none => pure ty

/-- The `Expr` of a stored definition/theorem value (see
`storedTyIdxM`). -/
def storedValIdxM (n : Name) (v : Expr) : CheckCM Expr := do
  let ent? : Option CConstE ← modifyGet fun s => (s.ienv[n]?, s)
  match ent? with
  | some ⟨_, _, some (vE, vi)⟩ =>
    if Expr.exprPtrBEq vE v then pure vi
    else pure v
  | _ => pure v

/-- The level-instantiated *type* of the stored constant `n`. -/
def constTyAtM (fe : FEnv) (_nI : Name) (n : Name) (us : List Level) :
    CheckCM Expr := do
  let hit? ← modifyGet fun s => (s.constTyAt[(n, us)]?, s)
  match hit? with
  | some i => pure i
  | none =>
    match fe.find? n with
    | some ci =>
      let cv := ci.toConstantVal
      let raw ← storedTyIdxM n cv.type
      let i ← instLevelParamsM cv.levelParams us raw
      modify fun s =>
        let mp := s.constTyAt
        let s := { s with constTyAt := ∅ }
        { s with constTyAt := mp.insert (n, us) i }
      pure i
    | none => throw (.internal "constTyAtM: unknown constant")

/-- The level-instantiated *value* of the stored definition `n`. -/
def constValAtM (fe : FEnv) (_nI : Name) (n : Name) (us : List Level) :
    CheckCM Expr := do
  let hit? ← modifyGet fun s => (s.constValAt[(n, us)]?, s)
  match hit? with
  | some i => pure i
  | none =>
    match fe.find? n with
    | some (.defnInfo cv v _) =>
      let raw ← storedValIdxM n v
      let i ← instLevelParamsM cv.levelParams us raw
      modify fun s =>
        let mp := s.constValAt
        let s := { s with constValAt := ∅ }
        { s with constValAt := mp.insert (n, us) i }
      pure i
    | _ => throw (.internal "constValAtM: not a stored definition")

/-- The level-instantiated right-hand side of the rule for constructor
`j` of the stored recursor `c`. -/
def ruleRhsAtM (fe : FEnv) (_cI _jI : Name) (c j : Name) (us : List Level) :
    CheckCM Expr := do
  let hit? ← modifyGet fun s => (s.ruleRhsAt[(c, j, us)]?, s)
  match hit? with
  | some i => pure i
  | none =>
    match fe.find? c with
    | some (.recInfo cv _ _ rules) =>
      match rules.find? (fun r' => r'.ctor == j) with
      | some rl =>
        let i ← instLevelParamsM cv.levelParams us rl.rhs
        modify fun s =>
          let mp := s.ruleRhsAt
          let s := { s with ruleRhsAt := ∅ }
          { s with ruleRhsAt := mp.insert (c, j, us) i }
        pure i
      | none => throw (.internal "ruleRhsAtM: no rule for constructor")
    | _ => throw (.internal "ruleRhsAtM: not a stored recursor")

/-- Drop the environment-dependent caches (an environment transition).
The environment-independent components — the converted-constant cache
`ienv` (self-certified by its `Expr` tags) and the level-operation
memos — survive. -/
def CState.flushed (s : CState) : CState :=
  { s with
      constTyAt := {}, constValAt := {}, ruleRhsAt := {},
      whnfCoreC := {}, whnfC := {}, inferC := {}, inferIOC := {},
      defeqC := {}, annotC := {}, instC := {} }

def flushC : CheckCM Unit := modify (·.flushed)


/-! ## The parsed-index driver's syntactic guards

`Expr.constsResolveF` as a memoized `Expr` DAG walk (the counterpart
of `constsResolveFIGo`): the tree-walking `Expr` version is what makes
the `Expr`-typed driver quadratic — or worse — on shared declarations.

The walk is the substitution walks' design over a `Bool`
(`ConLeche/Cached/ExprOpsC.lean`, "The `Bool`-valued walks"): a plain
descent `constsResolveFP`, a child step that reads `withExclusive`
(`ConLeche/Kernel/Exclusive.lean`) on the BORROWED node, and a walk
carrying its own proof against the plain descent, memoising only what
the read reports shared, under the node's address as key.  There is no
cutoff — no cached field decides whether a constant resolves — so the
structural per-call `Std.HashMap` this replaced (task #319) recorded
EVERY node it met, leaves included; this walk decides `bvar`, `sort`,
`lit` and `const` directly, never records them, and probes only a
compound node (`fvar` included: its annotation is descended) that
`withExclusive` reports shared.  `fe` is read-only and borrowed. -/

/-- The plain descent of `constsResolveFC`: the reference the walk is
verified against (`constsResolveFP_spec`,
`ConLeche/Verify/Cached/GuardsC.lean`, is the equation to
`Expr.constsResolveF`). -/
def constsResolveFP (fe : FEnv) (e : Expr) : Bool :=
  match e with
  | .bvar .. | .sort .. => true
  | .lit (.natVal _) .. =>
    (fe.find? natName).isSome && (fe.find? natZeroName).isSome &&
      (fe.find? natSuccName).isSome
  | .lit (.strVal _) .. =>
    (fe.find? natName).isSome && (fe.find? natZeroName).isSome &&
      (fe.find? natSuccName).isSome && (fe.find? stringName).isSome &&
      (fe.find? stringOfListName).isSome &&
      (fe.find? listName).isSome && (fe.find? listNilName).isSome &&
      (fe.find? listConsName).isSome && (fe.find? charName).isSome &&
      (fe.find? charOfNatName).isSome
  | .const nm _ .. => (fe.find? nm).isSome
  | .fvar _ ty .. => constsResolveFP fe ty
  | .app f a .. => constsResolveFP fe f && constsResolveFP fe a
  | .lam ty body _ .. | .forallE ty body _ .. =>
    constsResolveFP fe ty && constsResolveFP fe body
  | .letE ty val body .. =>
    constsResolveFP fe ty && constsResolveFP fe val && constsResolveFP fe body
  | .proj sn _ sub .. => (fe.find? sn).isSome && constsResolveFP fe sub

/-- The child step of `constsResolveFXP`: the compound test, then the
exclusivity read (there is no cutoff). -/
@[inline] def enterCRF (fe : @& FEnv) (e : @& Expr)
    (memo : Expr.MemoB0 (constsResolveFP fe))
    (rec : Unit → Squash (Expr.ResB0 (constsResolveFP fe) e)) :
    Squash (Expr.ResB0 (constsResolveFP fe) e) :=
  if !Expr.isCompoundF e then rec () else
  withExcl e fun excl =>
    if excl then rec () else memo.shared e fun _ => rec ()

/-- The walk of `constsResolveFC`. -/
def constsResolveFXP (fe : @& FEnv) (memo : Expr.MemoB0 (constsResolveFP fe))
    (e : @& Expr) : Squash (Expr.ResB0 (constsResolveFP fe) e) :=
  match e with
  | .bvar .. | .sort .. => Squash.mk (⟨true, by rw [constsResolveFP]⟩, memo)
  | .lit (.natVal _) .. =>
    Squash.mk (⟨(fe.find? natName).isSome && (fe.find? natZeroName).isSome &&
      (fe.find? natSuccName).isSome, by rw [constsResolveFP]⟩, memo)
  | .lit (.strVal _) .. =>
    Squash.mk (⟨(fe.find? natName).isSome && (fe.find? natZeroName).isSome &&
      (fe.find? natSuccName).isSome && (fe.find? stringName).isSome &&
      (fe.find? stringOfListName).isSome &&
      (fe.find? listName).isSome && (fe.find? listNilName).isSome &&
      (fe.find? listConsName).isSome && (fe.find? charName).isSome &&
      (fe.find? charOfNatName).isSome, by rw [constsResolveFP]⟩, memo)
  | .const nm _ .. => Squash.mk (⟨(fe.find? nm).isSome, by rw [constsResolveFP]⟩, memo)
  | .fvar _ ty .. =>
    enterCRF fe ty memo (fun _ => constsResolveFXP fe memo ty) |>.lift fun (⟨rt, ht⟩, memo) =>
    Squash.mk (⟨rt, by rw [constsResolveFP, ← ht]⟩, memo)
  | .app f a .. =>
    enterCRF fe f memo (fun _ => constsResolveFXP fe memo f) |>.lift fun (⟨rf, hf⟩, memo) =>
    match rf, hf with
    | true, hf =>
      enterCRF fe a memo (fun _ => constsResolveFXP fe memo a) |>.lift fun (⟨ra, ha⟩, memo) =>
      Squash.mk (⟨ra, by rw [constsResolveFP, ← hf, ← ha, Bool.true_and]⟩, memo)
    | false, hf =>
      Squash.mk (⟨false, by rw [constsResolveFP, ← hf, Bool.false_and]⟩, memo)
  | .lam ty body _ .. | .forallE ty body _ .. =>
    enterCRF fe ty memo (fun _ => constsResolveFXP fe memo ty) |>.lift fun (⟨rt, ht⟩, memo) =>
    match rt, ht with
    | true, ht =>
      enterCRF fe body memo (fun _ => constsResolveFXP fe memo body) |>.lift
        fun (⟨rb, hb⟩, memo) =>
      Squash.mk (⟨rb, by rw [constsResolveFP, ← ht, ← hb, Bool.true_and]⟩, memo)
    | false, ht =>
      Squash.mk (⟨false, by rw [constsResolveFP, ← ht, Bool.false_and]⟩, memo)
  | .letE ty val body .. =>
    enterCRF fe ty memo (fun _ => constsResolveFXP fe memo ty) |>.lift fun (⟨rt, ht⟩, memo) =>
    match rt, ht with
    | true, ht =>
      enterCRF fe val memo (fun _ => constsResolveFXP fe memo val) |>.lift
        fun (⟨rv, hv⟩, memo) =>
      match rv, hv with
      | true, hv =>
        enterCRF fe body memo (fun _ => constsResolveFXP fe memo body) |>.lift
          fun (⟨rb, hb⟩, memo) =>
        Squash.mk (⟨rb, by rw [constsResolveFP, ← ht, ← hv, ← hb]; simp⟩, memo)
      | false, hv =>
        Squash.mk (⟨false, by rw [constsResolveFP, ← ht, ← hv]; simp⟩, memo)
    | false, ht =>
      Squash.mk (⟨false, by rw [constsResolveFP, ← ht]; simp⟩, memo)
  | .proj sn _ sub .. =>
    if hfind : (fe.find? sn).isSome = true then
      enterCRF fe sub memo (fun _ => constsResolveFXP fe memo sub) |>.lift
        fun (⟨rs, hs⟩, memo) =>
      Squash.mk (⟨rs, by rw [constsResolveFP, ← hs, hfind, Bool.true_and]⟩, memo)
    else
      Squash.mk (⟨false, by rw [constsResolveFP]; simp [hfind]⟩, memo)

/-- The cached `Expr.constsResolveF fe` (one memoized DAG walk). -/
def constsResolveFC (fe : FEnv) (e : Expr) : Bool :=
  Expr.resBool (constsResolveFXP fe none e)

/-- Record an accepted constant's converted type/value, tagged with the
very `Expr` objects pushed into the environment (the counterpart of
`recordIConst`). -/
def recordCConst (n : Name) (tyE : Expr) (ty : Expr)
    (val : Option (Expr × Expr)) : CheckCM Unit :=
  modify fun s =>
    let m := s.ienv
    let s := { s with ienv := {} }
    { s with ienv := m.insert n ⟨tyE, ty, val⟩ }

end ConLeche.Cached
