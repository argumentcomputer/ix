module

import ConLeche.Kernel.Env
public import ConLeche.Kernel.PropRead
import ConLeche.Kernel.Level
import ConLeche.Kernel.ExprOps
public import ConLeche.Kernel.Basis

@[expose] public section

/-!
# The checker core's fuel-free helpers

The definitions of the core checker that mention no monad, no
`CoreFns` record and no fuel: the delta step and its readers
(`unfoldDefinition`, `unfoldableHead`, `headHint`, `sameConstHeads`),
the literal shapes and their guards (`natLitToConstructor`,
`natLitSupported`, `strLitToConstructor`, `strLitSupported`,
`rawNatLit?`), the certified `Nat` operations' names, recurrences,
reducts and pins (`natOpNames`, `natDivModNames`, `natOpEquations`,
`natOpResult`, `natOpStoredOk`, …), the structure-η fabrications
(`etaProjs`, `etaFabArgs`, `andRescueSlots`), the install-time rule
bits (`recRuleBits`, `projFnRule`, `recRuleK`, `recFireComparands`),
the tower entry's readers (`ProjEntry.fireOk`, `ProjEntry.typeAt`), the
β gate (`betaGateFires`) and the annotation datum's writer
(`annotBinderMeta`).

Split out of `ConLeche/Kernel/Core.lean` at task #305 (prep): a
relational description of the core's moves — a relation over `Expr`
and `Env` — must name these without importing the executable bodies,
and every one of them is exactly what such a relation needs.  The
bodies (`whnfCoreBody`, `whnfBody`, `inferBody`, `defeqBody`,
`annotateBody`, the knot and the fuel constants) stay in `Core.lean`,
which re-exports this module, so every importer of `Core` sees the
names unchanged.  Nothing here was rewritten: the definitions keep
their names, docstrings, attributes and relative order.
-/

namespace ConLeche

/-- The model-side name of field `i`'s projection for `T`
(the documented public interface of a `_model` family). -/
def projModelName (T : Name) (i : Nat) : Name :=
  (T.str "_model").str ("proj_" ++ toString i)

/-- Is the expression headed by a stored constructor? -/
def isCtorApp (env : Env) (e : Expr) : Bool :=
  match e.getAppFn with
  | .const c _ =>
    match env.find? c with
    | some (.ctorInfo _ _ _) => true
    | _ => false
  | _ => false

/-- Does the syntactic pi telescope end in a (normalized) `Prop`?
Used for the K capability (an inductive *proposition*) and to guard the
structure-eta rescue (the official kernel does not eta-rescue
propositional structures). -/
def piResultIsProp (e : Expr) : Bool :=
  match e.piResult with
  | .sort u => Level.isEquiv u .zero == some true
  | _ => false

/-- **The result-sort zero-ness datum of an inductive's type**
(`IndCaps.sortZ`, computed at the block's install): the reading of the
family's result sort as a predicate on its level parameters.  A type
whose telescope does not end in a sort gets `ifAllZero []` — "zero at
every valuation" — which no rescue passes. -/
def piResultZ (e : Expr) : PropWhen :=
  match e.piResult with
  | .sort u => Level.zeronessOf u
  | _ => .ifAllZero []

/-- Is the result sort of a stored inductive's type, instantiated at
the given levels, provably nonzero (official `is_never_zero`)?  The
**specification** of `capsNeverZero`: the walk down the family's type
that the stored datum replaces. -/
def piResultNeverZero (lps : List Name) (us : List Level) (e : Expr) :
    Bool :=
  match e.piResult with
  | .sort u => (Level.subst lps us u).isNeverZero
  | _ => false

/-- Is a stored inductive's result sort, at the given level
instantiation, provably nonzero (official `is_never_zero`)?  The
official kernel's structure rescue (`to_cnstr_when_structure`)
requires this of the major's type; the basis `PUnit` rescue mirrors
it (`Sort u` at a concrete level such as `Unit`'s `1` passes, the
parameter `u` itself does not).  Read off the stored datum: the
instantiated datum is unsatisfiable exactly where the instantiated
sort is never zero (`capsNeverZero_eq`,
`ConLeche/Verify/InferLemmas.lean`). -/
def capsNeverZero (lps : List Name) (us : List Level) (caps : IndCaps) :
    Bool :=
  (Level.substPW lps us caps.sortZ).isNever

/-- Is this (whnf'd) type expression a unit-like inductive type — a
stored inductive whose recursor (under the `<ind>.rec` naming
convention) has no indices and a single zero-field rule?  All of its
inhabitants are then equal (in the model: the proof point; the
environment invariant supplies the fact for the stored constant).

Task #161 de-gating round A+B+C, item C1 (harvest site 35, list entry
P8).  The test used to be a *scan*: two `Env.find?`s on the head's own
name, a `Name.str "rec"` allocation, and a 20-element
`reservedBasisNames.contains` walk — run on **every** proof-irrelevance
attempt (12 453 724 of them on init-full).  It is the same Bool as a
head-name test against the single pin that can pass it:
`unitLike_eq_punit` (`ConLeche/Verify/PinnedShapes.lean`) proves that
under `BasisPinnedTT` — the reserved-name pinning the install path
enforces — **only `PUnit` passes**, every other reserved recursor being
refuted by one of the three conditions.  So the head-name comparison is
put first and the rest is the *same* two lookups specialised to
`punitName`: `false` short-circuits after one `Name` comparison at
every non-`PUnit` head, which is essentially all of them, and the
`.str "rec"` allocation and the reserved-list walk are gone.

This is a computation downgrade, not a removal: at `c = punitName` the
two stored-shape checks still run, so an environment that has not
installed `PUnit` (or has installed it at the wrong shape) still fails
the test.  Only the *other* reserved heads are decided by the pin
rather than by a lookup — which is what `unitLike_eq_punit` licenses.
-/
def isUnitLikeTy (env : Env) : Expr → Bool
  | .const c _ =>
    c == punitName &&
    (match env.find? punitName with
      | some (.indInfo _ _) => true
      | _ => false) &&
    (match env.find? punitRecName with
      -- no indices: the major's position equals the rule prefix
      | some (.recInfo _ mI rP [r]) => mI == rP && r.nfields == 0
      | _ => false)
  | _ => false

/-- Unfold the (application of a) definition at the head, one step.
`none` when the head is not an unfoldable constant.  **Theorems are
opaque to reduction**: a stored `thmInfo` never unfolds, so whether a
declaration type-checks never depends on a theorem's value — this
anticipates https://github.com/leanprover/lean4/pull/14896 (theorems
become opaque to the kernel: `is_delta` stops unfolding them).  The
one known input whose typing needs a theorem to unfold, the arena's
`subject-reduction-redex`, is rejected (an accept-subset of the
reference kernels until that PR lands). -/
def unfoldDefinition (env : Env) (e : Expr) : Option Expr :=
  match e.getAppFn with
  | .const n us =>
    match env.find? n with
    | some (.defnInfo cv value _) =>
      if us.length = cv.levelParams.length then
        some (Expr.mkAppN (value.instantiateLevelParams cv.levelParams us)
          e.getAppArgs)
      else none
    | _ => none
  | _ => none

/-- May the delta step unfold `e`'s head — is it a constant whose
stored declaration carries a value at a matching level-parameter count
(the official kernel's `is_delta`)?  This is the *decision* the lazy
delta step takes; the unfolding itself is materialized only inside the
branch that consumes it (`unfoldDefinition`), never in both slots of a
match scrutinee.  By construction
`unfoldableHead env e = (unfoldDefinition env e).isSome`. -/
def unfoldableHead (env : Env) (e : Expr) : Bool :=
  match e.getAppFn with
  | .const n us =>
    match env.find? n with
    | some (.defnInfo cv _ _) => us.length == cv.levelParams.length
    | _ => false
  | _ => false

/-- The reducibility hint of the constant at the head of `e` (`opaque`
when the head is not a stored definition — a theorem included, which
never unfolds). -/
def headHint (env : Env) (e : Expr) : ReducibilityHint :=
  match e.getAppFn with
  | .const n _ =>
    match env.find? n with
    | some (.defnInfo _ _ hint) => hint
    | _ => .opaque
  | _ => .opaque

/-- Are `a` and `b` applications of the *same* constant (the lazy delta
same-head short-circuit: try level and spine congruence before
unfolding both sides)?  Mirrors the official kernel's
`try_eq_const_app`: both sides must actually be applications. -/
def sameConstHeads : Expr → Expr → Bool
  | .app f₁ _, .app f₂ _ =>
    match f₁.getAppFn, f₂.getAppFn with
    | .const n₁ _, .const n₂ _ => n₁ == n₂
    | _, _ => false
  | _, _ => false

/-- The constructor form of a `Nat` literal, one layer:
`n + 1` becomes `Nat.succ (lit n)`, `0` becomes `Nat.zero` (the
official kernel's `natLitToConstructor`, used on recursor majors). -/
def natLitToConstructor (n : Nat) : Expr :=
  match n with
  | 0 => .const natZeroName []
  | k + 1 => .app (.const natSuccName []) (.lit (.natVal k))

/-- The stored `Nat` declaration has the expected shape. -/
def natIndOk : Option ConstantInfo → Bool
  | some (.indInfo cv _) =>
    cv.levelParams.isEmpty && cv.type == .sort (.succ .zero)
  | _ => false

/-- The stored `Nat.zero` declaration has the expected shape. -/
def natZeroOk : Option ConstantInfo → Bool
  | some (.ctorInfo cv _ _) =>
    cv.levelParams.isEmpty && cv.type == .const natName []
  | _ => false

/-- The stored `Nat.succ` declaration has the expected (annotated)
shape. -/
def natSuccOk : Option ConstantInfo → Bool
  | some (.ctorInfo cv _ _) =>
    cv.levelParams.isEmpty &&
    (match cv.type with
     | .forallE (.const c1 []) (.const c2 []) _mb =>
       c1 == natName && c2 == natName
     | _ => false)
  | _ => false

/-- Whether the environment supports `Nat` literals: `Nat`, `Nat.zero`
and `Nat.succ` are stored with exactly the expected kinds, level
parameters and (annotated) types.  Every literal code path is guarded
on this — the model interprets a literal by iterating the `Nat.succ`
value on the `Nat.zero` value, and the soundness proofs read the
declaration shapes off this guard. -/
def natLitSupported (env : Env) : Bool :=
  natIndOk (env.find? natName) && natZeroOk (env.find? natZeroName) &&
    natSuccOk (env.find? natSuccName)

/-- Do all constants referenced in `e` (including inside `fvar` type
annotations) resolve in `env`?  A `Nat` literal implicitly references
the `Nat` basis constants (and a `String` literal additionally the
string-support constants).  Checked once per declaration; keeps the
environment well-formedness invariant syntactic. -/
def Expr.constsResolve (env : Env) : Expr → Bool
  | .bvar _ | .sort _ => true
  | .lit (.natVal _) =>
    (env.find? natName).isSome && (env.find? natZeroName).isSome &&
      (env.find? natSuccName).isSome
  | .lit (.strVal _) =>
    -- a string literal implicitly references the `Nat` trio (its
    -- character numerals) and the seven string-support constants
    (env.find? natName).isSome && (env.find? natZeroName).isSome &&
      (env.find? natSuccName).isSome && (env.find? stringName).isSome &&
      (env.find? stringOfListName).isSome && (env.find? listName).isSome &&
      (env.find? listNilName).isSome && (env.find? listConsName).isSome &&
      (env.find? charName).isSome && (env.find? charOfNatName).isSome
  | .const n _ => (env.find? n).isSome
  | .fvar _ ty => ty.constsResolve env
  | .app f a => f.constsResolve env && a.constsResolve env
  | .lam ty body _ | .forallE ty body _ =>
    ty.constsResolve env && body.constsResolve env
  | .letE ty val body =>
    ty.constsResolve env && val.constsResolve env && body.constsResolve env
  | .proj s _ e => (env.find? s).isSome && e.constsResolve env

/-- Convert a `Nat`-literal major premise to constructor form, one
layer; anything else passes through. -/
def litToCtorIfNat (env : Env) : Expr → Expr
  | .lit (.natVal n) =>
    if natLitSupported env then natLitToConstructor n else .lit (.natVal n)
  | e => e

/-- A `Nat` literal reading of a whnf'd expression: literals and the
`Nat.zero` constant (the official kernel's `rawNatLitExt?`). -/
def rawNatLit? : Expr → Option Nat
  | .lit (.natVal n) => some n
  | .const c [] => if c = natZeroName then some 0 else none
  | _ => none

/-! ## String literals

A string literal unfolds on demand to `String.ofList [c₁, …, cₙ]` with
each character built by `Char.ofNat` from a `Nat` literal — the
reference kernels' `strLitToConstructor` (lean4lean `Expr.lean`, nanoda
`expr.rs`), mirrored exactly.  The names below are *pinned* like the
`Nat` literal names: the guard `strLitSupported` checks that the stored
declarations have exactly the expected (annotated) types, which is what
the model's interpretation of a string literal reads its meaning off.
A string literal in the input while the guard fails is a positively
detected unsupported feature — annotation *declines* (exit 2). -/

/-- The constructor form of a `String` literal:
`String.ofList (List.cons.{0} Char (Char.ofNat (lit c₁)) (… (List.nil.{0}
Char)))` — the official kernel's `strLitToConstructor`, spelling as in
lean4lean (`Expr.strLitToConstructor`) and nanoda
(`str_lit_to_constructor`). -/
def strLitToConstructor (s : String) : Expr :=
  .app (.const stringOfListName []) <|
    s.toList.foldr
      (init := .app (.const listNilName [.zero]) (.const charName []))
      fun c e =>
        .app (.app (.app (.const listConsName [.zero]) (.const charName []))
          (.app (.const charOfNatName []) (.lit (.natVal c.toNat)))) e

/-- The stored `String` declaration has the expected shape
(`String : Type`, no level parameters; any constant kind). -/
def stringTyOk : Option ConstantInfo → Bool
  | some ci =>
    ci.toConstantVal.levelParams.isEmpty &&
      ci.toConstantVal.type == .sort (.succ .zero)
  | none => false

/-- The stored `Char` declaration has the expected shape (`Char : Type`,
no level parameters). -/
def charTyOk : Option ConstantInfo → Bool
  | some ci =>
    ci.toConstantVal.levelParams.isEmpty &&
      ci.toConstantVal.type == .sort (.succ .zero)
  | none => false

/-- The stored `List` declaration has the expected (annotated) shape
`List.{p} : Type p → Type p`. -/
def listTyOk : Option ConstantInfo → Bool
  | some ci =>
    match ci.toConstantVal.levelParams with
    | [p] =>
      (match ci.toConstantVal.type with
       | .forallE (.sort u1) (.sort u2) _mb =>
         u1 == .succ (.param p) && u2 == .succ (.param p)
       | _ => false)
    | _ => false
  | none => false

/-- The stored `List.nil` declaration has the expected (annotated) shape
`List.nil.{p} : ∀ (α : Type p), List.{p} α`. -/
def listNilTyOk : Option ConstantInfo → Bool
  | some ci =>
    match ci.toConstantVal.levelParams with
    | [p] =>
      (match ci.toConstantVal.type with
       | .forallE (.sort u1) (.app (.const l1 us1) (.bvar 0)) _mb =>
         u1 == .succ (.param p) && l1 == listName && us1 == [.param p]
       | _ => false)
    | _ => false
  | none => false

/-- The stored `List.cons` declaration has the expected (annotated) shape
`List.cons.{p} : ∀ (α : Type p) (head : α) (tail : List.{p} α),
List.{p} α` (with the codomain-sort annotations the annotation pass
produces on that type). -/
def listConsTyOk : Option ConstantInfo → Bool
  | some ci =>
    match ci.toConstantVal.levelParams with
    | [p] =>
      (match ci.toConstantVal.type with
       | .forallE (.sort u1)
           (.forallE (.bvar 0)
             (.forallE (.app (.const l1 us1) (.bvar 1))
               (.app (.const l2 us2) (.bvar 2)) _mb3) _mb2) _mb1 =>
         u1 == .succ (.param p) && l1 == listName && l2 == listName &&
           us1 == [.param p] && us2 == [.param p]
       | _ => false)
    | _ => false
  | none => false

/-- The stored `Char.ofNat` declaration has the expected (annotated)
shape `Char.ofNat : Nat → Char`. -/
def charOfNatTyOk : Option ConstantInfo → Bool
  | some ci =>
    ci.toConstantVal.levelParams.isEmpty &&
      (match ci.toConstantVal.type with
       | .forallE (.const c1 []) (.const c2 []) _mb =>
         c1 == natName && c2 == charName
       | _ => false)
  | none => false

/-- The stored `String.ofList` declaration has the expected (annotated)
shape `String.ofList : List.{0} Char → String`. -/
def stringOfListTyOk : Option ConstantInfo → Bool
  | some ci =>
    ci.toConstantVal.levelParams.isEmpty &&
      (match ci.toConstantVal.type with
       | .forallE (.app (.const l1 us1) (.const c1 [])) (.const c2 []) _mb =>
         l1 == listName && us1 == [.zero] && c1 == charName &&
           c2 == stringName
       | _ => false)
  | none => false

/-- Whether the environment supports `String` literals: the `Nat`
literal guard plus `String`, `String.ofList`, `List`, `List.nil`,
`List.cons`, `Char` and `Char.ofNat` stored with exactly the expected
level parameters and (annotated) types.  Every string-literal code path
is guarded on this; the model interprets a string literal through the
values of these constants, and the soundness proofs read the
declaration shapes off this guard.  (The reference kernels only check
*existence* of `Char.ofNat` and `String.ofList`; the type pins are what
makes the interpretation well-defined, in the spirit of the `Nat`
literal guard.) -/
def strLitSupported (env : Env) : Bool :=
  natLitSupported env &&
    stringTyOk (env.find? stringName) &&
    stringOfListTyOk (env.find? stringOfListName) &&
    listTyOk (env.find? listName) &&
    listNilTyOk (env.find? listNilName) &&
    listConsTyOk (env.find? listConsName) &&
    charTyOk (env.find? charName) &&
    charOfNatTyOk (env.find? charOfNatName)

/-! ## Structural-Nat literal acceleration

The official kernel accelerates the structural `Nat` operations on
literals (GMP-backed there).  Here the fast path is *certified*: an
operation participates only when its defining recurrence equations
hold by definitional equality — checked once, at install: `checkDecl`
positively rejects a nonstandard definition under one of these names,
so *presence in the store is the certificate* (no runtime flag, no
re-checking; a reduction-time re-check would in fact livelock — the
certification's own `pred zero` equation re-enters the fast path).

The certification runs in the environment *before* the operation is
stored, on the equations with the operation's self-references replaced
by its (annotated) definition value (`Expr.substConst0`): running it
after insertion would let the operation's own just-enabled fast path
discharge its all-literal-argument equations (`pred zero ≡ zero`,
`beq zero zero ≡ true`) vacuously — accepting definitions that
disagree with the fast path on those points, which is unsound.  The
install also pins the operation's and its dependencies' types to the
expected `Nat → … → Nat`/`Bool` shapes (`natOpStoredOk`): the model
reads the operations' function-space memberships off these shapes.

The environment model carries the matching semantic clause: a stored
definition under one of these names satisfies its recurrences, from
which meta-level induction over the literal yields the computed
value.  WF-recursive operations (`div`, `mod`, `gcd`) and string
literals are deferred. -/

def natPredName : Name := natName.str "pred"
def natAddName : Name := natName.str "add"
def natSubName : Name := natName.str "sub"
def natMulName : Name := natName.str "mul"
def natPowName : Name := natName.str "pow"
def natBeqName : Name := natName.str "beq"
def natBleName : Name := natName.str "ble"
def natDivName : Name := natName.str "div"
def natModName : Name := natName.str "mod"
def natGcdName : Name := natName.str "gcd"
def natLandName : Name := natName.str "land"
def natLorName : Name := natName.str "lor"
def natXorName : Name := natName.str "xor"
def natShiftLeftName : Name := natName.str "shiftLeft"
def natShiftRightName : Name := natName.str "shiftRight"
def boolName : Name := .str .anonymous "Bool"
def boolTrueName : Name := boolName.str "true"
def boolFalseName : Name := boolName.str "false"

/-- Is `e` the constant `Bool.true` — the official kernel's
`is_constant(e, Bool.true)` (`type_checker.cpp:1097`): the name, no
universe levels. -/
def Expr.isBoolTrue : Expr → Bool
  | .const c [] => c == boolTrueName
  | _ => false

/-- The pairs official's `quick_is_def_eq` decides by itself
(`type_checker.cpp:770-793`): two sorts, two literals, two `∀`s, two
`λ`s.  On such a pair `is_def_eq_core` never reaches proof irrelevance
— the divergence audit's D4 — so `defeqStep`'s hoisted `propIrrel` is
additionally gated on `!quickPair`; the arms themselves are the
structural ones further down (values are `whnfCore`-inert, so nothing
else happens in between). -/
def Expr.quickPair : Expr → Expr → Bool
  | .sort _, .sort _ => true
  | .lit _, .lit _ => true
  | .forallE .., .forallE .. => true
  | .lam .., .lam .. => true
  | _, _ => false

/-- The certified structural-`Nat` operations.  Six of them
(`add sub mul pow beq ble`) carry a literal fast path; `Nat.pred` is
here without one — it has no fast path (official's `reduce_nat` folds
nothing unary but `Nat.succ`), but `Nat.sub`'s recurrence
`sub x (succ y) = pred (sub x y)` names it, so its own recurrences
must be certified for `sub`'s literal fold to be sound. -/
def natOpNames : List Name :=
  [natPredName, natAddName, natSubName, natMulName, natPowName,
   natBeqName, natBleName]

/-- The WF-recursive operations with a *pinned-declaration* certified
fast path: at install, `checkDecl` compares the stream's definition
against a vendored pin of the toolchain's own (helper-unfolded)
definition by definitional equality, and then checks the pinned
`Nat.ble`-guarded characterization certificates
(`ConLeche/Kernel/NatOpPins.lean`) like theorem declarations — without
installing them.  Presence in the store is therefore again the
capability: a stored operation under one of these names has passed pin
and certificates, or the install declined.  (The name is historic:
the family started with `Nat.div`/`Nat.mod` and now covers every
pin-certified WF-recursive kernel-accelerated `Nat` operation —
`Nat.log2` left the list when its fast path did, official folding no
unary operation but `Nat.succ`.) -/
def natDivModNames : List Name :=
  [natDivName, natModName, natGcdName, natLandName, natLorName,
   natXorName, natShiftLeftName, natShiftRightName]

/-- The operations (transitively) involved in `c`'s recurrences. -/
def natOpDeps (c : Name) : List Name :=
  if c = natPredName then [natPredName]
  else if c = natAddName then [natAddName]
  else if c = natSubName then [natPredName, natSubName]
  else if c = natMulName then [natAddName, natMulName]
  else if c = natPowName then [natAddName, natMulName, natPowName]
  else if c = natBeqName then [natBeqName]
  else if c = natBleName then [natBleName]
  else if c = natDivName then [natPredName, natSubName, natBleName, natDivName]
  else if c = natModName then [natPredName, natSubName, natBleName, natModName]
  else if c = natGcdName then [natBleName, natModName, natGcdName]
  else if c = natLandName then
    [natAddName, natMulName, natBleName, natDivName, natModName, natLandName]
  else if c = natLorName then
    [natAddName, natSubName, natMulName, natBleName, natDivName, natModName,
     natLorName]
  else if c = natXorName then
    [natAddName, natMulName, natBleName, natDivName, natModName, natXorName]
  else if c = natShiftLeftName then
    [natSubName, natMulName, natBleName, natShiftLeftName]
  else if c = natShiftRightName then
    [natSubName, natBleName, natDivName, natShiftRightName]
  else []

/-- The defining recurrence equations of a structural-Nat operation,
over constructor forms with free variables `d`, `d + 1` (binder-free,
so the equation sides carry no annotations). -/
def natOpEquations (d : Nat) (c : Name) : List (Expr × Expr) :=
  let natTy : Expr := .const natName []
  let x : Expr := .fvar d natTy
  let y : Expr := .fvar (d + 1) natTy
  let z : Expr := .const natZeroName []
  let s : Expr → Expr := (.app (.const natSuccName []) ·)
  let ap1 : Name → Expr → Expr := fun n a => .app (.const n []) a
  let ap2 : Name → Expr → Expr → Expr := fun n a b =>
    .app (.app (.const n []) a) b
  let bT : Expr := .const boolTrueName []
  let bF : Expr := .const boolFalseName []
  if c = natPredName then
    [(ap1 c z, z), (ap1 c (s x), x)]
  else if c = natAddName then
    [(ap2 c x z, x), (ap2 c x (s y), s (ap2 c x y))]
  else if c = natSubName then
    [(ap2 c x z, x), (ap2 c x (s y), ap1 natPredName (ap2 c x y))]
  else if c = natMulName then
    [(ap2 c x z, z), (ap2 c x (s y), ap2 natAddName (ap2 c x y) x)]
  else if c = natPowName then
    [(ap2 c x z, s z), (ap2 c x (s y), ap2 natMulName (ap2 c x y) x)]
  else if c = natBeqName then
    [(ap2 c z z, bT), (ap2 c z (s y), bF), (ap2 c (s x) z, bF),
     (ap2 c (s x) (s y), ap2 c x y)]
  else if c = natBleName then
    [(ap2 c z y, bT), (ap2 c (s x) z, bF), (ap2 c (s x) (s y), ap2 c x y)]
  else []

/-- The reduct of op `c` on literal arguments (`pred` ignores the
second slot). -/
def natOpResult (c : Name) (a b : Nat) : Option Expr :=
  if c = natPredName then some (.lit (.natVal (a - 1)))
  else if c = natAddName then some (.lit (.natVal (a + b)))
  else if c = natSubName then some (.lit (.natVal (a - b)))
  else if c = natMulName then some (.lit (.natVal (a * b)))
  else if c = natPowName then
    -- the divergence audit's S2: official `reduce_pow` refuses exponents
    -- above `ReducePowMaxExp = 1 << 24` (`type_checker.cpp:616-627`) and
    -- lets `Nat.pow` unfold instead — the blow-up protection, mirrored
    if b > 16777216 then none else some (.lit (.natVal (a ^ b)))
  else if c = natDivName then some (.lit (.natVal (a / b)))
  else if c = natModName then some (.lit (.natVal (a % b)))
  else if c = natGcdName then some (.lit (.natVal (Nat.gcd a b)))
  else if c = natLandName then some (.lit (.natVal (Nat.land a b)))
  else if c = natLorName then some (.lit (.natVal (Nat.lor a b)))
  else if c = natXorName then some (.lit (.natVal (Nat.xor a b)))
  else if c = natShiftLeftName then
    some (.lit (.natVal (Nat.shiftLeft a b)))
  else if c = natShiftRightName then
    some (.lit (.natVal (Nat.shiftRight a b)))
  else if c = natBeqName then
    some (.const (if a = b then boolTrueName else boolFalseName) [])
  else if c = natBleName then
    some (.const (if a <= b then boolTrueName else boolFalseName) [])
  else none

/-- Stored-constant guards for op `c`: the `Nat` basis, every
dependency stored as a definition, and (for the `Bool`-valued ops and
the `ble`-guarded `div`/`mod`, whose semantic clauses mention the
`Bool` constructor values) the `Bool` constructors stored. -/
def natOpGuard (env : Env) (c : Name) : Bool :=
  natLitSupported env &&
  (natOpDeps c).all (fun n => match env.find? n with
    | some (.defnInfo cv _ _) => cv.levelParams.isEmpty
    | _ => false) &&
  (if c = natBeqName || c = natBleName || natDivModNames.contains c then
    (match env.find? boolTrueName with
      | some ci => ci.toConstantVal.levelParams.isEmpty
      | none => false) &&
    (match env.find? boolFalseName with
      | some ci => ci.toConstantVal.levelParams.isEmpty
      | none => false)
   else true)

/-- The pin-certified WF-recursive `Nat` operations, as a *safety
net*: the preceding certified branches normally intercept literal
applications, so this list only fires when a capability is absent
(op not stored, or a dependency missing — a mismatching declaration
already declined at install); such a *literal application* is then
positively declined (arena exit 2) rather than ground unary through
the fuel recursion.  Declaring the functions themselves is
unaffected: only the reduction path declines. -/
def natOpWfNames : List Name :=
  [natDivName, natModName, natGcdName, natLandName, natLorName,
   natXorName, natShiftLeftName, natShiftRightName]

/-- Substitute the level-monomorphic constant `n` by `r` through an
application spine (the certification equations' self-references; the
equation sides are binder-free, so only `app` recurses). -/
def Expr.substConst0 (n : Name) (r : Expr) : Expr → Expr
  | .const c us => if c = n ∧ us = [] then r else .const c us
  | .app f a => .app (Expr.substConst0 n r f) (Expr.substConst0 n r a)
  | e => e

/-- Substitute the level-monomorphic constant `n` by the *closed* term
`r` everywhere, including under binders (the div/mod certificate
statements' and proofs' references to the pinned operation; `r` being
closed, no lifting is needed).  `fvar` annotations are not entered:
the substitution runs on closed input terms only. -/
def Expr.substConstAll (n : Name) (r : Expr) : Expr → Expr
  | .const c us => if c = n ∧ us = [] then r else .const c us
  | .app f a => .app (Expr.substConstAll n r f) (Expr.substConstAll n r a)
  | .lam ty b mb =>
    .lam (Expr.substConstAll n r ty) (Expr.substConstAll n r b) mb
  | .forallE ty b mb =>
    .forallE (Expr.substConstAll n r ty) (Expr.substConstAll n r b) mb
  | .letE ty v b =>
    .letE (Expr.substConstAll n r ty) (Expr.substConstAll n r v)
      (Expr.substConstAll n r b)
  | .proj s i e => .proj s i (Expr.substConstAll n r e)
  | e => e

/-- The pinned codomain of a structural-Nat operation: `Bool` (itself
stored level-monomorphically at type `Sort 1`) for the comparisons,
`Nat` otherwise. -/
def natOpCod (env : Env) (c : Name) (e : Expr) : Bool :=
  if c = natBeqName || c = natBleName then
    e == .const boolName [] &&
    (match env.find? boolName with
     | some ci => ci.toConstantVal.levelParams.isEmpty &&
         ci.toConstantVal.type == .sort (.succ .zero)
     | none => false)
  else e == .const natName []

/-- The pinned type of a certified `Nat` operation:
`Nat → Nat` for the unary `pred`, `Nat → Nat → Nat` for the arithmetic
operations, `Nat → Nat → Bool` for the comparisons.  The model reads
the operations' function-space memberships off this shape. -/
def natOpTyPinned (env : Env) (c : Name) (ty : Expr) : Bool :=
  if c = natPredName then
    match ty with
    | .forallE dom body _mb =>
      dom == .const natName [] && natOpCod env c body
    | _ => false
  else
    match ty with
    | .forallE dom (.forallE dom2 body _mb2) _mb =>
      dom == .const natName [] && dom2 == .const natName [] &&
      natOpCod env c body
    | _ => false

/-- Op `n` is stored as a level-monomorphic definition with the pinned
type. -/
def natOpStoredOk (env : Env) (n : Name) : Bool :=
  match env.find? n with
  | some (.defnInfo cv _ _) =>
    cv.levelParams.isEmpty && natOpTyPinned env n cv.type
  | _ => false

/-- **The reduction-time test for a certified `Nat` operation** (task
#161 de-gating round A+B+C, item B3; harvest site 37, list entry P7):
is `c` stored as a definition at all?

`reduceNat` used to re-derive the whole `natOpGuard` at every literal
hit — `natLitSupported` (three `Env.find?`s), a `natOpDeps c` list
build plus a lookup per dependency (up to seven), and two more lookups
for the `Bool` constructors.  That conclusion is *carried by the
install fold invariant*, in both verification tiers and for every one
of the sixteen guarded names: `NatOps`/`NatOpsV` (the seven structural
ops, `natOpNames`) and `DivMod`/`DivModV` (the nine WF-pinned ops,
`natDivModNames`) both read

  `env.find? c = some (.defnInfo cv v hint) → natOpGuard env c = true ∧ …`

and `checkDecl` is what establishes them: it *declines* a stream that
stores one of these names without `natOpGuard env₂ c` (Checker.lean's
`.defnDecl` clause).  The converse is by computation — `c ∈ natOpDeps
c` for all sixteen — so on every environment the checker builds the two
tests agree, and the cheap one is a single `find?`. -/
def natOpStored (env : Env) (c : Name) : Bool :=
  match env.find? c with
  | some (.defnInfo _ _ _) => true
  | _ => false

/-- Peel a `∀`-telescope along an argument list (the residual type of
a fully applied telescope). -/
def piResidual : Expr → List Expr → Option Expr
  | e, [] => some e
  | .forallE _ b _, a :: as => piResidual (b.instantiate1 a) as
  | _, _ :: _ => none

/-- Are all `nF` projection slots of `T` table entries — i.e. does
`T`'s projection table exist and cover them?  (Task #175 tower-flag:
a stored table always carries bodies, so "the entry exists" is the
whole test.) -/
def towerSlotsAll (env : Env) (T : Name) (nF : Nat) : Bool :=
  (List.range nF).all fun j => (env.findProj? T j).isSome

/-- Are all `nF` projection slots of `T` recursor-backed projection
functions (the modeled path's)?  With `towerSlotsAll` the eta
certificate's slot discipline: a family's slots are all of one kind,
so the fabricated spine and the per-slot certificates agree. -/
def recSlotsAll (env : Env) (T : Name) (nF : Nat) : Bool :=
  (List.range nF).all fun j =>
    match env.find? (projFnName T j) with
    | some (.recInfo _ _ _ _) => true
    | _ => false

/-- The fabricated projections of a structure-eta spine (task #175
W4c): `.proj T j b` nodes when every slot has a table entry (the
direct install's structures — the node is what the table types and
reduces), else the modeled path's projection-function applications. -/
def etaProjs (env : Env) (T : Name) (us : List Level) (targs : List Expr)
    (b : Expr) (nF : Nat) : List Expr :=
  if towerSlotsAll env T nF then
    (List.range nF).map fun j => Expr.proj T j b
  else
    (List.range nF).map fun j =>
      Expr.mkAppN (.const (projFnName T j) us) (targs ++ [b])

/-- The constructor shape official's `try_eta_struct_core` tests before
inferring anything (`type_checker.cpp:824-829`): the candidate's head is
a stored constructor applied to exactly its parameters and fields.
(`structEtaCertWith` re-reads the same head; this is the gate that
keeps the inferences behind it.) -/
def etaCtorShape (env : Env) (a : Expr) : Bool :=
  match a.getAppFn with
  | .const c _ =>
    match env.find? c with
    | some (.ctorInfo _ cnP cnF) => a.getAppArgs.length == cnP + cnF
    | _ => false
  | _ => false

/-- The eta-rescue fabrication's argument spine: the reduced type's
arguments followed by the installed projection functions applied to
the stuck major.  Shared between the fabrication and its
synthetic-spine certificate in `majorToCtor`; a named helper keeps the
walked proof goals small. -/
def etaFabArgs (T : Name) (ust : List Level) (targs : List Expr)
    (major : Expr) (nF : Nat) : List Expr :=
  targs ++ (List.range nF).map fun j =>
    Expr.mkAppN (.const (projFnName T j) ust) (targs ++ [major])

/-- `etaFabArgs` at the entry kind (task #175 W4c): the projections
are `etaProjs`' — `.proj` nodes at an all-tower slot family, the
modeled spelling otherwise. -/
def etaFabArgsE (env : Env) (T : Name) (ust : List Level)
    (targs : List Expr) (major : Expr) (nF : Nat) : List Expr :=
  targs ++ etaProjs env T ust targs major nF

/-- **The tower-fire guard** (task #175 W4c/O4, restated at W6):
`whnfCore` fires the structural rule `proj_i (ctor p⃗ x⃗) ↦ x_i` at a
tower-backed entry under exactly the guard the tower infer branch
types the node with — at a `Prop`-declared structure the field's guard
level must be a proposition at this instantiation; at every other
family the rule fires unconditionally.

Until W6 the guard was "the structure's sort is provably nonzero at
this instantiation", which is *not* what the official kernel does
(`reduce_proj` reduces every constructor redex) and rejects the
modelled basis's own `PSigma'.fst_mk` (`PSigma'.fst (PSigma'.mk a b) ≡ a`
at symbolic `u v`, where `max u v` is neither provably zero nor
nonzero) once the pinned pair — whose entries were ungated — is
retired.  The model licence: at a squash instance (the structure's
sort is `0` at the valuation) the constructor application reads as
the point, and so does the selected field — for a non-`Prop`-declared
family every field's sort is bounded by the structure's (the O5 bound
`checkStructFieldSorts` checks), so at a zero instantiation every
field is a proposition; for a `Prop`-declared family the guard says
so of the projected field directly (`TowerEntryLaw`'s iota clause,
`ConLeche/Model/Annot/EnvModelM.lean`).  Ungated rules on a data field of a
`Prop`-declared structure stay out: such a node is not even typed
(`inferBody`'s guard). -/
def ProjEntry.fireOk (entry : ProjEntry) (us : List Level) : Bool :=
  !(Level.isEquiv entry.structSort .zero == some true) ||
    (Level.isEquiv (Level.subst entry.levelParams us entry.fieldSort) .zero
      == some true)

/-- **The pinned `And`'s projection slots, ready to fire**: the two
tower entries of `And` are stored, name the rule's constructor at the
major's parameter count, and their `Prop` guards pass at the levels
`ust` (`ProjEntry.fireOk`: `And`'s fields are propositions, so a
`.proj And j h` node is typed by the tower infer branch).  The gate of
`majorToCtor`'s `And` branch; abstracted over the lookup so the
indexed twin (`FEnv.andRescueSlotsF`) shares the body. -/
def andRescueSlotsOf (findProj? : Name → Nat → Option ProjEntry)
    (ctor : Name) (nP : Nat) (ust : List Level) : Bool :=
  (List.range 2).all fun j =>
    match findProj? andName j with
    | some e => e.ctor == ctor && e.numParams == nP && e.numFields == 2 &&
        e.fireOk ust
    | none => false

/-- `andRescueSlotsOf` at the plain environment. -/
def andRescueSlots (env : Env) (ctor : Name) (nP : Nat) (ust : List Level) : Bool :=
  andRescueSlotsOf env.findProj? ctor nP ust

/-- **The K bit at install** (`RecRule.k`): the rule's constructor has
no fields and belongs to an inductive stored with the K capability (an
inductive proposition).  Together with the recursor's rule list being
a singleton — which the reader `recRuleK` and `majorToCtor` match on
— this is the official kernel's `recursor_val::is_k()`.  Abstracted
over the lookup so the interned twin (`FEnv.find?`) shares the body. -/
def recRuleKOf (find? : Name → Option ConstantInfo) (ctor : Name) : Bool :=
  match find? ctor with
  | some (.ctorInfo cvj _ cnF) =>
    match (cvj.type.piResult).getAppFn with
    | .const T _ =>
      match find? T with
      | some (.indInfo _ caps) => caps.ruleK && cnF == 0
      | _ => false
    | _ => false
  | _ => false

/-- **The η-rescue bit at install** (`RecRule.eta`): the rule's
constructor is the η constructor of a stored η-capable inductive,
carries that inductive's own level parameters, and the recursor is not
itself a projection function (whose rescue would reduce to its own
reduct and loop).  Together with the singleton rule list this is the
standing condition of `majorToCtor`'s structure-η rescue.

The level-parameter conjunct is what lets the rescue fabricate the
constructor application at the major type's levels without comparing
the two lists per call: every route that grants η stores the
constructor at the former's level parameters (the fixpoint route's
recogniser pins `c.1.levelParams == lps`, the modeled route grants η
only at `cvC.levelParams = cvT.levelParams`, and the pinned `PUnit`
block is literal), so the conjunct holds wherever the rest does. -/
def recRuleEtaOf (find? : Name → Option ConstantInfo) (recName ctor : Name) :
    Bool :=
  match find? ctor with
  | some (.ctorInfo cvj _ _) =>
    match (cvj.type.piResult).getAppFn with
    | .const T _ =>
      match find? T with
      | some (.indInfo cvT caps) =>
        caps.eta && caps.etaCtor == ctor && !Name.isProjFnShape recName &&
          cvj.levelParams == cvT.levelParams
      | _ => false
    | _ => false
  | _ => false

/-- **Stamp a rule's two rescue bits at install** — the one place the
K and η-rescue conditions are decided.  Every route stores its rules
through this (the pinned basis blocks, the fixpoint route's generated
rules, the modeled route's checked rules, the projection functions):
the reduction then reads `RecRule.k`/`RecRule.eta` and re-derives
nothing, and the environment invariant `RecCtorsStored` records that a
set bit is the lookup's own verdict. -/
def recRuleBits (find? : Name → Option ConstantInfo) (recName : Name)
    (rl : RecRule) : RecRule :=
  { rl with k := recRuleKOf find? rl.ctor,
            eta := recRuleEtaOf find? recName rl.ctor }

@[simp] theorem recRuleBits_ctor (find? : Name → Option ConstantInfo)
    (recName : Name) (rl : RecRule) : (recRuleBits find? recName rl).ctor
      = rl.ctor := rfl

@[simp] theorem recRuleBits_rhs (find? : Name → Option ConstantInfo)
    (recName : Name) (rl : RecRule) : (recRuleBits find? recName rl).rhs
      = rl.rhs := rfl

@[simp] theorem recRuleBits_nfields (find? : Name → Option ConstantInfo)
    (recName : Name) (rl : RecRule) : (recRuleBits find? recName rl).nfields
      = rl.nfields := rfl

@[simp] theorem recRuleBits_ctorParams (find? : Name → Option ConstantInfo)
    (recName : Name) (rl : RecRule) :
    (recRuleBits find? recName rl).ctorParams = rl.ctorParams := rfl

@[simp] theorem recRuleBits_fire (find? : Name → Option ConstantInfo)
    (recName : Name) (rl : RecRule) : (recRuleBits find? recName rl).fire
      = rl.fire := rfl

@[simp] theorem recRuleBits_k (find? : Name → Option ConstantInfo)
    (recName : Name) (rl : RecRule) : (recRuleBits find? recName rl).k
      = recRuleKOf find? rl.ctor := rfl

@[simp] theorem recRuleBits_paramsBlind (find? : Name → Option ConstantInfo)
    (recName : Name) (rl : RecRule) :
    (recRuleBits find? recName rl).paramsBlind = rl.paramsBlind := rfl

@[simp] theorem recRuleBits_eta (find? : Name → Option ConstantInfo)
    (recName : Name) (rl : RecRule) : (recRuleBits find? recName rl).eta
      = recRuleEtaOf find? recName rl.ctor := rfl

@[simp] theorem map_ctor_recRuleBits (find? : Name → Option ConstantInfo)
    (recName : Name) (rs : List RecRule) :
    (rs.map (recRuleBits find? recName)).map (·.ctor) = rs.map (·.ctor) := by
  simp [List.map_map, Function.comp_def]

/-- **The stored rule of an installed projection function**: the
degenerate recursor's single rule, at the constructor's arities and
the generated right-hand side, with the two rescue bits stamped by
`recRuleBits` (both are `false` at a projection function — its own
rescue would loop — but the stamping is uniform, so the environment
invariant reads the same way at every route).  The parameter
comparison stays: the rule's law reads it. -/
def projFnRule (find? : Name → Option ConstantInfo) (T ctorName : Name)
    (pty : Expr) (nP nF i : Nat) (rhsA : Expr) : RecRule :=
  recRuleBits find? (projFnName T i)
    { ctor := ctorName, nfields := nF, ctorParams := nP,
      fire := if Expr.recRulePlain pty nP nP nP then .plain else .inert,
      rhs := rhsA, paramsBlind := false }

@[simp] theorem projFnRule_ctor (find? : Name → Option ConstantInfo)
    (T ctorName : Name) (pty : Expr) (nP nF i : Nat) (rhsA : Expr) :
    (projFnRule find? T ctorName pty nP nF i rhsA).ctor = ctorName := rfl

@[simp] theorem projFnRule_rhs (find? : Name → Option ConstantInfo)
    (T ctorName : Name) (pty : Expr) (nP nF i : Nat) (rhsA : Expr) :
    (projFnRule find? T ctorName pty nP nF i rhsA).rhs = rhsA := rfl

@[simp] theorem projFnRule_nfields (find? : Name → Option ConstantInfo)
    (T ctorName : Name) (pty : Expr) (nP nF i : Nat) (rhsA : Expr) :
    (projFnRule find? T ctorName pty nP nF i rhsA).nfields = nF := rfl

@[simp] theorem projFnRule_ctorParams (find? : Name → Option ConstantInfo)
    (T ctorName : Name) (pty : Expr) (nP nF i : Nat) (rhsA : Expr) :
    (projFnRule find? T ctorName pty nP nF i rhsA).ctorParams = nP := rfl

/-- Is a recursor K-flagged?  The stored bit of its single rule
(`RecRule.k`, computed at the block's install by `recRuleKOf`); the
official kernel reads `recursor_val::is_k()` here in just the same
way. -/
def recRuleK (rules : List RecRule) : Bool :=
  match rules with
  | [rl] => rl.k
  | _ => false

/-- The level and constructor-parameter comparands a firing rule's
checks compare the major's constructor levels and parameters against:
for a canonical (`.plain`) rule the constructor's levels link to the
recursor's by name and its parameters are the recursor's leading
arguments; for a certified nested (`.nested`) rule both are the stored
major-domain instantiations, at the recursor's level instantiation and
(for the parameters) instantiated at the recursor's leading-argument
spine (the stored pins live in the `rP`-binder prefix context — index
arguments never occur in them, by the shape certification).
(Junk for `.inert` rules — `iotaRec` declines before reading it.) -/
def recFireComparands (rl : RecRule) (lps : List Name)
    (us : List Level) (cvjLps : List Name) (args : List Expr)
    (rP : Nat) : List Level × List Expr :=
  match rl.fire with
  | .nested lvls pins =>
    (lvls.map (Level.subst lps us),
     pins.map fun p => Expr.instSpine (args.take rP) (rP - 1)
       (p.instantiateLevelParams lps us))
  | _ =>
    (cvjLps.map fun p => Level.subst lps us (.param p),
     args.take rl.ctorParams)

/-- **The type of a `.proj` node at a tower-backed entry** (task #175
S1): the stored body `F_i[p⃗ ↦ bvars, f_j ↦ .proj T j (bvar 0)]`,
level-instantiated at the subject type's levels, with the subject
type's arguments and the subject substituted for its `numParams + 1`
loose variables in ONE traversal (`instantiateList`: `bvar 0` is the
subject, `bvar (numParams - k)` parameter `k`). -/
def ProjEntry.typeAt (entry : ProjEntry) (us : List Level) (targs : List Expr)
    (pe : Expr) : Expr :=
  (entry.body.instantiateLevelParams entry.levelParams us).instantiateList
    (pe :: targs.reverse)

/-- **THE β SITE'S GATE** (task #161): does the mode's β gate fire at
this binder?

At `mode.betaGate` (i.e. at `.verified`, and nowhere else) a λ-binder
whose *validated* annotation datum is `.never` — "the codomain sort is
nonzero at every valuation" — licenses skipping the certificate: the
`Red.betaGate` rule's soundness (`Red.betaGate_sound`,
`ConLeche/Model/Rules/RedSound.lean`) derives the domain membership from the
redex's own `WellDenoted` slot and consumes no certificate at all.

At a possibly-zero datum, and at every non-gated mode, the certificate
runs unconditionally — the establishment/consumption asymmetry fence,
and task #100's de-gating ruling, both untouched: *that* gate read a
**computed** nonzero sort (unsound-to-model under the domain-relative
collapse); this one reads a **validated annotation**.

Both arms hand back the same reduct, so reducts stay
annotation-blind; the dead-branch collapse is `betaGateFires_off`
(`Verify/BetaGate.lean`).

The gate is a **pure early return**, not a wrapper around the test's
`Bool`, and that shape is load-bearing: the `else` arm is then the
pre-gate clause *byte-for-byte*, so every existing proof of every
non-gated mode continues verbatim after one `simp only` on the
condition.  (A wrapper around the test would have re-associated the
certificate's binds and cost every site a `bind_assoc` as well.)

`betaGateFires` is deliberately mode-and-datum only — it reads no
expression and runs no computation, so it is decidable *before* the
certificate would have started, which is the whole performance
point. -/
@[inline] def betaGateFires (mode : CheckMode) (pw : PropWhen) : Bool :=
  mode.betaGate && pw.isNever

/-- Is this datum a real (non-placeholder) input annotation? -/
@[inline] def pwWritten (pw : PropWhen) : Bool := !pw.isNever

/-- The datum a rebuilt binder ends up with: the one threaded in from
the node below (the chain rule), unless it carries a real input
annotation — those are judged by validation, never overwritten. -/
def annotBinderMeta (pw? : Option PropWhen) (mb : BinderMeta) : BinderMeta :=
  match pw? with
  | some pw => if pwWritten mb.pw then mb else ⟨pw⟩
  | none => mb

end ConLeche
