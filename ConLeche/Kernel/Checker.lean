module

public import ConLeche.Kernel.Inductives.NativeInstall

@[expose] public section

/-!
# The checker

`checkDecl` checks one declaration against the current environment and,
on success, returns the extended environment.  `checkDeclsPure` folds it
over a list of declarations, starting from the empty environment.  The
entry-point records (`CheckerOps` and its instantiations) and the
common `checkConstantVal` live in `ConLeche/Kernel/CheckerBase.lean`;
the modeled-inductive install in `ConLeche/Kernel/Inductives/Modeled.lean`; the
direct simple-structure install in `ConLeche/Kernel/Inductives/StructInstall.lean`.
Verification: `ConLeche.Verify.*` (inversions and claims) and
`ConLeche.Model.*` (the graded model's capstones).
-/

namespace ConLeche

variable {m : Type -> Type} [Monad m] [MonadExceptOf CheckError m]
variable (mode : CheckMode)

/-- Install one pinned basis declaration (duplicate-checked). -/
def installBasisDecl (env : Env) (ci : ConstantInfo) : m Env := do
  unless (env.find? ci.name).isNone do
    throw (.invalid s!"duplicate declaration {ci.name}")
  pure (⟨ci :: env.consts⟩ : Env)

/-- Check a `def` declaration's value against its checked constant.
The reducibility hint is stored untouched: it steers only the lazy
delta unfolding order in `isDefEq`, never a verdict, so nothing about
it needs checking. -/
def checkDefnVal (ops : CheckerOps m) (env : Env) (cv : ConstantVal)
    (value : Expr) (hint : ReducibilityHint) : m Env := do
  unless value.looseBVarsBounded 0 do
    throw (.invalid s!"loose bound variable in value of {cv.name}")
  if value.hasFvar then
    throw (.invalid s!"unexpected free variable in value of {cv.name}")
  let value ← ops.annotate env 0 value
  unless value.allLevelParamsDefined cv.levelParams do
    throw (.invalid s!"undeclared universe parameter in value of {cv.name}")
  unless value.constsResolve env do
    throw (unresolvedConstsError s!"value of {cv.name}" value)
  let vtype ← ops.inferType env 0 value
  unless ← ops.isDefEq env 0 vtype cv.type do
    throw (.invalid s!"type mismatch in definition {cv.name}")
  pure ⟨.defnInfo cv value hint :: env.consts⟩

/-- Check a `theorem` declaration's value against its checked constant
(whose type must additionally be a proposition).  **A theorem is
stored by its statement**: the constant keeps the record's own value
(the raw one, as parsed) as an unread datum — a theorem is opaque to
reduction (`unfoldDefinition` has no `thmInfo` arm), so nothing in the
kernel or the invariant ever reads it — and the annotated value is a
*realizability witness*, checked against the statement and then
discarded, exactly as an opaque's is.  This is what lets the driver
install a theorem before its value is looked at at all (phase A pushes
the record's constant; phase B annotates and checks the value,
`ConLeche/Cached/Installed.lean`). -/
def checkThmVal (ops : CheckerOps m) (env : Env) (cv : ConstantVal)
    (value : Expr) : m Env := do
  -- the type of a theorem must be a proposition
  let stype ← ops.inferType env 0 cv.type
  let u ← ops.ensureSort env 0 stype
  unless (← liftFueled "level comparison" (Level.isEquiv u .zero)) do
    throw (.invalid s!"type of theorem {cv.name} is not a proposition")
  unless value.looseBVarsBounded 0 do
    throw (.invalid s!"loose bound variable in value of {cv.name}")
  if value.hasFvar then
    throw (.invalid s!"unexpected free variable in value of {cv.name}")
  let jv ← ops.annotate env 0 value
  unless jv.allLevelParamsDefined cv.levelParams do
    throw (.invalid s!"undeclared universe parameter in value of {cv.name}")
  unless jv.constsResolve env do
    throw (unresolvedConstsError s!"value of {cv.name}" jv)
  let vtype ← ops.inferType env 0 jv
  unless ← ops.isDefEq env 0 vtype cv.type do
    throw (.invalid s!"type mismatch in theorem {cv.name}")
  pure ⟨.thmInfo cv value :: env.consts⟩

/-- Check an `opaque` declaration's value against its checked
constant: exactly the theorem check without the is-a-proposition
requirement.  The result is stored as an `axiomInfo` — the checked
value is a *realizability witness*, consumed by the model extension
and then discarded: the official kernel's `is_delta` never unfolds an
opaque (unlike theorems, task #66), so storing the value in an
unfoldable kind would be a reduction-strategy superset (it would
e.g. compute `Lean.reduceBool b` where the reference kernels are
stuck; the task-#95 honest limit relies on that stuckness). -/
def checkOpaqueVal (ops : CheckerOps m) (env : Env) (cv : ConstantVal)
    (value : Expr) : m Env := do
  unless value.looseBVarsBounded 0 do
    throw (.invalid s!"loose bound variable in value of {cv.name}")
  if value.hasFvar then
    throw (.invalid s!"unexpected free variable in value of {cv.name}")
  let value ← ops.annotate env 0 value
  unless value.allLevelParamsDefined cv.levelParams do
    throw (.invalid s!"undeclared universe parameter in value of {cv.name}")
  unless value.constsResolve env do
    throw (unresolvedConstsError s!"value of {cv.name}" value)
  let vtype ← ops.inferType env 0 value
  unless ← ops.isDefEq env 0 vtype cv.type do
    throw (.invalid s!"type mismatch in opaque {cv.name}")
  pure ⟨.axiomInfo cv :: env.consts⟩
/-- Certify a list of recurrence equations by definitional equality
(at depth 2: the equations' variables are `fvar 0`/`fvar 1`). -/
def certifyNatEqs (ops : CheckerOps m) (env : Env) :
    List (Expr × Expr) → m Bool
  | [] => pure true
  | eq :: rest => do
    if ← ops.isDefEq env 2 eq.1 eq.2 then
      certifyNatEqs ops env rest
    else pure false

/-- The pinned defining expression of a pin-certified WF-recursive op
in one **pin variant** (`ConLeche/Kernel/NatOpPinSet.lean`: one
toolchain's generated pins, `ConLeche/Kernel/NatOpPins.lean` splices one
per committed dump). -/
def divModDeclPin (ps : NatOpPinSet) (c : Name) : Expr :=
  if c = natDivName then ps.divPin
  else if c = natGcdName then ps.gcdPin
  else if c = natLandName then ps.landPin
  else if c = natLorName then ps.lorPin
  else if c = natXorName then ps.xorPin
  else if c = natShiftLeftName then ps.shiftLeftPin
  else if c = natShiftRightName then ps.shiftRightPin
  else ps.modPin

/-- The certificate proof terms of a pin-certified WF-recursive op in
one pin variant, one per statement of `divModCertStmts`. -/
def divModCertProofs (ps : NatOpPinSet) (c : Name) : List Expr :=
  if c = natDivName then ps.divProofs
  else if c = natGcdName then ps.gcdProofs
  else if c = natLandName then ps.landProofs
  else if c = natLorName then ps.lorProofs
  else if c = natXorName then ps.xorProofs
  else if c = natShiftLeftName then ps.shiftLeftProofs
  else if c = natShiftRightName then ps.shiftRightProofs
  else ps.modProofs

/-- The pinned characterization statements of a pin-certified
WF-recursive op, in *open* form over `x := fvar 0`, `y := fvar 1` (the
hypotheses become `fvar 2, fvar 3`): per certificate, the list of
hypothesis types and the characteristic equation `Eq Nat lhs rhs`.
The guards are spelled with the already-certified `Nat.ble` (never the
`Nat.le`/`Nat.lt` `Prop` inductives) and the numeral `1` as
`Nat.succ Nat.zero`, so the model side consumes them through the
existing `NatOpsOk` literal semantics for `ble`/`sub`.  The op's
self-reference is `.const c []`, substituted with the stored annotated
value before checking (all statement components are application
spines, so `Expr.substConst0` applies). -/
def divModCertStmts (c : Name) : List (List Expr × Expr) :=
  let natTy : Expr := .const natName []
  let x : Expr := .fvar 0 natTy
  let y : Expr := .fvar 1 natTy
  let one : Expr := .app (.const natSuccName []) (.const natZeroName [])
  let ble2 : Expr → Expr → Expr := fun a b =>
    .app (.app (.const natBleName []) a) b
  let eqB : Expr → Expr → Expr := fun a b =>
    .app (.app (.app (.const eqName [.succ .zero]) (.const boolName [])) a) b
  let eqN : Expr → Expr → Expr := fun a b =>
    .app (.app (.app (.const eqName [.succ .zero]) natTy) a) b
  let op2 : Expr → Expr → Expr := fun a b => .app (.app (.const c []) a) b
  let sub2 : Expr → Expr → Expr := fun a b =>
    .app (.app (.const natSubName []) a) b
  let bT : Expr := .const boolTrueName []
  let bF : Expr := .const boolFalseName []
  let z : Expr := .const natZeroName []
  let two : Expr := .app (.const natSuccName []) one
  let mod2 : Expr → Expr → Expr := fun a b =>
    .app (.app (.const natModName []) a) b
  let div2 : Expr → Expr → Expr := fun a b =>
    .app (.app (.const natDivName []) a) b
  let add2 : Expr → Expr → Expr := fun a b =>
    .app (.app (.const natAddName []) a) b
  let mul2 : Expr → Expr → Expr := fun a b =>
    .app (.app (.const natMulName []) a) b
  if c = natGcdName then
    -- `gcd`: `1 ≤ x → gcd x y = gcd (y % x) x`, `x = 0 → gcd x y = y`
    [([eqB (ble2 one x) bT], eqN (op2 x y) (op2 (mod2 y x) x)),
     ([eqB (ble2 one x) bF], eqN (op2 x y) y)]
  else if c = natShiftLeftName then
    -- `1 ≤ y → x <<< y = (2*x) <<< (y-1)`, `y = 0 → x <<< y = x`
    [([eqB (ble2 one y) bT], eqN (op2 x y) (op2 (mul2 two x) (sub2 y one))),
     ([eqB (ble2 one y) bF], eqN (op2 x y) x)]
  else if c = natShiftRightName then
    -- `1 ≤ y → x >>> y = (x >>> (y-1)) / 2`, `y = 0 → x >>> y = x`
    [([eqB (ble2 one y) bT], eqN (op2 x y) (div2 (op2 x (sub2 y one)) two)),
     ([eqB (ble2 one y) bF], eqN (op2 x y) x)]
  else if c = natLandName then
    -- `1 ≤ x → x &&& y = 2*((x/2) &&& (y/2)) + (x%2)*(y%2)`,
    -- `x = 0 → x &&& y = 0`
    [([eqB (ble2 one x) bT],
      eqN (op2 x y) (add2 (mul2 two (op2 (div2 x two) (div2 y two)))
        (mul2 (mod2 x two) (mod2 y two)))),
     ([eqB (ble2 one x) bF], eqN (op2 x y) z)]
  else if c = natLorName then
    -- `1 ≤ x → x ||| y = 2*((x/2) ||| (y/2)) + (x%2 + y%2 - (x%2)*(y%2))`,
    -- `x = 0 → x ||| y = y`
    [([eqB (ble2 one x) bT],
      eqN (op2 x y) (add2 (mul2 two (op2 (div2 x two) (div2 y two)))
        (sub2 (add2 (mod2 x two) (mod2 y two))
          (mul2 (mod2 x two) (mod2 y two))))),
     ([eqB (ble2 one x) bF], eqN (op2 x y) y)]
  else if c = natXorName then
    -- `1 ≤ x → x ^^^ y = 2*((x/2) ^^^ (y/2)) + (x%2 + y%2) % 2`,
    -- `x = 0 → x ^^^ y = y`
    [([eqB (ble2 one x) bT],
      eqN (op2 x y) (add2 (mul2 two (op2 (div2 x two) (div2 y two)))
        (mod2 (add2 (mod2 x two) (mod2 y two)) two))),
     ([eqB (ble2 one x) bF], eqN (op2 x y) y)]
  else
  let recRhs : Expr :=
    if c = natDivName then .app (.const natSuccName []) (op2 (sub2 x y) y)
    else op2 (sub2 x y) y
  let baseRhs : Expr := if c = natDivName then .const natZeroName [] else x
  [([eqB (ble2 y x) bT, eqB (ble2 one y) bT], eqN (op2 x y) recRhs),
   ([eqB (ble2 y x) bF], eqN (op2 x y) baseRhs),
   ([eqB (ble2 one y) bF], eqN (op2 x y) baseRhs)]

/-- The vendored proof applied to the statement's free variables
(`x`, `y`, then one `fvar` per hypothesis, carrying the hypothesis
*type* as its `fvar` annotation — the checker's implicit local
context). -/
def divModCertApplied (proofS : Expr) (hyps : List Expr) : Expr :=
  let base : Expr :=
    .app (.app proofS (.fvar 0 (.const natName [])))
      (.fvar 1 (.const natName []))
  match hyps with
  | [h1] => .app base (.fvar 2 h1)
  | [h1, h2] =>
    .app (.app base (.fvar 2 h1))
      (.fvar 3 h2)
  | _ => base

/-- The syntactic guards of one certificate check: the substituted
proof is closed, level-monomorphic and resolving, and the substituted
statement components resolve. -/
def divModCertGuard (env : Env) (c : Name) (annVal : Expr)
    (hyps : List Expr) (eqE proof : Expr) : Bool :=
  (Expr.substConstAll c annVal proof).looseBVarsBounded 0 &&
  !(Expr.substConstAll c annVal proof).hasFvar &&
  (Expr.substConstAll c annVal proof).allLevelParamsDefined [] &&
  (Expr.substConstAll c annVal proof).constsResolve env &&
  (hyps.map (Expr.substConst0 c annVal)).all
    (fun h => h.constsResolve env) &&
  (Expr.substConst0 c annVal eqE).constsResolve env

/-- Check the pinned certificates of op `c`: per certificate, the
vendored proof (with the op's self-references replaced by the stored
annotated value — the checks run in the *pre-insertion* environment,
exactly like the structural-Nat certification: post-insertion the op's
own just-enabled fast path would participate in checking the very
certificates that justify it) is applied to free variables typed by
the pinned open statement, its type inferred, and compared against the
pinned characteristic equation.  This checks each certificate exactly
like a theorem declaration over an opened telescope — nothing is
installed. -/
def checkDivModCerts (ops : CheckerOps m) (env : Env) (c : Name)
    (annVal : Expr) : List (List Expr × Expr) → List Expr → m Bool
  | [], [] => pure true
  | (hyps, eqE) :: srest, proof :: prest => do
    if divModCertGuard env c annVal hyps eqE proof then
      let appliedA ← ops.annotate env 4
        (divModCertApplied (Expr.substConstAll c annVal proof)
          (hyps.map (Expr.substConst0 c annVal)))
      let tp ← ops.inferType env 4 appliedA
      if ← ops.isDefEq env 4 tp (Expr.substConst0 c annVal eqE) then
        checkDivModCerts ops env c annVal srest prest
      else pure false
    else pure false
  | _, _ => pure false

/-- Environment prerequisites of a certified `Nat.div`/`Nat.mod`:
dependency guard, pinned dependencies, the pinned `Eq` basis (the
certificate statements are equations in the pinned equality), and the
`Bool` constructors stored at the type `Bool` itself (the guards'
`true`/`false` must inhabit the `Bool` value semantically). -/
def divModEnvGuard (env2 : Env) (c : Name) : Bool :=
  natOpGuard env2 c && (natOpDeps c).all (natOpStoredOk env2) &&
  env2.find? eqName == some eqA &&
  (match env2.find? boolTrueName with
    | some ci => ci.toConstantVal.type == .const boolName []
    | none => false) &&
  (match env2.find? boolFalseName with
    | some ci => ci.toConstantVal.type == .const boolName []
    | none => false)

/-- Syntactic guards on one variant's pin (generated; checked once at
install rather than proven about the blob). -/
def divModPinGuard (ps : NatOpPinSet) (env : Env) (c : Name) : Bool :=
  (divModDeclPin ps c).looseBVarsBounded 0 && !(divModDeclPin ps c).hasFvar &&
  (divModDeclPin ps c).allLevelParamsDefined [] &&
  (divModDeclPin ps c).constsResolve env

/-- All of one variant's certificates' syntactic guards at once.
Checked *before* the pin comparison; a failure moves on to the next
variant: a stream may legitimately stop short of the constants a
variant's proofs mention. -/
def divModCertsGuard (ps : NatOpPinSet) (env : Env) (c : Name)
    (annVal : Expr) : Bool :=
  ((divModCertStmts c).zip (divModCertProofs ps c)).all
    (fun p => divModCertGuard env c annVal p.1.1 p.1.2 p.2)

/-- **One pin variant's attempt** (task #273): the stored value against
the variant's pin by definitional equality, and on a match the
variant's certificates (`checkDivModCerts`).  `true` = matched, the
fast path is justified; `false` = the pin is not definitionally equal,
or a certificate did not check.  The third outcome is an error thrown
from inside — a certificate blob generated by another toolchain can be
ill-typed against this stream (the v4.33.0 blobs apply `Decidable.rec`
with two minors; on lean4 master it has one), and the pin comparison
does not see that (the pins mention `ite`/`dite`/`Nat.decLe` BY NAME,
so a stream from another toolchain matches the pin syntactically).
`CheckerOps.orElse` turns that error into "this variant does not
match" — the only place a thrown error is recovered from, and it is
scoped to exactly this attempt. -/
def checkDivModPinAt (ops : CheckerOps m) (env : Env) (c : Name)
    (value' : Expr) (ps : NatOpPinSet) : m Bool := do
  let pinA ← ops.annotate env 0 (divModDeclPin ps c)
  let okPin ← ops.isDefEq env 0 value' pinA
  if okPin then
    checkDivModCerts ops env c value' (divModCertStmts c)
      (divModCertProofs ps c)
  else pure false

/-- What a variant failed on, for the decline message.  The pure
instantiations always report the `none` text (see
`CheckerOps.orElse`); the executable reports the error. -/
def divModAttemptReason (ps : NatOpPinSet) : Option CheckError → String
  | none => s!"{ps.toolchain}: pin not definitionally equal, or a \
      certificate failed"
  | some e => s!"{ps.toolchain}: {e}"

/-- **The variant loop**: the first variant whose guards pass and whose
attempt succeeds enables the fast path; every other outcome moves on
to the next variant, and when none is left the stream DECLINES with
the per-variant reasons.  A certificate failure after a pin match used
to be an internal error (exit 3); with variants it is one variant not
matching (the pin comparison cannot tell toolchains apart, see
`checkDivModPinAt`), so the decline message is the operator's
diagnosis: `scripts/diagnose_natop_prefix.py` explains a "ground
constants absent" entry, the executable's error text the rest. -/
def checkDivModPinLoop (ops : CheckerOps m) (env : Env) (c : Name)
    (value' : Expr) : List NatOpPinSet → List String → m Unit
  | [], tried =>
    throw (.notImplemented s!"unsupported Nat.div/mod spelling ({c}: no \
      pin variant matched — {String.intercalate "; " tried})")
  | ps :: rest, tried =>
    if divModPinGuard ps env c && divModCertsGuard ps env c value' then
      ops.orElse (checkDivModPinAt ops env c value' ps) fun r =>
        checkDivModPinLoop ops env c value' rest
          (tried ++ [divModAttemptReason ps r])
    else
      checkDivModPinLoop ops env c value' rest
        (tried ++ [s!"{ps.toolchain}: pin or certificate ground constants \
          absent"])

/-- The pin-certified operations' install gate, run after the ordinary
definition check (`env2` is the already-extended environment, `env`
the pre-insertion one all checks run in): the dependency and
pinned-`Eq` guards, then the pin variants in `pins` order
(`checkDivModPinLoop`) — the stored value against each variant's pin
of its toolchain's own helper-unfolded definition by definitional
equality, and on a match that variant's certificates
(`checkDivModCerts`).  No variant matching is a decline (exit 2),
never a silent accept; the operation's literal fast path is enabled
exactly when a variant's certificates checked in this run.

**The variant list is a parameter** (task #304): every function from
here up to the fold takes it, and the shipped checker passes
`natOpPinSets` — so a statement about the checker can be made for an
arbitrary list, which is what the pin list being data rather than a
constant buys.  The parameter sits right after `ops` (the "how to
check" arguments) all the way up, and right after `mode` in the cached
driver. -/
def checkDivModPin (ops : CheckerOps m) (pins : List NatOpPinSet)
    (env env2 : Env) (c : Name) : m Unit := do
  if divModEnvGuard env2 c then
    match env2.find? c with
    | some (.defnInfo _ value' _) =>
      checkDivModPinLoop ops env c value' pins []
    | _ => throw (.internal s!"Nat.div/mod operation not stored ({c})")
  else throw (.notImplemented
    s!"unsupported Nat.div/mod environment ({c})")

/-- The `Lean.reduceNat`/`Lean.reduceBool` install gate, run after the
ordinary opaque check (`env2` is the already-extended environment,
`env` the pre-insertion one the comparisons run in; `value` the
declaration's raw witness value, annotated again here — the stored
constant is an `axiomInfo`, which carries no value):

* the stored constant must carry the pinned type;
* the witness value must be definitionally equal to the build-time pin
  of the toolchain's own defining expression
  (`ConLeche/Kernel/TrustPins.lean`) — toolchain drift surfaces as a
  decline (exit 2), never silently;
* the *identity certificate*: `value x ≡ x` over an opened `fvar` at
  the element type.  This is what the model consumes
  (`EnvModel.reduce_ops`): with the operation interpreted as the
  identity, the `ofReduce*` axioms' types are trivially inhabited.  A
  certificate failure after the pin matched is an internal
  inconsistency (the pin *is* the identity function). -/
def checkReducePin (ops : CheckerOps m) (env env2 : Env) (c : Name)
    (value : Expr) : m Unit := do
  if reduceStoredOk env2 c && reduceElemOk env c then
    if reducePinGuard env c then do
      let valA ← ops.annotate env 0 value
      let pinA ← ops.annotate env 0 (reduceDeclPin c)
      let okPin ← ops.isDefEq env 0 valA pinA
      if okPin then do
        let x := reduceCertVar c
        let ok ← ops.isDefEq env 1 (.app valA x) x
        if ok then pure ()
        else throw (.internal
          s!"pinned compiler-trust opaque is not the identity ({c})")
      else throw (.notImplemented
        s!"unsupported compiler-trust opaque spelling ({c})")
    else throw (.notImplemented
      s!"unsupported compiler-trust opaque spelling ({c}: pin ground constants absent)")
  else throw (.notImplemented
    s!"unsupported compiler-trust opaque declaration ({c})")

/-- **Install the pinned (pre-annotated) basis block.**  The three
records that install one — the fold's own `basisDecl` kind, a stream
block `basisPinHit` recognises and a quotient record `quotPinHit`
recognises — share this body, so what is proved of one is proved of
all three.  The quotient block's types mention the pinned equality
former. -/
def checkBasisDecl (env : Env) (kind : BasisKind) : m Env := do
  if kind = .quotK then
    unless env.find? eqName = some eqA do
      throw (.notImplemented "quotient basis requires the pinned Eq basis")
  kind.declsA.foldlM installBasisDecl env

/-- Check a single declaration, extending the environment on success. -/
def checkDecl (ops : CheckerOps m) (pins : List NatOpPinSet) (env : Env)
    (d : Declaration) : m Env := do
  match d with
  | .defnDecl cv value hint => do
    let cv ← checkConstantVal ops env cv
    let env2 ← checkDefnVal ops env cv value hint
    -- Structural-Nat pins: the fast-path ops must be the standard
    -- structural recursions — their recurrence equations are checked
    -- by definitional equality here, once, so the literal fast path's
    -- reduction-time certification never fails on an accepted
    -- environment.  A nonstandard definition under one of these names
    -- is positively unsupported.  The equations are certified in the
    -- *pre-insertion* environment with the operation's self-references
    -- replaced by its stored value (see `ConLeche/Kernel/Core.lean`:
    -- certifying after insertion would let the operation's own fast
    -- path discharge its all-literal equations vacuously), and the
    -- operation's and its dependencies' stored types are pinned.
    if natOpNames.contains cv.name then
      unless natOpGuard env2 cv.name &&
          (natOpDeps cv.name).all (natOpStoredOk env2) do
        throw (.notImplemented
          s!"nonstandard structural Nat operation environment ({cv.name})")
      match env2.find? cv.name with
      | some (.defnInfo _ value' _) =>
        let ok ← certifyNatEqs ops env
          ((natOpEquations 0 cv.name).map fun eq =>
            (Expr.substConst0 cv.name value' eq.1,
             Expr.substConst0 cv.name value' eq.2))
        unless ok do
          throw (.notImplemented
            s!"nonstandard structural Nat operation ({cv.name})")
      | _ => throw (.internal s!"structural Nat operation not stored ({cv.name})")
    -- WF-recursive Nat pins (`Nat.div`/`Nat.mod`): the stored value must
    -- be definitionally equal to some committed pin variant of a
    -- toolchain's own (helper-unfolded) definition, and that variant's
    -- pinned `Nat.ble`-guarded characterization certificates must
    -- check (in the pre-insertion environment, self-references
    -- substituted; see `checkDivModCerts`) — they are not installed;
    -- their success is what the model side consumes for the literal
    -- fast path.  No variant matching is a decline (exit 2) naming
    -- what each variant failed on — elaborator drift surfaces
    -- visibly, never silently (task #273).
    if natDivModNames.contains cv.name then
      checkDivModPin ops pins env env2 cv.name
    pure env2
  | .thmDecl cv value =>
    let cv ← checkConstantVal ops env cv
    checkThmVal ops env cv value
  | .opaqueDecl cv value => do
    let cv ← checkConstantVal ops env cv
    let env2 ← checkOpaqueVal ops env cv value
    -- Compiler-trust opaques (`Lean.reduceNat`/`Lean.reduceBool`,
    -- task #95): the stored value must be definitionally equal to the
    -- build-time pin of the toolchain's own defining expression — the
    -- gate that lets the `ofReduce*` axioms' identity certificates
    -- never fail on an accepted environment.
    if reduceOpNames.contains cv.name then
      checkReducePin ops env env2 cv.name value
    pure env2
  | .axiomDecl cv =>
    -- Pinned axioms are *installed*: the two standard axioms
    -- (`propext` via the stored `Iff` recursor and extensionality of
    -- propositions, `Classical.choice` via the stored `Nonempty`
    -- recursor and global choice) and the `Init` compiler-trust
    -- family (task #95: `Lean.trustCompiler` as an opaque with value
    -- `True.intro`; `Lean.ofReduceNat`/`Lean.ofReduceBool` over the
    -- pinned identity opaques, trivially true).  All types and the
    -- shapes of the inductives they quantify over are pinned (up to
    -- the exporter's unstable hygienic binder names).  `sorryAx` — the
    -- one axiom the checker tolerates as a DECLARATION (user ruling) —
    -- is well-formedness-checked but installs NOTHING: an export
    -- declares it whenever its module mentions `sorry`, whether or not
    -- anything uses it, so the record is skipped and the run continues,
    -- and because there is no set model for it any USE of the name
    -- declines at the record that uses it (`unknownConstError`,
    -- `ConLeche/Kernel/Core.lean`, and `unresolvedConstsError`,
    -- `ConLeche/Kernel/CheckerBase.lean`).  Any other axiom
    -- is a positive decline at its own record; a *pinned name* with a
    -- non-pinned shape likewise (the pin would otherwise shadow).
    -- **`Quot.sound` is the pinned quotient BLOCK's own record**
    -- (task #293): the export writes it as an ordinary axiom record
    -- beside the four `#QUOT` ones, so it arrives here — compared with
    -- the pin and installing NOTHING of its own (the pinned block
    -- installs the axiom together with its three other constants, at
    -- the first quotient record that matches), and DECLINING when it
    -- does not match.  The comparison precedes the common checks
    -- because the name is a reserved basis name: this record IS the
    -- pinned block's, not a redeclaration of it.  What stood here was
    -- a parser check (`ConLeche/Frontend/ExportC.lean`), which
    -- swallowed the record before the fold ever saw it.
    if cv.name = quotSoundName then
      (if ConstantInfo.canonEq (.axiomInfo cv) (quotBasis.getD 4 (.axiomInfo default)) then
        pure env
      else
        throw (.notImplemented "quotient soundness axiom mismatch"))
    else do
      let cvA ← checkConstantVal ops env cv
      if stdAxiomOk env cvA then
        pure ⟨.axiomInfo cvA :: env.consts⟩
      else if cvA.name = trustCompilerName then
        -- `Lean.trustCompiler : True` is trivially realizable (task
        -- #95): installed exactly like a checked `opaque` with witness
        -- value `True.intro` over the pinned `True` family — the pin
        -- guarantees everything the ordinary opaque check would have
        -- checked for that value, and the model interprets the constant
        -- by `True.intro`'s interpretation.
        if trustCompilerOk env cvA then
          pure ⟨.axiomInfo cvA :: env.consts⟩
        else throw (.notImplemented
          s!"unsupported Lean.trustCompiler shape ({cv.name})")
      else if cvA.name = ofReduceNatName ∨ cvA.name = ofReduceBoolName then
        -- The pinned `ofReduce*` axioms (task #95): over the pinned
        -- `Eq` basis, the element inductive and the identity-certified
        -- reduce opaque, `∀ a b, reduce a = b → a = b` interprets to an
        -- inhabited proposition (the hypothesis *is* the conclusion).
        if ofReduceAxOk env cvA then
          pure ⟨.axiomInfo cvA :: env.consts⟩
        else throw (.notImplemented
          s!"unsupported compiler-trust axiom environment ({cv.name})")
      else if cvA.name = propextName ∨ cvA.name = choiceName then
        throw (.notImplemented s!"standard axiom shape mismatch ({cv.name})")
      else if cvA.name = sorryAxName then
        pure env
      else
        throw (.notImplemented s!"non-standard axiom ({cv.name})")
  | .basisDecl kind => checkBasisDecl env kind
  | .indDecl block nP =>
    -- **THE PINNED BASIS BLOCKS** (task #293).  A stream's `Nat` block
    -- arrives as an ordinary `indDecl` — the decoder emits the file's
    -- records and nothing else — and it is recognised HERE: a block
    -- whose members are named as one of the five pins' and which
    -- matches it up to `ConstantInfo.canon` installs the PIN (the
    -- annotated, model-proved literals `installBasisDecl` puts in the
    -- environment verbatim).  A block under a pinned name that does not
    -- match falls through to the ordinary route, where
    -- `checkConstantVal`'s reserved-name check REJECTS it: a basis
    -- redefinition is invalid input (task #181's ruling).
    match basisPinHit block with
    | some kind => checkBasisDecl env kind
    | none =>
    -- TASK #228 — THE DECLARED PARAMETER COUNT, first and for both
    -- routes.  Official reads `nparams` off the declaration and checks
    -- the block against it (`check_inductive_types`' telescope loop,
    -- and the replay's structural comparison of every constructor
    -- record with the generated one); `indParamsOk` is that check,
    -- one-sided, so a `false` is official's own reject.  It runs
    -- BEFORE the dispatch because it is a property of the DECLARATION
    -- and not of a route: the modeled path reaches it too, which is
    -- where a block with no constructor and no recursor record — the
    -- shape neither route recognises — is rejected rather than
    -- declined (arena 047).
    if indParamsOk nP block then
      -- ONE ROUTE (task #210): the fixpoint route takes every block it
      -- RECOGNISES — one type former, one recursor, ordinary,
      -- finitary-recursive or reflexive fields (the structure and sum
      -- routes it replaced were deleted at Part C).  Everything else is
      -- the modeled path's, and its model is the in-process modeller's
      -- (`ConLeche/Frontend/InModel.lean`), whose records precede the
      -- block in the very same parse; `checkModeled` DECLINES, naming the
      -- block, when there is none.  The dispatch is the RECOGNISER alone
      -- (task #219): a mutual or nested block carries several type
      -- formers, resp. several recursors, so `sumSplit` refuses it
      -- outright and no model lookup is needed to route it — which is why
      -- a stream record that happens to be named `T._model` has no effect
      -- on any block.  The module split (`CheckerBase ← Modeled ←
      -- Checker`) is why the dispatch lives here and not inside
      -- `checkModeled`.
      match nativeParts? nP block with
      | some p => checkNative ops env p
      | none => checkModeled mode ops env block
    else throw (.invalid "number of parameters mismatch")
  | .quotDecl k cv =>
    -- **THE QUOTIENT PACKAGE** (task #293).  The export writes it as
    -- four records; each one is compared with the pinned block's
    -- constant at its own kind, and the FIRST that matches installs the
    -- pinned block whole (the other three then find it installed and
    -- add nothing — they are the same declaration).  A record that does
    -- not match is a quotient this checker positively does not support:
    -- the decline the parser used to issue, now at the record, in the
    -- fold.
    if quotPinHit k cv then
      (match k with
       | .type => checkBasisDecl env .quotK
       | _ => pure env)
    else throw (.notImplemented (match k with
      | .sound => "quotient soundness axiom mismatch"
      | _ => "quotient declaration mismatch"))

/-- Check a list of declarations in order, starting from the empty
environment. -/
def checkDeclsPure (ops : CheckerOps m) (pins : List NatOpPinSet)
    (ds : List Declaration) : m Env :=
  ds.foldlM (checkDecl mode ops pins) Env.empty

end ConLeche
