module

public import IxC.Kernel.Inductives.NativeInstall

@[expose] public section

/-!
# The checker

`checkDecl` checks one declaration against the current environment and,
on success, returns the extended environment.  `checkDeclsPure` folds it
over a list of declarations, starting from the empty environment.  The
entry-point records (`CheckerOps` and its instantiations) and the
common `checkConstantVal` live in `IxC/Kernel/CheckerBase.lean`;
the modeled-inductive install in `IxC/Kernel/Inductives/Modeled.lean`; the
direct simple-structure install in `IxC/Kernel/Inductives/StructInstall.lean`.
Verification: `Ix.Kernel.Verify.*` (inversions and claims) and
`Ix.Kernel.Model.*` (the graded model's capstones).
-/

namespace Ix.Kernel

variable {m : Type -> Type} [Monad m] [MonadExcept (CheckError md) m]
variable (mode : CheckMode)

/-- Install one pinned basis declaration (duplicate-checked). -/
def installBasisDecl (env : Env md) (ci : ConstantInfo md) : m (Env md) := do
  unless (env.find? ci.name).isNone do
    throw (.invalid msg!"duplicate declaration {ci.name}")
  pure (⟨ci :: env.consts⟩ : Env md)

/-- Check a `def` declaration's value against its checked constant.
The reducibility hint is stored untouched: it steers only the lazy
delta unfolding order in `isDefEq`, never a verdict, so nothing about
it needs checking. -/
def checkDefnVal (ops : (CheckerOps md) m) (env : Env md) (cv : ConstantVal md)
    (value : Expr md) (hint : ReducibilityHint) : m (Env md) := do
  unless value.looseBVarsBounded 0 do
    throw (.invalid msg!"loose bound variable in value of {cv.name}")
  if value.hasFvar then
    throw (.invalid msg!"unexpected free variable in value of {cv.name}")
  let value ← ops.annotate env 0 value
  unless value.allLevelParamsDefined cv.levelParams do
    throw (.invalid msg!"undeclared universe parameter in value of {cv.name}")
  unless value.constsResolve env do
    throw (unresolvedConstsError msg!"value of {cv.name}" value)
  let vtype ← ops.inferType env 0 value
  unless ← ops.isDefEq env 0 vtype cv.type do
    throw (.invalid msg!"type mismatch in definition {cv.name}")
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
`IxC/Kernel/Cached/Installed.lean`). -/
def checkThmVal (ops : (CheckerOps md) m) (env : Env md) (cv : ConstantVal md)
    (value : Expr md) : m (Env md) := do
  -- the type of a theorem must be a proposition
  let stype ← ops.inferType env 0 cv.type
  let u ← ops.ensureSort env 0 stype
  unless (← liftFueled "level comparison" (Level.isEquiv u .zero)) do
    throw (.invalid msg!"type of theorem {cv.name} is not a proposition")
  unless value.looseBVarsBounded 0 do
    throw (.invalid msg!"loose bound variable in value of {cv.name}")
  if value.hasFvar then
    throw (.invalid msg!"unexpected free variable in value of {cv.name}")
  let jv ← ops.annotate env 0 value
  unless jv.allLevelParamsDefined cv.levelParams do
    throw (.invalid msg!"undeclared universe parameter in value of {cv.name}")
  unless jv.constsResolve env do
    throw (unresolvedConstsError msg!"value of {cv.name}" jv)
  let vtype ← ops.inferType env 0 jv
  unless ← ops.isDefEq env 0 vtype cv.type do
    throw (.invalid msg!"type mismatch in theorem {cv.name}")
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
def checkOpaqueVal (ops : (CheckerOps md) m) (env : Env md) (cv : ConstantVal md)
    (value : Expr md) : m (Env md) := do
  unless value.looseBVarsBounded 0 do
    throw (.invalid msg!"loose bound variable in value of {cv.name}")
  if value.hasFvar then
    throw (.invalid msg!"unexpected free variable in value of {cv.name}")
  let value ← ops.annotate env 0 value
  unless value.allLevelParamsDefined cv.levelParams do
    throw (.invalid msg!"undeclared universe parameter in value of {cv.name}")
  unless value.constsResolve env do
    throw (unresolvedConstsError msg!"value of {cv.name}" value)
  let vtype ← ops.inferType env 0 value
  unless ← ops.isDefEq env 0 vtype cv.type do
    throw (.invalid msg!"type mismatch in opaque {cv.name}")
  pure ⟨.axiomInfo cv :: env.consts⟩
/-- Certify a list of recurrence equations by definitional equality
(at depth 2: the equations' variables are `fvar 0`/`fvar 1`). -/
def certifyNatEqs (ops : (CheckerOps md) m) (env : Env md) :
    List (Expr md × Expr md) → m Bool
  | [] => pure true
  | eq :: rest => do
    if ← ops.isDefEq env 2 eq.1 eq.2 then
      certifyNatEqs ops env rest
    else pure false

/-- The proof applied to the statement's free variables
(`x`, `y`, then one `fvar` per hypothesis, carrying the hypothesis
*type* as its `fvar` annotation — the checker's implicit local
context). -/
def divModCertApplied (proofS : Expr md) (hyps : List (Expr md)) : Expr md :=
  let base : Expr md :=
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
def divModCertGuard (env : Env md) (c : Key md) (annVal : Expr md)
    (hyps : List (Expr md)) (eqE proof : Expr md) : Bool :=
  (Expr.substConstAll c annVal proof).looseBVarsBounded 0 &&
  !(Expr.substConstAll c annVal proof).hasFvar &&
  (Expr.substConstAll c annVal proof).allLevelParamsDefined [] &&
  (Expr.substConstAll c annVal proof).constsResolve env &&
  (hyps.map (Expr.substConst0 c annVal)).all
    (fun h => h.constsResolve env) &&
  (Expr.substConst0 c annVal eqE).constsResolve env

/-- Check the certificates of op `c` against its specification's
statements (`divModCertStmts`): per certificate, the evidence's proof
(with the op's self-references replaced by the stored annotated value —
the checks run in the *pre-insertion* environment, exactly like the
structural-Nat certification: post-insertion the op's own just-enabled
fast path would participate in checking the very certificates that
justify it) is applied to free variables typed by the open statement,
its type inferred, and compared against the characteristic equation.
This checks each certificate exactly like a theorem declaration over an
opened telescope — nothing is installed. -/
def checkDivModCerts (ops : (CheckerOps md) m) (env : Env md) (c : Key md)
    (annVal : Expr md) : List (List (Expr md) × Expr md) → List (Expr md) → m Bool
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

/-- Environment prerequisites of a certified well-founded operation:
dependency guard, its dependencies stored at their pinned types, the
pinned `Eq` basis (the certificate statements are equations in the
pinned equality), and the `Bool` constructors stored at the type
`Bool` itself (the guards' `true`/`false` must inhabit the `Bool` value
semantically). -/
def divModEnvGuard (env2 : Env md) (c : Key md) : Bool :=
  natOpGuard env2 c && (natOpDeps c).all (natOpStoredOk env2) &&
  env2.find? eqName == some eqA &&
  (match env2.find? boolTrueName with
    | some ci => ci.toConstantVal.type == .const boolName []
    | none => false) &&
  (match env2.find? boolFalseName with
    | some ci => ci.toConstantVal.type == .const boolName []
    | none => false)

/-- All certificates' syntactic guards at once, over the evidence's proof
terms, one per statement of `divModCertStmts`. -/
def divModCertsGuard (proofs : List (Expr md)) (env : Env md) (c : Key md)
    (annVal : Expr md) : Bool :=
  ((divModCertStmts c).zip proofs).all
    (fun p => divModCertGuard env c annVal p.1.1 p.1.2 p.2)

/-- What a certificate check failed on, for the decline message.  The
pure instantiations always report the `none` text (see
`CheckerOps.orElse`); the executable reports the error. -/
def divModEvidenceReason (c : Key md) : Option (CheckError md) → Msg md
  | none => msg!"unsupported Nat.div/mod evidence ({c}: a certificate did not check)"
  | some e => msg!"unsupported Nat.div/mod evidence ({c}: {e})"

/-- **The well-founded operations' install gate**, run after the ordinary
definition check (`env2` is the already-extended environment, `env`
the pre-insertion one all checks run in): the dependency and pinned-`Eq`
guards, then the operation's evidence from the role table (`ev`): one
`.proof` entry per certificate statement (`evidenceProofs`), whose proofs
pass the syntactic guards and the closure condition (`evidenceLocal`: the
proofs reach only the operation's dependency closure), and whose
certificates check (`checkDivModCerts`).  Anything else is a decline (exit
2), never a silent accept; the operation's literal fast path is enabled
exactly when its certificates checked in this run.

**The evidence is a parameter**: every function from here up to the fold
takes it, and soundness holds at every value — the model consumes the
certificate runs, not where the proofs came from
(`IxC/Kernel/Model/DivModCert.lean`).  A certificate that is ill-typed
against this stream throws inside the check; `CheckerOps.orElse` turns
that into this decline, as it does a `false`. -/
def checkDivModEvidence (ops : (CheckerOps md) m) (ev : Evidences md)
    (env env2 : Env md) (c : Key md) : m Unit := do
  if divModEnvGuard env2 c then
    match env2.find? c with
    | some (.defnInfo _ value' _) =>
      match evidenceProofs ev c with
      | some proofs =>
        if divModCertsGuard proofs env c value' && evidenceLocal env.find? c value' proofs then
          ops.orElse (checkDivModCerts ops env c value' (divModCertStmts c) proofs) fun r =>
            throw (.notImplemented (divModEvidenceReason c r))
        else throw (.notImplemented msg!"unsupported Nat.div/mod evidence ({c}: certificate \
          ground constants absent or outside the dependency closure)")
      | none => throw (.notImplemented msg!"unsupported Nat.div/mod evidence ({c}: no proof \
          evidence, one per certificate statement)")
    | _ => throw (.internal msg!"Nat.div/mod operation not stored ({c})")
  else throw (.notImplemented
    msg!"unsupported Nat.div/mod environment ({c})")

/-- **The `Lean.reduceNat`/`Lean.reduceBool` install gate** (their
specification is `identity`), run after the ordinary opaque check (`env2`
is the already-extended environment, `env` the pre-insertion one the
certificate runs in; `value` the declaration's raw witness value,
annotated again here — the stored constant is an `axiomInfo`, which
carries no value):

* the stored constant must carry the pinned type, over the element
  inductive's pinned shape;
* the *identity certificate*: `value x ≡ x` over an opened `fvar` at
  the element type.  This is what the model consumes
  (`EnvModel.reduce_ops`): with the operation interpreted as the
  identity, the `ofReduce*` axioms' types are trivially inhabited.

There is no comparison with a toolchain's defining expression any more
(the pin `fun b => b` and `checkReducePin` are retired): the certificate
is the specification, and a value that is not the identity declines. -/
def checkReduceIdentity (ops : (CheckerOps md) m) (env env2 : Env md) (c : Key md)
    (value : Expr md) : m Unit := do
  if reduceStoredOk env2 c && reduceElemOk env c then do
    let valA ← ops.annotate env 0 value
    let x := reduceCertVar c
    let ok ← ops.isDefEq env 1 (.app valA x) x
    if ok then pure ()
    else throw (.notImplemented
      msg!"unsupported compiler-trust opaque ({c}: the value is not the identity)")
  else throw (.notImplemented
    msg!"unsupported compiler-trust opaque declaration ({c})")

/-- **Install the pinned (pre-annotated) basis block.**  The three
records that install one — the fold's own `basisDecl` kind, a stream
block `basisPinHit` recognises and a quotient record `quotPinHit`
recognises — share this body, so what is proved of one is proved of
all three.  The quotient block's types mention the pinned equality
former. -/
def checkBasisDecl (env : Env md) (kind : BasisKind) : m (Env md) := do
  if kind = .quotK then
    unless env.find? eqName = some eqA do
      throw (.notImplemented "quotient basis requires the pinned Eq basis")
  kind.declsA.foldlM installBasisDecl env

/-- Check a single declaration, extending the environment on success. -/
def checkDecl (ops : (CheckerOps md) m) (ev : Evidences md) (env : Env md)
    (d : Declaration md) : m (Env md) := do
  match d with
  | .defnDecl cv value hint => do
    let cv ← checkConstantVal ops env cv
    let env2 ← checkDefnVal ops env cv value hint
    -- Structural-Nat operations: their evidence is one `.defeq` entry
    -- per recurrence equation (`evidenceDefeqOk`, the role table's
    -- evidence for an `ops` specification's unconditional equations), and
    -- the fast-path ops must be the standard
    -- structural recursions — their recurrence equations are checked
    -- by definitional equality here, once, so the literal fast path's
    -- reduction-time certification never fails on an accepted
    -- environment.  A nonstandard definition under one of these names
    -- is positively unsupported.  The equations are certified in the
    -- *pre-insertion* environment with the operation's self-references
    -- replaced by its stored value (see `IxC/Kernel/Core.lean`:
    -- certifying after insertion would let the operation's own fast
    -- path discharge its all-literal equations vacuously), and the
    -- operation's and its dependencies' stored types are pinned.
    if natOpNames.contains cv.name then
      unless evidenceDefeqOk ev cv.name do
        throw (.notImplemented
          msg!"unsupported structural Nat operation evidence ({cv.name})")
      unless natOpGuard env2 cv.name &&
          (natOpDeps cv.name).all (natOpStoredOk env2) do
        throw (.notImplemented
          msg!"nonstandard structural Nat operation environment ({cv.name})")
      match env2.find? cv.name with
      | some (.defnInfo _ value' _) =>
        let ok ← certifyNatEqs ops env
          ((natOpEquations 0 cv.name).map fun eq =>
            (Expr.substConst0 cv.name value' eq.1,
             Expr.substConst0 cv.name value' eq.2))
        unless ok do
          throw (.notImplemented
            msg!"nonstandard structural Nat operation ({cv.name})")
      | _ => throw (.internal msg!"structural Nat operation not stored ({cv.name})")
    -- Well-founded `Nat` operations (`Nat.div`, `Nat.mod`, …): their
    -- evidence is one `.proof` entry per certificate statement of their
    -- `ops` specification, and the proofs' `Nat.ble`-guarded
    -- characterization certificates must check (in the pre-insertion
    -- environment, self-references substituted; see `checkDivModCerts`)
    -- — they are not installed; their success is what the model side
    -- consumes for the literal fast path.  Missing or failing evidence is
    -- a decline (exit 2), never a silent accept.
    if natDivModNames.contains cv.name then
      checkDivModEvidence ops ev env env2 cv.name
    pure env2
  | .thmDecl cv value =>
    let cv ← checkConstantVal ops env cv
    checkThmVal ops env cv value
  | .opaqueDecl cv value => do
    let cv ← checkConstantVal ops env cv
    let env2 ← checkOpaqueVal ops env cv value
    -- Compiler-trust opaques (`Lean.reduceNat`/`Lean.reduceBool`,
    -- task #95): their specification is `identity`, so the stored value
    -- is certified to be the identity function — the gate that lets the
    -- `ofReduce*` axioms' identity certificates never fail on an
    -- accepted environment.
    if reduceOpNames.contains cv.name then
      checkReduceIdentity ops env env2 cv.name value
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
    -- `IxC/Kernel/Core.lean`, and `unresolvedConstsError`,
    -- `IxC/Kernel/CheckerBase.lean`).  Any other axiom
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
    -- a parser check (`IxC/Kernel/Frontend/ExportC.lean`), which
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
          msg!"unsupported Lean.trustCompiler shape ({cv.name})")
      else if cvA.name = ofReduceNatName ∨ cvA.name = ofReduceBoolName then
        -- The pinned `ofReduce*` axioms (task #95): over the pinned
        -- `Eq` basis, the element inductive and the identity-certified
        -- reduce opaque, `∀ a b, reduce a = b → a = b` interprets to an
        -- inhabited proposition (the hypothesis *is* the conclusion).
        if ofReduceAxOk env cvA then
          pure ⟨.axiomInfo cvA :: env.consts⟩
        else throw (.notImplemented
          msg!"unsupported compiler-trust axiom environment ({cv.name})")
      else if cvA.name = propextName ∨ cvA.name = choiceName then
        throw (.notImplemented msg!"standard axiom shape mismatch ({cv.name})")
      else if cvA.name = sorryAxName then
        pure env
      else
        throw (.notImplemented msg!"non-standard axiom ({cv.name})")
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
      -- (`IxC/Kernel/Frontend/InModel.lean`), whose records precede the
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
def checkDeclsPure (ops : (CheckerOps md) m) (ev : Evidences md)
    (ds : List (Declaration md)) : m (Env md) :=
  ds.foldlM (checkDecl mode ops ev) Env.empty

end Ix.Kernel
