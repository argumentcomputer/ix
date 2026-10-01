module

public import ConLeche.Cached.CheckerC

@[expose] public section

/-!
# The parsed-declaration driver on the cached representation

One `CState` for the whole stream, the environment-dependent caches
flushed per declaration, declarations consumed as `Declaration` records
straight from the direct parse (`ConLeche/Frontend/ExportC.lean`, task
#171 — no conversion detour).

`checkDeclStepC` is the fold's step for every declaration kind that is
checked as it is installed: axioms, inductive and basis blocks, the
pinned `Nat`-operation and `reduce*` declarations — and, on this step,
a definition, theorem or opaque too.  The declaration fold itself,
`checkDecls` (`ConLeche/Cached/Installed.lean`), installs every record
first (a separable value declaration by the install half of this
step, annotated and pushed with its check recorded; everything else by
this step) and checks the recorded declarations afterwards; the
binary's driver (`Main.lean`) runs that fold with a heartbeat between
the steps and returns its environment together with the proof that
`checkDecls` returns it.  The fold runs at `.verified` and at
`.trusted` alike (the twin driver `checkDeclsT` /
`ConLeche/Cached/ParsedT.lean` retired 2026-09-06; the trusted lane is
the same fold at the other mode, and nothing else): acceptance at
`.verified` is covered by the main corollary
`no_False_declaration` (`ConLeche/MainTheorem.lean`, through
`no_False_theorem_accepted` in `ConLeche/Verify/Cached/StreamThm.lean`), and the two
modes agree on the install skeletons whenever both accept
(`trusted_agrees_skels_D`, `ConLeche/Verify/Cached/AgreeFloor.lean`).

The driver's parameter is the `CheckMode` itself (task #185; from
2026-09-06 to then a configuration record stood in for it): the knot it
ties (`coreKnotI mode`) and the install-time stages
(`checkIotaRulesF`, `checkProjIotaF`, `indBlockCapsF`,
`ctorResidualOkF` — each reads only the uninhabited-true `ttChecks`)
all take the same mode.
-/

namespace ConLeche.Cached

open ConLeche

/-! ## The parsed-declaration checker -/

variable (mode : CheckMode)

/-- Parsed `ensureSort` (no per-call conversion). -/
def opSIxC (fe : FEnv) (d : Nat) (i : Expr) : CheckCM Level :=
  ensureSortI (coreKnotI mode fe checkFuel) d i

/-- `checkConstantVal` on a parsed declaration: the checks of
`checkConstantValF` with the syntactic passes memoized on the `Expr`
DAG and the cached operations on its nodes. -/
def checkConstantValC (fe : FEnv) (cv : ConstantVal) :
    CheckCM (ConstantVal × Expr) := do
  if (fe.find? cv.name).isSome then
    throw (.invalid s!"duplicate declaration {cv.name}")
  if reservedBasisNames.contains cv.name then
    throw (.invalid s!"reserved basis name {cv.name}")
  if cv.name.isProjFnShape then
    throw (.invalid s!"reserved projection name {cv.name}")
  unless Name.nodup cv.levelParams do
    throw (.invalid s!"duplicate universe parameters in {cv.name}")
  unless Expr.looseBVarsBounded 0 cv.type do
    throw (.invalid s!"loose bound variable in type of {cv.name}")
  if Expr.hasFvar cv.type then
    throw (.invalid s!"unexpected free variable in type of {cv.name}")
  let jty ← (coreKnotI mode fe checkFuel).annotate 0 cv.type
  unless Expr.allLevelParamsDefinedC cv.levelParams jty do
    throw (.invalid s!"undeclared universe parameter in type of {cv.name}")
  unless constsResolveFC fe jty do
    throw (unresolvedConstsError s!"type of {cv.name}" jty)
  let jsty ← (coreKnotI mode fe checkFuel).infer 0 jty
  let _u ← opSIxC mode fe 0 jsty
  let tyE := jty
  pure (⟨cv.name, cv.levelParams, tyE⟩, jty)

/-- `checkDefnValP` over `Expr`. -/
def checkDefnValC (fe : FEnv) (cvA : ConstantVal) (jty : Expr)
    (value : Expr) (hint : ReducibilityHint) : CheckCM FEnv := do
  unless Expr.looseBVarsBounded 0 value do
    throw (.invalid s!"loose bound variable in value of {cvA.name}")
  if value.hasFvar then
    throw (.invalid s!"unexpected free variable in value of {cvA.name}")
  let jv ← (coreKnotI mode fe checkFuel).annotate 0 value
  unless Expr.allLevelParamsDefinedC cvA.levelParams jv do
    throw (.invalid s!"undeclared universe parameter in value of {cvA.name}")
  unless constsResolveFC fe jv do
    throw (unresolvedConstsError s!"value of {cvA.name}" jv)
  let vE := jv
  recordCConst cvA.name cvA.type jty (some (vE, jv))
  let jvt ← (coreKnotI mode fe checkFuel).infer 0 jv
  unless ← (coreKnotI mode fe checkFuel).defeq 0 jvt jty do
    throw (.invalid s!"type mismatch in definition {cvA.name}")
  pure (fe.push (.defnInfo cvA vE hint))

/-- `checkThmValP` over `Expr`. -/
def checkThmValC (fe : FEnv) (cvA : ConstantVal) (jty : Expr)
    (value : Expr) : CheckCM FEnv := do
  let jsty ← (coreKnotI mode fe checkFuel).infer 0 jty
  let ul ← opSIxC mode fe 0 jsty
  unless (← liftFueled "level comparison" (Level.isEquiv ul .zero)) do
    throw (.invalid s!"type of theorem {cvA.name} is not a proposition")
  unless Expr.looseBVarsBounded 0 value do
    throw (.invalid s!"loose bound variable in value of {cvA.name}")
  if value.hasFvar then
    throw (.invalid s!"unexpected free variable in value of {cvA.name}")
  let jv ← (coreKnotI mode fe checkFuel).annotate 0 value
  unless Expr.allLevelParamsDefinedC cvA.levelParams jv do
    throw (.invalid s!"undeclared universe parameter in value of {cvA.name}")
  unless constsResolveFC fe jv do
    throw (unresolvedConstsError s!"value of {cvA.name}" jv)
  recordCConst cvA.name cvA.type jty none
  let jvt ← (coreKnotI mode fe checkFuel).infer 0 jv
  unless ← (coreKnotI mode fe checkFuel).defeq 0 jvt jty do
    throw (.invalid s!"type mismatch in theorem {cvA.name}")
  -- stored by statement: the record's own value, unread (opaque)
  pure (fe.push (.thmInfo cvA value))

/-- `checkOpaqueValP` over `Expr`. -/
def checkOpaqueValC (fe : FEnv) (cvA : ConstantVal) (jty : Expr)
    (value : Expr) : CheckCM FEnv := do
  unless Expr.looseBVarsBounded 0 value do
    throw (.invalid s!"loose bound variable in value of {cvA.name}")
  if value.hasFvar then
    throw (.invalid s!"unexpected free variable in value of {cvA.name}")
  let jv ← (coreKnotI mode fe checkFuel).annotate 0 value
  unless Expr.allLevelParamsDefinedC cvA.levelParams jv do
    throw (.invalid s!"undeclared universe parameter in value of {cvA.name}")
  unless constsResolveFC fe jv do
    throw (unresolvedConstsError s!"value of {cvA.name}" jv)
  recordCConst cvA.name cvA.type jty none
  let jvt ← (coreKnotI mode fe checkFuel).infer 0 jv
  unless ← (coreKnotI mode fe checkFuel).defeq 0 jvt jty do
    throw (.invalid s!"type mismatch in opaque {cvA.name}")
  pure (fe.push (.axiomInfo cvA))

/-- `checkBasisDecl`'s cached twin: the body the three records that
install a pinned basis block share (task #293). -/
def checkBasisDeclC (fe : FEnv) (kind : BasisKind) : CheckCM FEnv := do
  if kind = .quotK then
    unless fe.find? eqName = some eqA do
      throw (.notImplemented "quotient basis requires the pinned Eq basis")
  kind.declsA.foldlM installBasisDeclF fe

/-- One converted declaration (mirrors `checkDeclSPPlain` branch by
branch; inductive and basis blocks reuse the `Expr`-level drivers).
`pins` is the `Nat.div`/`Nat.mod` pin-variant list the install gate
tries (task #304), threaded from the fold. -/
def checkDeclC (pins : List NatOpPinSet) (fe : FEnv) (pd : Declaration) :
    CheckCM FEnv :=
  match pd with
  | .defnDecl cv value hint => do
    let (cvA, jty) ← checkConstantValC mode fe cv
    if natOpNames.contains cvA.name || natDivModNames.contains cvA.name then
      let fe2 ← checkDefnValC mode fe cvA jty value hint
      if natOpNames.contains cvA.name then
        unless natOpGuardF fe2 cvA.name &&
            (natOpDeps cvA.name).all (natOpStoredOkF fe2) do
          throw (.notImplemented
            s!"nonstandard structural Nat operation environment ({cvA.name})")
        match fe2.find? cvA.name with
        | some (.defnInfo _ value' _) =>
          let ok ← certifyNatEqs (sharedOpsC mode fe) fe.env
            ((natOpEquations 0 cvA.name).map fun eq =>
              (Expr.substConst0 cvA.name value' eq.1,
               Expr.substConst0 cvA.name value' eq.2))
          unless ok do
            throw (.notImplemented
              s!"nonstandard structural Nat operation ({cvA.name})")
        | _ => throw (.internal
            s!"structural Nat operation not stored ({cvA.name})")
      if natDivModNames.contains cvA.name then
        checkDivModPinF (sharedOpsC mode fe) pins fe fe2 cvA.name
      pure fe2
    else
      checkDefnValC mode fe cvA jty value hint
  | .thmDecl cv value => do
    let (cvA, jty) ← checkConstantValC mode fe cv
    checkThmValC mode fe cvA jty value
  | .opaqueDecl cv value => do
    let (cvA, jty) ← checkConstantValC mode fe cv
    -- RC linearity (cf. the parser-state rule): with `fe` still live
    -- after the push — the `reduceOpNames` branch reads it —
    -- `checkOpaqueValC`'s `fe.push` copied the whole index on EVERY
    -- opaque install.  Branch first, so the common arm hands `fe` to
    -- the push unshared.
    if reduceOpNames.contains cvA.name then do
      let fe2 ← checkOpaqueValC mode fe cvA jty value
      checkReducePinF (sharedOpsC mode fe) fe fe2 cvA.name value
      pure fe2
    else
      checkOpaqueValC mode fe cvA jty value
  | .axiomDecl cv =>
    -- `checkDecl`'s twin (task #293): `Quot.sound` is the pinned
    -- quotient block's own record — compared with the pin, installing
    -- nothing, declining on a mismatch.
    if cv.name = quotSoundName then
      (if ConstantInfo.canonEq (.axiomInfo cv) (quotBasis.getD 4 (.axiomInfo default)) then
        pure fe
      else
        throw (.notImplemented "quotient soundness axiom mismatch"))
    else do
      let (cvA, jty) ← checkConstantValC mode fe cv
      if stdAxiomOkF fe cvA then do
        recordCConst cvA.name cvA.type jty none
        pure (fe.push (.axiomInfo cvA))
      else if cvA.name = trustCompilerName then
        if trustCompilerOkF fe cvA then do
          recordCConst cvA.name cvA.type jty none
          pure (fe.push (.axiomInfo cvA))
        else throw (.notImplemented
          s!"unsupported Lean.trustCompiler shape ({cv.name})")
      else if cvA.name = ofReduceNatName ∨ cvA.name = ofReduceBoolName then
        if ofReduceAxOkF fe cvA then do
          recordCConst cvA.name cvA.type jty none
          pure (fe.push (.axiomInfo cvA))
        else throw (.notImplemented
          s!"unsupported compiler-trust axiom environment ({cv.name})")
      else if cvA.name = propextName ∨ cvA.name = choiceName then
        throw (.notImplemented s!"standard axiom shape mismatch ({cv.name})")
      else if cvA.name = sorryAxName then
        pure fe
      else
        throw (.notImplemented s!"non-standard axiom ({cv.name})")
  | .basisDecl kind => checkBasisDeclC fe kind
  | .indDecl block nP =>
    -- **THE PINNED BASIS BLOCKS** (`checkDecl`'s twin, task #293): the
    -- stream's own `Nat` block, recognised here and installed as the
    -- pin; a block under a pinned name that does not match falls
    -- through and the reserved-name check rejects it.
    match basisPinHit block with
    | some kind => checkBasisDeclC fe kind
    | none =>
    -- TASK #228: the stream's DECLARED parameter count, checked before
    -- the dispatch and for both routes (`checkDecl`'s twin).
    if indParamsOk nP block then
      -- ONE ROUTE (task #210), dispatched by the RECOGNISER alone (task
      -- #219): a recognised block is the fixpoint route's, every other
      -- one the modeled path's (its model the in-process modeller's).
      match nativeParts? nP block with
      | some p => checkNativeS mode fe p
      | none => checkIndDeclSF mode fe block
    else throw (.invalid "number of parameters mismatch")
  | .quotDecl k cv =>
    -- `checkDecl`'s twin (task #293): the `type` record installs the
    -- pinned block whole, the other members install nothing, and a
    -- record that does not match its pin is a positive decline.
    if quotPinHit k cv then
      (match k with
       | .type => checkBasisDeclC fe .quotK
       | _ => pure fe)
    else throw (.notImplemented (match k with
      | .sound => "quotient soundness axiom mismatch"
      | _ => "quotient declaration mismatch"))

/-! ## Names and durations for the driver's messages -/

/-- Milliseconds as `s.d` seconds (`12345` ↦ `"12.3"`).  `Nat`
arithmetic — no `Float` formatting on a message path. -/
def msSecs (ms : Nat) : String := s!"{ms / 1000}.{(ms % 1000) / 100}"

/-- A parsed declaration's display label (`Main.declCName`, shared with
the driver's progress callback so the two can never drift). -/
def declCLabel : Declaration → String
  | .defnDecl cv _ _ => s!"def {cv.name}"
  | .thmDecl cv _ => s!"theorem {cv.name}"
  | .opaqueDecl cv _ => s!"opaque {cv.name}"
  | .axiomDecl cv => s!"axiom {cv.name}"
  | .indDecl b _ => s!"inductive {(b.head?.map (·.name)).getD .anonymous}"
  | .basisDecl k => s!"basis block {repr k}"
  | .quotDecl _ cv => s!"quot {cv.name}"

/-- One step of the converted-declaration fold: flush, then check. -/
def checkDeclStepC (pins : List NatOpPinSet) (fe : FEnv) (pd : Declaration) :
    CheckCM FEnv := do
  flushC
  checkDeclC mode pins fe pd

end ConLeche.Cached
