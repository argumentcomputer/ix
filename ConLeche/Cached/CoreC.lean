module

public import ConLeche.Cached.StateC

@[expose] public section

/-!
# The cached checker core

The core over the computed-field representation: `whnfCore`, `whnf`,
`infer`, `defeq` and `annotate`, each memoized in `CState`.  Task #198
removed the last of the deleted arena's shape from these bodies — the
`CStore` no-ops and the `withStore` reads that ran queries against
them; a syntactic read is now the operation itself.

See DESIGN.md, "The cached checker".

**One body, two modes (2026-09-06, `agent/coret-retire`; the mode is
the only parameter since task #185).**  Every body below is a template
over `mode : CheckMode`, and the knot at the end (`coreKnotI mode`)
ties them at a mode.  The verified core is this knot at `.verified`;
the trusted core is this same knot at `.trusted` — there is no second
implementation.  The hand-written cert-skipping twin
(`ConLeche/Cached/CoreT.lean`, retired with this batch) is gone: what
the trusted mode omits is exactly what `mode.verifiedChecks` gates
here (group A: the annotation validations, the λ-codomain sort check,
the projection certificate) plus what `mode.certs` gates (the
certificate families: every `certAtI` / `certUnlessI` site and the
`betaSkip` / `ioSkip` reads), and nothing else (DESIGN.md, "CORET
RETIRED").  Every read is a `match` on the two-constructor enum
(`ConLeche/Kernel/Env.lean`), so at either literal mode it reduces by
`rfl` and the branch is gone, not collapsed.
-/

namespace ConLeche.Cached

open ConLeche

variable {m : Type → Type}

/-! ## The core record and its helper twins -/

/-- The record of mutually recursive cached entry points. -/
structure CoreFnsI where
  whnfCore : Nat → Expr → CheckCM Expr
  whnf : Nat → Expr → CheckCM Expr
  infer : Nat → Expr → CheckCM Expr
  defeq : Nat → Expr → Expr → CheckCM Bool
  annotate : Nat → Expr → CheckCM Expr
  /-- Type inference at the **infer-only grade** (task #170 / #172 B4)
  — the twin of `CoreFns.inferIO` (`ConLeche/Kernel/Core.lean`): what
  every internal inference call site runs.  The knot selects the
  grade's meaning per mode (`mode.ioGate`): the io body (own memo,
  `CState.inferIOC`) at **both modes** since the licence ruling of
  2026-09-06 — the io skip is a licence, not certification-only work
  — and the full `infer` only at `ioGate = false`, which no mode
  spells any more (the retired R core). -/
  inferIO : Nat → Expr → CheckCM Expr

/-- The io-grade view (twin of `CoreFns.ioView`): the record whose
full-grade `infer` slot is the io slot, so a body written against
`r.infer` recurses at the io grade when handed `r.ioView`. -/
def CoreFnsI.ioView (r : CoreFnsI) : CoreFnsI :=
  { r with infer := r.inferIO }

/-- Twin of `unfoldDefinition` (monadic: the unfolded value is read
through the `(name, levels)` cache).  Like the spec, a theorem never
unfolds. -/
def unfoldDefinitionI (fe : FEnv) (e : Expr) : CheckCM (Option Expr) := do
  match Expr.getAppFn e with
  | .const n us => do
    let nm ← pure n
    match fe.find? nm with
    | some (.defnInfo cv _ _) =>
      if us.length = cv.levelParams.length then do
        let v ← constValAtM fe n nm us
        let args ← pure (Expr.getAppArgsC e)
        let r ← mkAppNM v args
        pure (some r)
      else pure none
    | _ => pure none
  | _ => pure none

/-- Twin of `litToCtorIfNat`. -/
def litToCtorIfNatI (fe : FEnv) (e : Expr) : CheckCM Expr := do
  match e with
  | .lit (.natVal n) =>
    if natLitSupportedF fe then pure (natLitToConstructor n)
    else pure e
  | _ => pure e

/-- Twin of `reduceNat`. -/
def reduceNatI (r : CoreFnsI) (fe : FEnv) (depth : Nat) (e : Expr) :
    CheckCM (Option Expr) := do
  match e with
  | .app f₁ b =>
    match f₁ with
    | .const c us =>
      match us with
      | _ :: _ => pure none
      | [] => do
        let cn ← pure c
        if cn = natSuccName ∧ natLitSupportedF fe then do
          let w ← r.whnf depth b
          match ← pure (rawNatLitC? w) with
          | some n => do
            let r ← pure (Expr.lit (.natVal (n + 1)))
            pure (some r)
          | none => pure none
        else pure none
    | .app f₂ a =>
      match f₂ with
      | .const c us =>
        match us with
        | _ :: _ => pure none
        | [] => do
          let cn ← pure c
          if (cn = natAddName ∨ cn = natSubName ∨ cn = natMulName ∨
              cn = natPowName ∨ cn = natBeqName ∨ cn = natBleName ∨
              cn = natDivName ∨ cn = natModName ∨ cn = natGcdName ∨
              cn = natLandName ∨ cn = natLorName ∨ cn = natXorName ∨
              cn = natShiftLeftName ∨ cn = natShiftRightName) ∧
              natOpStoredF fe cn = true then do
            -- first argument first; the second only behind a literal
            -- (official `reduce_bin_nat_op`; the spec's D15 note)
            let w₁ ← r.whnf depth a
            match ← pure (rawNatLitC? w₁) with
            | some n₁ => do
              let w₂ ← r.whnf depth b
              match ← pure (rawNatLitC? w₂) with
              | some n₂ =>
                match natOpResult cn n₁ n₂ with
                | some x => do
                  let r ← pure x
                  pure (some r)
                | none => pure none
              | none => pure none
            | none => pure none
          else if natOpWfNames.contains cn ∧ natLitSupportedF fe then do
            let w₁ ← r.whnf depth a
            match ← pure (rawNatLitC? w₁) with
            | some _ => do
              let w₂ ← r.whnf depth b
              match ← pure (rawNatLitC? w₂) with
              | some _ => throw (.notImplemented
                  s!"native Nat computation on literals ({cn})")
              | none => pure none
            | none => pure none
          else pure none
      | _ => pure none
    | _ => pure none
  | _ => pure none

/-- Twin of `iotaCerts`, bulk form (task #50): peel the raw telescope
while accumulating the certified arguments, substituting only each
binder's *domain* (small) instead of copying the whole residual
telescope per argument.  A raw `bvar` body (whose substitution could
expose further `∀`-binders — the fold semantics) substitutes the
accumulator and re-enters.

`lic` is the ι-slot licence (the spec's docstring): at a licensed walk
a `.never` binder's slot is skipped outright — no domain instantiation,
no inference, no defeq — and the binder's argument joins the
accumulator as if certified.  The datum read is the level-instantiated
one (the telescope was instantiated at the recursor's levels by
`constTyAtM`), which is where `Nat.rec.{u}`'s `.ifAllZero [u]` major
binder becomes `.never` at `u := succ _`. -/
def iotaCertsIAux (r : CoreFnsI) (fe : FEnv) (depth : Nat) (lic : Bool) :
    Expr → List Expr → List Expr → CheckCM Bool
  | _, _, [] => pure true
  | ty, acc, arg :: rest => do
    match ty with
    | .forallE dom body mb =>
      if lic && mb.pw.isNever then
        iotaCertsIAux r fe depth lic body (arg :: acc) rest
      else do
        let dom' ← instListM dom acc
        let ta ← r.inferIO depth arg
        if ← r.defeq depth ta dom' then
          iotaCertsIAux r fe depth lic body (arg :: acc) rest
        else pure false
    | .bvar _ =>
      match acc with
      | [] => pure false
      | _ :: _ => do
        let ty' ← instListM ty acc
        iotaCertsIAux r fe depth lic ty' [] (arg :: rest)
    | _ => pure false
termination_by _ acc args => (args.length, acc.length)
decreasing_by
  · apply Prod.Lex.left; simp
  · apply Prod.Lex.left; simp
  · apply Prod.Lex.right' <;> simp

/-- Twin of `iotaCerts` (certify a spine against a recursor telescope);
the bulk-instantiating accumulator loop at the empty accumulator. -/
def iotaCertsI (r : CoreFnsI) (fe : FEnv) (depth : Nat) (lic : Bool)
    (ty : Expr) (args : List Expr) : CheckCM Bool :=
  iotaCertsIAux r fe depth lic ty [] args

/-- Twin of `defEqList`. -/
def defEqListI (r : CoreFnsI) (fe : FEnv) (depth : Nat) :
    List Expr → List Expr → CheckCM Bool
  | [], [] => pure true
  | a :: as, b :: bs => do
    if ← r.defeq depth a b then
      defEqListI r fe depth as bs
    else pure false
  | _, _ => pure false

/-- Twin of `iotaIndexOk` (the canonical-index comparison, only where
the recursor has indices). -/
def iotaIndexOkI (r : CoreFnsI) (fe : FEnv) (depth : Nat) (mI rP cnP : Nat)
    (tyCtor : Expr) (margs idx : List Expr) : CheckCM Bool :=
  if mI = rP then pure true
  else do
    match ← piResidualM tyCtor margs with
    | some residual => do
      let resArgs ← pure (Expr.getAppArgsC residual)
      defEqListI r fe depth (resArgs.drop cnP) idx
    | none => pure false

/-- Twin of `defeqSpine`. -/
def defeqSpineI (r : CoreFnsI) (fe : FEnv) (depth : Nat) (a b : Expr) :
    CheckCM Bool := do
  match Expr.getAppFn a with
  | .const n us =>
    match Expr.getAppFn b with
    | .const n' us' => do
      let aargs ← pure (Expr.getAppArgsC a)
      let bargs ← pure (Expr.getAppArgsC b)
      if n = n' ∧ aargs.length = bargs.length then
        match ← isEquivListLM us us' with
        | some true => defEqListI r fe depth aargs bargs
        | _ => pure false
      else pure false
    | _ => pure false
  | _ => pure false

/-- Twin of `proofIrrel`. -/
def proofIrrelI (r : CoreFnsI) (fe : FEnv) (depth : Nat) (a b : Expr) :
    CheckCM Bool := do
  let ta ← r.inferIO depth a
  let wta ← r.whnf depth ta
  if ← pure (isUnitLikeTyC fe wta) then do
    let tb ← r.inferIO depth b
    let wtb ← r.whnf depth tb
    if ← pure (isUnitLikeTyC fe wtb) then
      pure true
    else
      pure false
  else do
    let tta ← r.inferIO depth ta
    let wtta ← r.whnf depth tta
    match wtta with
    | .sort uT => do
      let z ← pure .zero
      let okA ← liftFueled "level comparison" (← isEquivLM uT z)
      let tb ← r.inferIO depth b
      let ttb ← r.inferIO depth tb
      let wttb ← r.whnf depth ttb
      match wttb with
      | .sort vT => do
        let z ← pure .zero
        let okB ← liftFueled "level comparison" (← isEquivLM vT z)
        pure (okA && okB)
      | _ => pure false
    | _ => pure false

/- Task #172 batch B2 — **THE BODY TEMPLATE'S PARAMETER** (the mode
itself since task #185).  Every configured body below takes
`mode : CheckMode` and is instantiated at the two named concrete cores
at the end of this module (`…PC` at `.verified`, `…TC` at `.trusted`;
the `…RC` half retired with the R core, 2026-09-05).  Every read below
is one of the `CheckMode` functions of `ConLeche/Kernel/Env.lean`, each
a `match` on the enum.  The ι cone (`structEtaCertWithI` →
`majorToCtorI` → `prepareMajorI` → `iotaRecI`) reads its ι-slot
licence off `mode.betaGate` — the same function the β site reads —
and keeps only the TT-lane residue on `mode.ttChecks`, a literal
`false` at each mode. -/
variable (mode : CheckMode)

/-! ### The certificate-family switch (the twin's retirement, 2026-09-06)

`CheckMode.certs` (`ConLeche/Kernel/Env.lean`) is the task-#76 skip
list as a mode function: the certificate families the reference
kernel does not run and only the soundness proof consumes.  Every such
certificate below is spelled through one of the two wrappers here, so
the list of `certAtI`/`certUnlessI` sites — plus the `betaSkip` and
`ioSkip` reads — **is** the list of what the trusted core omits beyond
group A.  At `.verified` the function is `true`, so `certAtI .verified
c` is `c` by `rfl` (`certAtI_verified`); the simulation tower
(`ConLeche/Verify/Cached/*`), stated under `hμ : mode.verifiedChecks =
true`, sees through the wrapper by `certAtI_of_verifiedChecks` — the
spec bodies carry no such wrapper. -/

/-- Run the certificate `c` when the mode runs the certificate
families; otherwise it is `true` without running. -/
@[inline] def certAtI (mode : CheckMode) (c : CheckCM Bool) : CheckCM Bool :=
  if mode.certs then c else pure true

/-- `certAtI` with a *verdict-relevant* exception: `keep = true` runs
the check at every mode (the twin's judgement at ι's parameter
comparison — nested-rule comparands and projection-function rules
compare in both modes, ordinary plain rules only when certifying). -/
@[inline] def certUnlessI (mode : CheckMode) (keep : Bool) (c : CheckCM Bool) :
    CheckCM Bool :=
  if mode.certs || keep then c else pure true

/-- At a mode running the certificate families the wrapper is the
certificate — the simulation tower's blindness to the switch, under
its `hμ`. -/
@[simp] theorem certAtI_of_verifiedChecks {mode : CheckMode}
    (hμ : mode.verifiedChecks = true) (c : CheckCM Bool) :
    certAtI mode c = c := by
  cases mode <;> simp_all [certAtI, CheckMode.certs, CheckMode.verifiedChecks]
@[simp] theorem certUnlessI_of_verifiedChecks {mode : CheckMode}
    (hμ : mode.verifiedChecks = true) (keep : Bool) (c : CheckCM Bool) :
    certUnlessI mode keep c = c := by
  cases mode <;> simp_all [certUnlessI, CheckMode.certs, CheckMode.verifiedChecks]
/-- … and at the two modes the wrapper is the certificate or the
constant `true`, by `rfl`. -/
@[simp] theorem certAtI_verified (c : CheckCM Bool) :
    certAtI .verified c = c := rfl
@[simp] theorem certAtI_trusted (c : CheckCM Bool) :
    certAtI .trusted c = pure true := rfl

/-- Twin of `propIrrel` (task #168): the hoisted `Prop`-branch test
with both head-symbol arms.  Ungated since 2026-09-06 — the readers
run in both modes, so this body takes no `CheckMode` at all. -/
def propIrrelI (r : CoreFnsI) (fe : FEnv) (depth : Nat) (a b : Expr) :
    CheckCM Bool := do
  if notProofFast fe.find? a || notProofFast fe.find? b then
    pure false
  else if isProofFast fe.find? a && isProofFast fe.find? b then
    pure true
  else
  let ta ← r.inferIO depth a
  let tta ← r.inferIO depth ta
  let wtta ← r.whnf depth tta
  match wtta with
  | .sort uT => do
    let z ← pure .zero
    let okA ← liftFueled "level comparison" (← isEquivLM uT z)
    let tb ← r.inferIO depth b
    let ttb ← r.inferIO depth tb
    let wttb ← r.whnf depth ttb
    match wttb with
    | .sort vT => do
      let z ← pure .zero
      let okB ← liftFueled "level comparison" (← isEquivLM vT z)
      pure (okA && okB)
    | _ => pure false
  | _ => pure false

/-- The projection-application spine
`[proj_0 targs b, …]` (structural recursion; the spec side is a pure
`List.map`). -/
def projAppsFnI (T : Name) (us' : List Level) (targs : List Expr)
    (b : Expr) : List Nat → CheckCM (List Expr)
  | [] => pure []
  | i :: rest => do
    let pf ← pure (projFnName T i)
    let h ← pure (Expr.const pf us')
    let r ← mkAppNM h (targs ++ [b])
    let rs ← projAppsFnI T us' targs b rest
    pure (r :: rs)

/-- The `.proj T i b` spine (the tower spelling, task #175
W4c). -/
def projNodesI (T : Name) (b : Expr) : List Nat → CheckCM (List Expr)
  | [] => pure []
  | i :: rest => do
    let r ← pure (Expr.proj T i b)
    let rs ← projNodesI T b rest
    pure (r :: rs)

/-- Twin of `etaProjs`: the tower spelling at an all-tower slot family
(`towerSlotsAll` through the index), the projection-function spelling
otherwise. -/
def projAppsI (fe : FEnv) (Tn T : Name) (us' : List Level)
    (targs : List Expr) (b : Expr) (nF : Nat) :
    CheckCM (List Expr) :=
  if fe.towerSlotsAllF Tn nF then
    projNodesI T b (List.range nF)
  else projAppsFnI T us' targs b (List.range nF)

/-- Twin of `structEtaProjCerts`. -/
def structEtaProjCertsI (r : CoreFnsI) (fe : FEnv) (depth : Nat)
    (TI : Name) (T : Name) (us' : List Level) (targs : List Expr)
    (b : Expr)
    (lpsT : List Name) : List Nat → CheckCM Bool
  | [] => pure true
  | i :: rest => do
    match fe.find? (projFnName T i) with
    | some (.recInfo cvp _ _ _) =>
      if cvp.levelParams = lpsT ∧
          (cvp.type.stripPis (targs.length + 1)).isSome = true then do
        let pf ← pure (projFnName TI i)
        let pty ← constTyAtM fe pf (projFnName T i) us'
        if ← iotaCertsI r fe depth false pty (targs ++ [b]) then
          structEtaProjCertsI r fe depth TI T us' targs b lpsT rest
        else pure false
      else pure false
    | _ => pure false

/-- Twin of `structEtaCertWith`. -/
def structEtaCertWithI (r : CoreFnsI) (fe : FEnv) (depth : Nat)
    (a b wtb : Expr) : CheckCM Bool := do
  match Expr.getAppFn a with
  | .const c us => do
    let cn ← pure c
    match fe.find? cn with
    | some (.ctorInfo cvc cnP cnF) => do
      let aargs ← pure (Expr.getAppArgsC a)
      if aargs.length = cnP + cnF then
        match Expr.getAppFn wtb with
        | .const T us' => do
          let Tn ← pure T
          match fe.find? Tn with
          | some (.indInfo cvT caps) => do
            let targs ← pure (Expr.getAppArgsC wtb)
            if caps.eta = true ∧ caps.etaCtor = cn ∧
                reservedBasisNames.contains Tn = false ∧
                reservedBasisNames.contains cn = false ∧
                targs.length = caps.etaParams ∧
                us'.length = cvT.levelParams.length ∧
                cvc.levelParams = cvT.levelParams ∧
                (fe.towerSlotsAllF Tn caps.etaFields ||
                  fe.recSlotsAllF Tn caps.etaFields) = true then do
              if ← liftFueled "level comparison"
                  (← isEquivListLM us us') then do
                let tyT ← constTyAtM fe T Tn us'
                -- the type-former telescope certificate and the
                -- per-slot ones are certificate families (official's
                -- `try_eta_struct_core` runs neither); off at `.trusted`
                if ← certAtI mode (iotaCertsI r fe depth false tyT targs) then do
                  -- the per-slot certificates are the projection-function
                  -- kind's; a tabled family has none (task #175 S1)
                  if ← certAtI mode
                      (if fe.towerSlotsAllF Tn caps.etaFields then pure true
                      else structEtaProjCertsI r fe depth T Tn us'
                        targs b cvT.levelParams
                        (List.range caps.etaFields)) then do
                    if ← defEqListI r fe depth
                        (aargs.take caps.etaParams) targs then do
                      let projs ← projAppsI fe Tn T us' targs b caps.etaFields
                      -- synthetic-spine certification (task #137): the
                      -- fabricated constructor application
                      -- `c targs (proj_i … b)` is certified against the
                      -- constructor's own telescope, here rather than at
                      -- the callers, so that BOTH consumers get it —
                      -- `majorToCtorI`'s eta rescue ran it already
                      -- (task #71), `defeq`'s `structEtaCertI` did not.
                      -- TT-lane check (task #147): skipped unless
                      -- `mode.ttChecks`, a literal `false` at
                      -- both shipped cores.
                      if ← (if mode.ttChecks then do
                          let tyCtor ← constTyAtM fe c cn us
                          iotaCertsI r fe depth false tyCtor (targs ++ projs)
                        else pure true) then
                        defEqListI r fe depth (aargs.drop caps.etaParams) projs
                      else pure false
                    else pure false
                  else pure false
                else pure false
              else pure false
            else pure false
          | _ => pure false
        | _ => pure false
      else pure false
    | _ => pure false
  | _ => pure false

/-- Twin of `structEtaCert`. -/
def structEtaCertI (r : CoreFnsI) (fe : FEnv) (depth : Nat) (a b : Expr) :
    CheckCM Bool := do
  -- the constructor-shape gate first (D13), as in the spec
  let sh ← pure (etaCtorShapeC fe a)
  if sh then
    let tb ← r.inferIO depth b
    let wtb ← r.whnf depth tb
    structEtaCertWithI mode r fe depth a b wtb
  else pure false

/-- Twin of `structUnitCert`. -/
def structUnitCertI (r : CoreFnsI) (fe : FEnv) (depth : Nat) (a b : Expr) :
    CheckCM Bool := do
  let ta ← r.inferIO depth a
  let wta ← r.whnf depth ta
  match Expr.getAppFn wta with
  | .const T us' => do
    let Tn ← pure T
    match fe.find? Tn with
    | some (.indInfo cvT caps) => do
      let targs ← pure (Expr.getAppArgsC wta)
      if caps.unitlike = true ∧
          reservedBasisNames.contains Tn = false ∧
          targs.length = caps.unitParams ∧
          us'.length = cvT.levelParams.length then do
        let tb ← r.inferIO depth b
        let wtb ← r.whnf depth tb
        if ← r.defeq depth wta wtb then do
          -- the type-former telescope certificate (a certificate
          -- family: official's `is_def_eq_unit_like` stops at the
          -- defeq above); off at `.trusted`
          let tyT ← constTyAtM fe T Tn us'
          certAtI mode (iotaCertsI r fe depth false tyT targs)
        else pure false
      else pure false
    | _ => pure false
  | _ => pure false

/-- Twin of `etaCert` (the λ's pieces come pre-destructured, as in the
spec). -/
def etaCertI (r : CoreFnsI) (_fe : FEnv) (depth : Nat)
    (ty₁ body₁ : Expr) (m₁ : BinderMeta) (b : Expr) :
    CheckCM Bool := do
  let tb ← r.inferIO depth b
  let wtb ← r.whnf depth tb
  match wtb with
  | .forallE ty₂ _ m₂ => do
    -- prop-ness agreement checked LAST (task #161); see `etaCert`
    if ← r.defeq depth ty₂ ty₁ then do
      let fv ← pure (Expr.fvar depth ty₁)
      let b₁ ← inst1M body₁ fv
      let ba ← pure (Expr.app b fv)
      unless ← r.defeq (depth + 1) b₁ ba do return false
      if mode.verifiedChecks && !(m₁.pw == m₂.pw) then
        throw (.notImplemented "sort-annotation mismatch (eta)")
      pure true
    else pure false
  | _ => pure false

/-- Twin of `stuckIrrel`. -/
def stuckIrrelI (r : CoreFnsI) (fe : FEnv) (depth : Nat) (a b : Expr) :
    CheckCM Bool := do
  if ← structEtaCertI mode r fe depth a b then pure true
  else if ← structEtaCertI mode r fe depth b a then pure true
  else if ← structUnitCertI mode r fe depth a b then pure true
  else proofIrrelI r fe depth a b

/-- Twin of `majorToCtor`. -/
def majorToCtorI (r : CoreFnsI) (fe : FEnv) (depth : Nat)
    (_recName : Name) (rules : List RecRule) (major : Expr) :
    CheckCM Expr := do
  if ← pure (isCtorAppC fe major) then pure major else
  match rules with
  | [rl] =>
    match fe.find? rl.ctor with
    | some (.ctorInfo cvj cnP _cnF) =>
      match (cvj.type.piResult).getAppFn with
      | .const T _ =>
        match fe.find? T with
        | some (.indInfo cvT caps) =>
          if rl.k = true then do
            let tmaj₀ ← r.inferIO depth major
            let tmaj ← r.whnf depth tmaj₀
            match Expr.getAppFn tmaj with
            | .const T' ust =>
              if (← pure (T' == T)) ∧ cvj.levelParams.length = ust.length then do
                let margs ← pure (Expr.getAppArgsC tmaj)
                if cnP ≤ margs.length then do
                  let ctorI ← pure rl.ctor
                  let h ← pure (Expr.const ctorI ust)
                  let fab ← mkAppNM h (margs.take cnP)
                  if ← pure (Expr.wscopedBC depth fab &&
                      Expr.looseBVarsBounded 0 fab &&
                      Expr.leafGuard fab major) then do
                    -- synthetic-spine certification (task #71): a
                    -- fabricated constructor spine keeps the ungated
                    -- telescope certificate, relocated here from the
                    -- fire path
                    let tyCtor ← constTyAtM fe ctorI rl.ctor ust
                    -- (a certificate family; off at `.trusted`)
                    if ← certAtI mode (iotaCertsI r fe depth false tyCtor
                        (margs.take cnP)) then do
                      -- official `to_cnstr_when_K` fabrication type
                      -- check (load-bearing with the major-slot
                      -- certificate gated at nonzero motives, tasks
                      -- #49/#71; arena bad/098_ruleKbad) — runs in
                      -- both modes; `proofIrrelI` stays as the
                      -- soundness certificate, a certificate family
                      -- (official stops at the type check), off at
                      -- `.trusted`
                      let tfab ← r.inferIO depth fab
                      if ← r.defeq depth tmaj tfab then
                        if ← certAtI mode (proofIrrelI r fe depth fab major) then
                          pure fab
                        else pure major
                      else pure major
                    else pure major
                  else pure major
                else pure major
              else pure major
            | _ => pure major
          else if rl.eta = true then do
            let tmaj₀ ← r.inferIO depth major
            let tmaj ← r.whnf depth tmaj₀
            match Expr.getAppFn tmaj with
            | .const T' ust => do
              let margs ← pure (Expr.getAppArgsC tmaj)
              let ustL ← pure ust
              -- instantiated non-Prop guard, as in the spec body
              -- `majorToCtor` (task #61)
              if (← pure (T' == T)) ∧ margs.length = caps.etaParams ∧
                  ust.length = cvT.levelParams.length ∧
                  capsNeverZero cvT.levelParams ustL caps = true then do
                let TI ← pure T
                let projs ← projAppsI fe T TI ust margs major caps.etaFields
                let ctorI ← pure caps.etaCtor
                let h ← pure (Expr.const ctorI ust)
                let fab ← mkAppNM h (margs ++ projs)
                if ← pure (Expr.wscopedBC depth fab &&
                    Expr.looseBVarsBounded 0 fab &&
                    Expr.leafGuard fab major) then do
                  -- synthetic-spine certification, as in the K
                  -- branch (task #71)
                  let tyCtor ← constTyAtM fe ctorI rl.ctor ust
                  -- (a certificate family; off at `.trusted`)
                  if ← certAtI mode (iotaCertsI r fe depth false tyCtor
                      (margs ++ projs)) then do
                    if ← structEtaCertWithI mode r fe depth fab major
                        tmaj then
                      pure fab
                    else if caps.etaFields = 0 then
                      if ← proofIrrelI r fe depth fab major then
                        pure fab
                      else pure major
                    else pure major
                  else pure major
                else pure major
              else pure major
            | _ => pure major
          else if T = andName then do
            -- the `And`-only rescue, as in the spec body
            let tmaj₀ ← r.inferIO depth major
            let tmaj ← r.whnf depth tmaj₀
            match Expr.getAppFn tmaj with
            | .const T' ust => do
              let margs ← pure (Expr.getAppArgsC tmaj)
              if (← pure (T' == T)) ∧ margs.length = cnP ∧
                  cvj.levelParams.length = ust.length ∧
                  fe.andRescueSlotsF rl.ctor cnP ust = true then do
                let TI ← pure T
                let projs ← projNodesI TI major [0, 1]
                let ctorI ← pure rl.ctor
                let h ← pure (Expr.const ctorI ust)
                let fab ← mkAppNM h (margs ++ projs)
                if ← pure (Expr.wscopedBC depth fab &&
                    Expr.looseBVarsBounded 0 fab &&
                    Expr.leafGuard fab major) then do
                  let tyCtor ← constTyAtM fe ctorI rl.ctor ust
                  if ← certAtI mode (iotaCertsI r fe depth false tyCtor
                      (margs ++ projs)) then do
                    let tfab ← r.inferIO depth fab
                    if ← r.defeq depth tmaj tfab then
                      if ← certAtI mode (proofIrrelI r fe depth fab major) then
                        pure fab
                      else pure major
                    else pure major
                  else pure major
                else pure major
              else pure major
            | _ => pure major
          else pure major
        | _ => pure major
      | _ => pure major
    | _ => pure major
  | _ => pure major

/-- Twin of `litMajorToCtor`. -/
def litMajorToCtorI (r : CoreFnsI) (fe : FEnv) (depth : Nat) (e : Expr) :
    CheckCM Expr := do
  match e with
  | .lit (.strVal s) =>
    if strLitSupportedF fe then do
      let x ← pure (strLitToConstructor s)
      r.whnf depth x
    else pure e
  | _ => litToCtorIfNatI fe e

/-- Twin of `projLitToCtor`. -/
def projLitToCtorI (r : CoreFnsI) (fe : FEnv) (depth : Nat) (e : Expr) :
    CheckCM Expr := do
  match e with
  | .lit (.strVal s) =>
    if strLitSupportedF fe then do
      let x ← pure (strLitToConstructor s)
      r.whnf depth x
    else pure e
  | _ => pure e

/-- Twin of `prepareMajor`: the major's preparation in the official
order (K rescue on the raw major, then whnf and the literal
conversion; elsewhere whnf, literal, eta).  The K flag is the single
rule's stored bit, as in the spec (`recRuleK`). -/
def prepareMajorI (r : CoreFnsI) (fe : FEnv) (depth : Nat)
    (recName : Name) (rules : List RecRule) (major : Expr) :
    CheckCM Expr := do
  if recRuleK rules then do
    let majorK ← majorToCtorI mode r fe depth recName rules major
    let major₀ ← r.whnf depth majorK
    litMajorToCtorI r fe depth major₀
  else do
    let major₀ ← r.whnf depth major
    let major₁ ← litMajorToCtorI r fe depth major₀
    majorToCtorI mode r fe depth recName rules major₁

/-- The nested-rule pin instantiations (structural recursion;
the spec side is `(recFireComparands …).2`'s `List.map`). -/
def pinArgsI (lps : List Name) (us : List Level) (args : List Expr)
    (t : Nat) : List Expr → CheckCM (List Expr)
  | [] => pure []
  | p :: ps => do
    let praw ← pure p
    let pi ← instLevelParamsM lps us praw
    let r ← instSpineM args t pi
    let rs ← pinArgsI lps us args t ps
    pure (r :: rs)

/-- The length of an application spine, without building its argument
list. -/
def iotaNumArgs : Expr → Nat → Nat
  | .app f _, n => iotaNumArgs f (n + 1)
  | _, n => n

/-- The arity pre-check of the ι step: `iotaRecI` returns `none`
unless the head is a stored recursor applied to exactly `majorIdx + 1`
arguments with the recursor's own number of levels
(`iotaRecI_of_arityOk_false`).  The whnf spine loop asks this before
every ι attempt, which is allocation-free where the ι step's own guard
would first materialise the argument list. -/
def iotaArityOk (fe : FEnv) (e : Expr) : Bool :=
  match Expr.getAppFn e with
  | .const c us =>
    match fe.find? c with
    | some (.recInfo cv mI _ _) =>
      iotaNumArgs e 0 == mI + 1 && us.length == cv.levelParams.length
    | _ => false
  | _ => false

/-- Twin of `iotaRec`. -/
def iotaRecI (r : CoreFnsI) (fe : FEnv) (depth : Nat) (e : Expr) :
    CheckCM (Option Expr) := do
  match Expr.getAppFn e with
  | .const c us => do
    let cn ← pure c
    match fe.find? cn with
    | some (.recInfo cv mI rP rules) => do
      let args ← pure (Expr.getAppArgsC e)
      -- checker change #9 (twin of `Core.lean`'s `iotaRec`): guard the
      -- recursor's level arity before the rule's RHS is instantiated.
      if args.length = mI + 1 ∧ us.length = cv.levelParams.length then do
        let bvar0 ← pure (Expr.mkBvar 0)
        let major ← prepareMajorI mode r fe depth cn rules (args.getD mI bvar0)
        match Expr.getAppFn major with
        | .const cj usj => do
          let cjn ← pure cj
          match fe.find? cjn with
          | some (.ctorInfo cvj _ _) =>
            match rules.find? (fun r' => r'.ctor == cjn) with
            | some rl => do
              let margs ← pure (Expr.getAppArgsC major)
              if margs.length = rl.ctorParams + rl.nfields then
               if rl.fire = .inert then
                 throw (.notImplemented
                   "iota reduction over a nested auxiliary recursor rule")
               else do
                -- (the ι batch: the two `stripPis` pins are gone — see
                -- the spec's `iotaRec`)
                -- the comparands (canonical: recursor's levels/args;
                -- nested: the stored major-domain instantiations)
                let cmpLvls : List Level ←
                  match rl.fire with
                  | .nested lvls _ => substLevelTreesM cv.levelParams us lvls
                  | _ =>
                    substLevelTreesM cv.levelParams us
                      (cvj.levelParams.map Level.param)
                let cmpArgs : List Expr ←
                  match rl.fire with
                  | .nested _ pins =>
                    pinArgsI cv.levelParams us (args.take rP) (rP - 1) pins
                  | _ => pure (args.take rl.ctorParams)
                if ← liftFueled "level comparison"
                    (← isEquivListLM usj cmpLvls) then do
                 -- the parameter comparison: not run at all for a
                 -- `.plain` rule the installing route marked
                 -- `paramsBlind` (`RecRule.compareParams`; official's
                 -- `inductive_reduce_rec` compares nothing).  Where it
                 -- is run it is verdict-relevant for a nested rule
                 -- (the comparands ARE the pins) and for a
                 -- projection-function rule, and a certificate family
                 -- for every other plain rule — the retired twin's
                 -- judgement, kept
                 if ← (if rl.compareParams then
                    certUnlessI mode
                      ((match rl.fire with | .nested _ _ => true | _ => false)
                        || Name.isProjFnShape cn)
                      (defEqListI r fe depth (margs.take rl.ctorParams)
                        cmpArgs)
                    else pure true) then do
                  -- ONE certificate family: the two instantiated
                  -- types, the two telescope runs and the
                  -- canonical-index comparison (which exists only
                  -- where indices do — the spec's `iotaRec`).  The
                  -- telescope runs are licensed (`iotaCertsIAux`) off
                  -- `mode.betaGate` — the same function the β site
                  -- reads, `true` at `.verified`.  Nothing here is
                  -- read outside the family, so the whole block is
                  -- what `.trusted` omits: the types are looked up
                  -- only where a certificate consumes them (DESIGN.md,
                  -- "CORET RETIRED", inversion 22).
                  if ← certAtI mode (do
                      let tyRec ← constTyAtM fe c cn us
                      if ← iotaCertsI r fe depth mode.betaGate tyRec
                          (args.take mI ++ [major]) then do
                        let tyCtor ← constTyAtM fe cj cjn usj
                        if ← iotaCertsI r fe depth mode.betaGate tyCtor
                            margs then
                          iotaIndexOkI r fe depth mI rP rl.ctorParams tyCtor
                            margs ((args.take mI).drop rP)
                        else pure false
                      else pure false) then do
                      let rhs ← ruleRhsAtM fe c cj cn cjn us
                      let red ← mkAppNM rhs
                        (args.take rP ++ margs.drop rl.ctorParams)
                      pure (some red)
                  else pure none
                 else pure none
                else pure none
              else pure none
            | none => pure none
          | _ => pure none
        | _ => pure none
      else pure none
    | _ => pure none
  | _ => pure none

/-- Twin of `projCert`. -/
def projCertI (r : CoreFnsI) (fe : FEnv) (depth : Nat) (lic : Bool)
    (c : Name) (us : List Level) (args : List Expr) : CheckCM Bool := do
  let cn ← pure c
  match fe.find? cn with
  | some (.ctorInfo _ _ _) => do
    let tyC ← constTyAtM fe c cn us
    iotaCertsI r fe depth lic tyC args
  | _ => pure false

/-- Twin of `projCertAt`. -/
def projCertAtI (r : CoreFnsI) (fe : FEnv) (depth : Nat) (verified lic : Bool)
    (c : Name) (us : List Level) (args : List Expr) : CheckCM Bool :=
  if verified then projCertI r fe depth lic c us args else pure true

mutual

/-- Bulk-beta argument loop (task #50): consume the whole application
spine against the whnf'd head `v`.  A lambda head enters the peel loop
(first binder inline, which keeps the argument count decreasing);
other heads try iota with one more argument and otherwise accumulate a
stuck application — exactly the per-level `whnfCoreBody` app clauses,
but with the chained per-argument `instantiate1` of the beta path
replaced by one bulk substitution per peeled group
(`ConLeche/Verify/BetaSpine.lean` proves the identification).  The
head-normalization loop's continuation `k` is threaded through
(task #106). -/
def whnfAppI (r : CoreFnsI) (fe : FEnv) (depth : Nat)
    (k : Expr → CheckCM Expr) :
    Expr → List Expr → CheckCM Expr
  | v, [] => pure v
  | v, a :: rest => do
    match v with
    | .lam ty body mb => do
        -- task #161: the β gate is a pure early return; the `else`
        -- arm is the pre-gate clause, verbatim (`betaGateFires`)
        if mode.betaSkip mb.pw then
          betaPeelI r fe depth k body [a] rest
        else do
          -- task #172 B4: the β certificate's inference at the io grade
          let ta ← r.inferIO depth a
          if ← r.defeq depth ta ty then
            betaPeelI r fe depth k body [a] rest
          else do
            let fa ← pure (Expr.app v a)
            mkAppNM fa rest
    | _ => do
      let fa ← pure (Expr.app v a)
      -- the ι step is tried only where it could fire; every other
      -- prefix of the spine returns `none` by `iotaRecI`'s own guard
      match ← (if iotaArityOk fe fa then iotaRecI mode r fe depth fa
               else pure none) with
      | some e'' => do
        let v' ← k e''
        whnfAppI r fe depth k v' rest
      | none => whnfAppI r fe depth k fa rest
termination_by _ args => (args.length, 0)
decreasing_by
  all_goals first
    | (apply Prod.Lex.left; simp; done)
    | (apply Prod.Lex.right' <;> simp)

/-- Peel loop of `whnfAppI`: `t` is the raw (unsubstituted) lambda body
after the binders consumed so far, `acc` their arguments (innermost
first).  Each binder's argument certificate (unconditional since the
task-#100 de-gating) substitutes only the *domain*; the body is
substituted once, when peeling stops. -/
def betaPeelI (r : CoreFnsI) (fe : FEnv) (depth : Nat)
    (k : Expr → CheckCM Expr) :
    Expr → List Expr → List Expr → CheckCM Expr
  | t, acc, [] => do
    let e' ← instListM t acc
    k e'
  | t, acc, a :: rest => do
    match t with
    | .lam ty body mb => do
        -- task #161: the β gate is a pure early return; the `else`
        -- arm is the pre-gate clause, verbatim (`betaGateFires`)
        if mode.betaSkip mb.pw then
          betaPeelI r fe depth k body (a :: acc) rest
        else do
          let ty' ← instListM ty acc
          -- task #172 B4: the io grade (see `whnfAppI`)
          let ta ← r.inferIO depth a
          if ← r.defeq depth ta ty' then
            betaPeelI r fe depth k body (a :: acc) rest
          else do
            let f' ← instListM t acc
            let fa ← pure (Expr.app f' a)
            mkAppNM fa rest
    | _ => do
      let e' ← instListM t acc
      let v ← k e'
      whnfAppI r fe depth k v (a :: rest)
termination_by _ _acc args => (args.length, 1)
decreasing_by
  all_goals first
    | (apply Prod.Lex.left; simp; done)
    | (apply Prod.Lex.right' <;> simp)

end

/-- Twin of `whnfCoreStep`: one head-normalization step (beta, iota,
projection) with the loop's continuation `k` abstracted, in the
open-recursion style of the whole module.  Only the spine head's
normalization stays a knot call (genuine nesting, bounded by the
term's depth); every *reduction* step is iteration, so a chain no
longer charges the shared recursion-depth budget one unit per step
(task #106 — that is what made the `Nat.brecOn` grind of
`Std.Time…toDays._proof_1` exhaust `checkFuel`). -/
def whnfCoreStepI (r : CoreFnsI) (fe : FEnv) (depth : Nat)
    (k : Expr → CheckCM Expr) (e : Expr) : CheckCM Expr := do
    match e with
    | .sort _ | .fvar .. | .forallE ..
    | .lam .. | .const .. | .lit _ => pure e
    | .app _ _ => do
      -- Bulk beta (task #50): normalize the spine head once and run the
      -- argument loop over the whole spine, batching consecutive
      -- lambda binders into one substitution.
      let h ← pure (Expr.getAppFn e)
      let args ← pure (Expr.getAppArgsC e)
      let v ← r.whnfCore depth h
      whnfAppI mode r fe depth k v args
    | .proj sn i pe => do
      let e' ← r.whnf depth pe
      let e' ← projLitToCtorI r fe depth e'
      let snn ← pure sn
      match fe.findProj? snn i with
      | some entry =>
        match Expr.getAppFn e' with
        | .const c us => do
          let args ← pure (Expr.getAppArgsC e')
          if (← pure (c == entry.ctor)) ∧ i < entry.numFields ∧
              args.length = entry.numParams + entry.numFields ∧
              us.length = entry.levelParams.length ∧
              entry.fireOk us = true then do
            let bvar0 ← pure (Expr.mkBvar 0)
            let arg := args.getD (entry.numParams + i) bvar0
            -- task #100 de-gating: the certificate runs
            -- unconditionally at the verified mode (the former
            -- nonzero-sort gate is unsound-to-model under the
            -- domain-relative collapse); task #175 W6: the spine
            -- against the constructor's type (see `projCert`); the
            -- trusted mode runs none (`projCertAt`).
            if ← projCertAtI r fe depth mode.verifiedChecks mode.betaGate c us args then
              k arg
            else pure (Expr.proj sn i e')
          else pure (Expr.proj sn i e')
        | _ => pure (Expr.proj sn i e')
      | none => pure (Expr.proj sn i e')
    | .letE _ _ _ =>
      -- unreachable by construction, as in the spec body (task #241):
      -- the annotate pass returns the ζ reduct, so no `letE` node
      -- survives into the checked world
      throw (.internal "whnfCore: `let` in an annotated expression")
    | .bvar _ =>
      throw (.notImplemented "whnf beyond the supported fragment")

/-- Twin of `whnfCoreLoop`: iterate `whnfCoreStepI` on its own step
budget. -/
def whnfCoreLoopI (r : CoreFnsI) (fe : FEnv) (depth : Nat) :
    Nat → Expr → CheckCM Expr
  | 0, _ => throw (.internal "fuel exhausted: whnfCore loop")
  | n + 1, e =>
    whnfCoreStepI mode r fe depth (whnfCoreLoopI r fe depth n) e

/-- Twin of `whnfCoreBody`: the head-normalization loop at its own step
budget. -/
def whnfCoreBodyI (r : CoreFnsI) (fe : FEnv) : Nat → Expr → CheckCM Expr :=
  fun depth e => whnfCoreLoopI mode r fe depth whnfCoreLoopFuel e

/-- Application-inference spine loop (task #50): walk the raw
Π-telescope against the arguments with deferred substitution — each
argument's certificate substitutes only its *domain*; the codomain is
substituted once per peeled group.  A non-syntactic telescope step
substitutes and normalizes, exactly like the chained `inferBody`
recursion (`ConLeche/Verify/BetaSpine.lean` proves the
identification). -/
def inferSpineI (r : CoreFnsI) (fe : FEnv) (depth : Nat) :
    Expr → Array Expr → List Expr → CheckCM Expr
  | ty, acc, [] => instListRevM ty acc
  | ty, acc, a :: rest => do
    match ty with
    | .forallE dom body _mt => do
      -- per-argument re-check (task #100 de-gating: the former
      -- possibly-Prop gate of task #49 is unsound-to-model under the
      -- domain-relative collapse; the certificate runs
      -- unconditionally, as in the spec body `inferBody`)
      let dom' ← instListRevM dom acc
      let ta ← r.infer depth a
      unless ← r.defeq depth ta dom' do
        throw (.invalid "application type mismatch")
      inferSpineI r fe depth body (acc.push a) rest
    | _ => do
      let ty' ← instListRevM ty acc
      let w ← r.whnf depth ty'
      match w with
      | .forallE dom body _mt => do
        let ta ← r.infer depth a
        unless ← r.defeq depth ta dom do
          throw (.invalid "application type mismatch")
        inferSpineI r fe depth body #[a] rest
      | _ => throw (.invalid "function expected")

/-- **The io-grade spine walk** (task #172 B4): `inferSpineI` with the
per-argument certificate gated — the ONE io-graded check
(`inferBodyIO`'s app clause, `ConLeche/Kernel/Core.lean`), in the bulk
telescope form.  At a ∀ step whose annotation datum is `.never` the
argument's inference and the domain comparison are skipped; the
returned type is the same telescope walk either way, so the lane is
annotation-blind in its results.  A syntactic `.forallE` is its own
whnf, so the syntactic step's datum is the datum the pure io body
reads off the whnf'd type.

**The licence reads the datum and nothing else** (the ruling of
2026-09-06).  It used to carry a `mode.verifiedChecks &&` mode conjunct; that
conjunct made the *trusted* core run the certificate the verified core
skips — an inversion of what the trusted mode is defined to be (the
real mode with certification-only steps omitted).  Validating the
datum is certification-only work and stays in group A; consuming it is
not.  The P tier's licensing theorem (`io_domain_transfer`,
`Model/IOLicense.lean`) never used the mode conjunct either: it spends
only `pwBit_ne_zero_of_isNever`.

**The read is `mode.ioSkip mt.pw`** (the twin's retirement): at
`.verified` that is `mt.pw.isNever` by `rfl` — the datum alone, as
above — and at `.trusted` it is `true`: the per-argument
certificate at an internal inference is a certificate family
(official's `infer_only` runs none), skipped wholesale. -/
def inferSpineIOI (r : CoreFnsI) (fe : FEnv) (depth : Nat) :
    Expr → Array Expr → List Expr → CheckCM Expr
  | ty, acc, [] => instListRevM ty acc
  | ty, acc, a :: rest => do
    match ty with
    | .forallE dom body mt => do
      unless mode.ioSkip mt.pw do
        let dom' ← instListRevM dom acc
        let ta ← r.infer depth a
        unless ← r.defeq depth ta dom' do
          throw (.invalid "application type mismatch")
      inferSpineIOI r fe depth body (acc.push a) rest
    | _ => do
      let ty' ← instListRevM ty acc
      let w ← r.whnf depth ty'
      match w with
      | .forallE dom body mt => do
        unless mode.ioSkip mt.pw do
          let ta ← r.infer depth a
          unless ← r.defeq depth ta dom do
            throw (.invalid "application type mismatch")
        inferSpineIOI r fe depth body #[a] rest
      | _ => throw (.invalid "function expected")

/-- Twin of `whnfStep`. -/
def whnfStepI (r : CoreFnsI) (fe : FEnv) (depth : Nat)
    (k : Expr → CheckCM Expr) (e : Expr) : CheckCM Expr := do
  let e₁ ← r.whnfCore depth e
  match ← reduceNatI r fe depth e₁ with
  | some e₂ => k e₂
  | none =>
    match ← unfoldDefinitionI fe e₁ with
    | some e₂ => k e₂
    | none => pure e₁

/-- Twin of `whnfLoop`. -/
def whnfLoopI (r : CoreFnsI) (fe : FEnv) (depth : Nat) :
    Nat → Expr → CheckCM Expr
  | 0, _ => throw (.internal "fuel exhausted: whnf loop")
  | n + 1, e => whnfStepI r fe depth (whnfLoopI r fe depth n) e

/-- Twin of `whnfBody`. -/
def whnfBodyI (r : CoreFnsI) (fe : FEnv) : Nat → Expr → CheckCM Expr :=
  fun depth e => whnfLoopI r fe depth whnfLoopFuel e

/-- Twin of `ensureSort` (returns the level; no readback needed). -/
def ensureSortI (r : CoreFnsI) (depth : Nat) (e : Expr) : CheckCM Level := do
  let w ← r.whnf depth e
  match w with
  | .sort u => pure u
  | _ => throw (.invalid "expected a sort")

/-! ### Binder-telescope loops (task #72)

The official-kernel discipline (lean4lean's `inferLambda`/`inferForall`
loops): peel a whole binder telescope accumulating opened free
variables, substituting only each binder's *domain* on the way in
(domains are small; `instListM` against the accumulator), infer or
annotate the leaf once on the bulk-opened body, then rebuild with one
`abstractRange` per domain and one over the leaf.  Each loop replays
exactly the per-binder checks of the chained recursion, in order; the
value-level identification with the chained spec bodies is
`ConLeche/Verify/BinderLoop.lean` (the `DiscI` walks relate the loops to
their pure mirrors, and `_sound_body` theorems reproduce a mirror run
in the original one-binder-at-a-time body at some fuel).
The peel fuel is semantically transparent: on exhaustion the leaf phase hands
the residual binder chain back to the knot, which is exactly the
chained spec's next step. -/

/-- Stack entry of `inferLamsI`: binder name, opened domain and binder
meta. -/
abbrev InferLamEntry := Expr × BinderMeta

/-- Rebuild loop of `inferLamsI`: fold the stack (innermost binder
first, `j` its binder level relative to the ambient depth `d`).  The
intermediate `∀`-node inferences of the chained body are
value-determined by the peel phase's domain sorts and the leaf phase's
body-type sort and cannot fail (task #100 stage 6: the per-level
λ-annotation re-check is gone with the stored annotations). -/
def inferLamsOutI (d : Nat) :
    List InferLamEntry → Nat → Expr → PropWhen → CheckCM Expr
  | [], _j, cur, _prevPw => pure cur
  | (tyo, mb) :: rest, j, cur, prevPw => do
    -- Task #161, the chain rule (see `inferBody`'s `.lam` clause): a
    -- node's prop-ness annotation must agree with its inner
    -- neighbour's (the innermost step compares the entry with itself
    -- — vacuously true).
    if mode.verifiedChecks && !(mb.pw == prevPw) then
      throw (.notImplemented "sort-annotation mismatch (lam-cod-chain)")
    let tyAbs ← abstractRangeM tyo d j
    let node ← pure (Expr.forallE tyAbs cur mb)
    inferLamsOutI d rest (j - 1) node mb.pw

/-- Leaf phase of `inferLamsI`: bulk-open the residual body, infer it,
then rebuild outward.

Task #152: at the verified modes the chain's body type is
sort-checked here — the spec's codomain check (`inferBody`'s `.lam`
clause), which fires at the innermost binder of a λ-chain, i.e.
exactly when the peel stops on a non-λ residual.  The guard is the
same one the spec uses, on the same term. -/
def inferLamsLeafI (r : CoreFnsI) (d : Nat) (t : Expr) (k : Nat)
    (fvs : Array Expr) (stk : List InferLamEntry) : CheckCM Expr := do
  let ob ← instListRevM t fvs
  let bt ← r.infer (d + k) ob
  match t with
  | .lam .. => pure ()
  | _ =>
    if mode.verifiedChecks then
      let btt ← r.inferIO (d + k) bt
      let wbtt ← r.whnf (d + k) btt
      match wbtt with
      | .sort vb =>
        -- Task #161: validate the innermost binder's prop-ness
        -- annotation against the chain's body-type sort — the leaf
        -- half of the spec's `.lam` clause check.
        match stk with
        | (_, mb₀) :: _ => do
          let pv ← pure (Level.zeronessOf vb)
          unless pv == mb₀.pw do
            throw (.notImplemented
              "sort-annotation mismatch (lam-cod-leaf)")
        | [] => pure ()
      | _ => throw (.invalid "expected a sort")
  let cur ← abstractRangeM bt d k
  -- The fold's initial neighbour: a λ residual (the fuel-exhausted
  -- path) supplies its own annotation — the head entry's chain check
  -- then compares against it, exactly as the spec's per-node clause
  -- does; a non-λ residual makes the head entry's step vacuous (its
  -- codomain fact is the leaf check above).
  let prevPw ← do
    match t with
    | .lam _ _ mbT => pure mbT.pw
    | _ =>
      pure (match stk with
        | (_, mb₀) :: _ => mb₀.pw
        | [] => .never)
  inferLamsOutI mode d stk (k - 1) cur prevPw

/-- λ-telescope inference loop (task #72; used by `inferBodyI`'s and
`inferBodyIOI`'s lam cases): peel the raw λ-chain, checking each opened
domain to be a type on the way in.  `k` counts the opened binders
(`≥ 1`: the caller peels the first binder inline), `fvs` their free
variables innermost-first. -/
def inferLamsI (r : CoreFnsI) (d : Nat) :
    Nat → Expr → Nat → Array Expr → List InferLamEntry → CheckCM Expr
  | fuel + 1, t, k, fvs, stk => do
    match t with
    | .lam ty body mb => do
      let tyo ← instListRevM ty fvs
      let tty ← r.infer (d + k) tyo
      let wtty ← r.whnf (d + k) tty
      match wtty with
      | .sort _ => do
        let fv ← pure (Expr.fvar (d + k) tyo)
        inferLamsI r d fuel body (k + 1) (fvs.push fv)
          ((tyo, mb) :: stk)
      | _ => throw (.invalid "expected a sort")
    | _ => inferLamsLeafI mode r d t k fvs stk
  | 0, t, k, fvs, stk => inferLamsLeafI mode r d t k fvs stk

/-- Rebuild loop of `inferPisI`: fold the accumulated domain sorts by
`imax`, innermost binder first — exactly the chained `∀`-rule's result
value.

Task #272 (GitHub issue #9): the codomain sort's zero-ness datum is
THREADED, not recomputed.  `zeronessOf (imax u v) = zeronessOf v`
holds definitionally, so every node of a ∀ telescope shares the leaf's
datum — the chain the annotation loop already folds
(`annotateBindersOutI`).  The fold used to read it out of a
`Level`-keyed memo, which MISSED at every step (a node's key
`.imax u v` is new each time) and then walked `zeronessOf` down the
growing right spine: `O(k²)` in the telescope depth `k`, and it was
90 % of the check phase on a ∀ chain of 40 000 binders. -/
def inferPisOutI : List (Level × PropWhen) → Level → PropWhen →
    CheckCM Level
  | [], v, _pv => pure v
  | (u, pw) :: rest, v, pv => do
    -- Task #161: validate the node's prop-ness annotation against its
    -- inferred codomain sort (`pv` is the zero-ness of `v`, the spec
    -- `∀`-clause's `v` at this node).
    if mode.verifiedChecks && !(pv == pw) then
      throw (.notImplemented "sort-annotation mismatch (forall-cod)")
    let v' ← pure (.imax u v)
    -- `zeronessOf v' = zeronessOf v = pv` (the `.imax` clause).
    inferPisOutI rest v' pv

/-- Leaf phase of `inferPisI`: bulk-open the residual body, infer its
sort, then fold the domain sorts outward. -/
def inferPisLeafI (r : CoreFnsI) (d : Nat) (t : Expr) (k : Nat)
    (fvs : Array Expr) (stk : List (Level × PropWhen)) : CheckCM Expr := do
  let ob ← instListRevM t fvs
  let bt ← r.infer (d + k) ob
  let wbt ← r.whnf (d + k) bt
  match wbt with
  | .sort v => do
    let iv ← inferPisOutI mode stk v (Level.zeronessOf v)
    pure (Expr.sort iv)
  | _ => throw (.invalid "expected a sort")

/-- ∀-telescope inference loop (task #100 stage 6: the `∀`-rule infers
its codomain sort — the stored annotation is not read): peel the raw
∀-chain, checking each opened domain to be a type on the way in and
accumulating its sort, infer the bulk-opened leaf's sort once, and
fold `imax` outward. -/
def inferPisI (r : CoreFnsI) (d : Nat) :
    Nat → Expr → Nat → Array Expr → List (Level × PropWhen) →
      CheckCM Expr
  | fuel + 1, t, k, fvs, stk => do
    match t with
    | .forallE ty body mb => do
      let tyo ← instListRevM ty fvs
      let tty ← r.infer (d + k) tyo
      let wtty ← r.whnf (d + k) tty
      match wtty with
      | .sort u => do
        let fv ← pure (Expr.fvar (d + k) tyo)
        inferPisI r d fuel body (k + 1) (fvs.push fv)
          ((u, mb.pw) :: stk)
      | _ => throw (.invalid "expected a sort")
    | _ => inferPisLeafI mode r d t k fvs stk
  | 0, t, k, fvs, stk => inferPisLeafI mode r d t k fvs stk

/-- Twin of `inferBody`. -/
def inferBodyI (r : CoreFnsI) (fe : FEnv) : Nat → Expr → CheckCM Expr :=
  fun depth e => do
    match e with
    | .sort u => do
      let su ← pure (.succ u)
      pure (Expr.sort su)
    | .fvar idx ty =>
      if idx < depth then pure ty
      else throw (.invalid "free variable out of scope")
    | .const n us => do
      let nm ← pure n
      match fe.find? nm with
      | none => throw (unknownConstError nm)
      | some ci =>
        unless !ci.isTowerEntry do
          throw (.invalid s!"projection table entry used as a constant {nm}")
        let cv := ci.toConstantVal
        unless us.length = cv.levelParams.length do
          throw (.invalid s!"incorrect number of universe levels for {nm}")
        constTyAtM fe n nm us
    | .lit (.natVal _) => do
      if natLitSupportedF fe then do
        let ni ← pure natName
        pure (Expr.const ni [])
      else throw (.invalid "Nat literal without the Nat basis declarations")
    | .lit (.strVal _) => do
      if strLitSupportedF fe then do
        let si ← pure stringName
        pure (Expr.const si [])
      else throw (.notImplemented
        "string literals before the String support declarations")
    | .forallE ty body mb => do
      -- Binder-telescope loop (task #72 discipline; the codomain sort
      -- is inferred; task #161: each node's prop-ness annotation is
      -- validated against it in the rebuild fold).
      let tty ← r.infer depth ty
      let wtty ← r.whnf depth tty
      match wtty with
      | .sort u => do
        let fv ← pure (Expr.fvar depth ty)
        let fuel ← peelFuelM
        inferPisI mode r depth fuel body 1 #[fv] [(u, mb.pw)]
      | _ => throw (.invalid "expected a sort")
    | .lam ty body mb => do
      let tty ← r.infer depth ty
      let wtty ← r.whnf depth tty
      match wtty with
      | .sort _ => do
        -- Binder-telescope loop (task #72): peel the whole λ-chain,
        -- open in bulk, rebuild with `abstractRange`.
        let fv ← pure (Expr.fvar depth ty)
        let fuel ← peelFuelM
        inferLamsI mode r depth fuel body 1 #[fv] [(ty, mb)]
      | _ => throw (.invalid "expected a sort")
    | .app _ _ => do
      -- Bulk telescope consumption (task #50): infer the spine head
      -- once and walk its Π-telescope against the whole spine.
      let h ← pure (Expr.getAppFn e)
      let args ← pure (Expr.getAppArgsC e)
      let tf ← r.infer depth h
      inferSpineI r fe depth tf #[] args
    | .proj sn i pe => do
      let tpe ← r.infer depth pe
      let te ← r.whnf depth tpe
      match Expr.getAppFn te with
      | .const T us => do
        let Tn ← pure T
        match fe.findProj? Tn i with
        | some entry => do
          let targs ← pure (Expr.getAppArgsC te)
          if T = sn ∧ targs.length = entry.numParams ∧
              us.length = entry.levelParams.length then do
            -- the official `infer_proj` restriction (task #175
            -- W4c/O4), as in the spec body
            if Level.isEquiv entry.structSort .zero == some true then
              unless Level.isEquiv
                  (Level.subst entry.levelParams us entry.fieldSort) .zero
                  == some true do
                throw (.invalid
                  "projection from a propositional structure must be a proposition")
            -- the body at the arguments and the subject, as in the
            -- spec body (task #175 S1) — through the memoized,
            -- sharing-preserving `Expr` instantiations
            -- (`ProjEntry.typeAtI`; the spec's `typeAt` is a tree walk
            -- that copied the subject and the parameters — the affine
            -- frontier's out-of-memory, DESIGN.md "The affine frontier")
            pure (entry.typeAtI us targs pe)
          else throw (.notImplemented "projection without a native entry")
        | none => throw (.notImplemented "projection without a native entry")
      | _ => throw (.notImplemented "projection without a native entry")
    | .letE _ _ _ =>
      -- unreachable by construction, as in the spec body (task #241):
      -- the official `infer_let` triple lives in `annotateBodyI`'s own
      -- `.letE` clause, which returns the ζ reduct (task #217)
      throw (.internal "inferType: `let` in an annotated expression")
    | .bvar _ =>
      throw (.notImplemented "inferType beyond the supported fragment")

/-- **The io-grade inference body** (task #172 B4): `inferBodyI` with
exactly the application clause changed — the spine walk is the gated
`inferSpineIOI` (the ONE io-graded check).  Every non-application
view dispatches to `inferBodyI`'s own clause, so there is no textual
clone to drift: the two bodies differ in one clause by construction.
Recursion grade is the record's: the knot ties this body to
`CoreFnsI.ioView`, so `r.infer` here is the io slot one level down —
the grade propagates exactly as official's `infer_only` does. -/
def inferBodyIOI (r : CoreFnsI) (fe : FEnv) : Nat → Expr → CheckCM Expr :=
  fun depth e => do
    match e with
    | .app _ _ => do
      let h ← pure (Expr.getAppFn e)
      let args ← pure (Expr.getAppArgsC e)
      let tf ← r.infer depth h
      inferSpineIOI mode r fe depth tf #[] args
    | .forallE ty body mb => do
      -- the pure io ∀ clause, **chained** (deliberately not the
      -- task-#72 telescope loop: the loops are the front door's
      -- optimization, and looping the io lane would owe the whole
      -- loop-identification walk family a second, io-graded instance
      -- for a lane whose subjects are internal re-inferences —
      -- recorded in the B4 seal as a measured-need follow-up)
      let tty ← r.infer depth ty
      let wtty ← r.whnf depth tty
      match wtty with
      | .sort u => do
        let fv ← pure (Expr.fvar depth ty)
        let ob ← inst1M body fv
        let bt ← r.infer (depth + 1) ob
        let v ← ensureSortI r (depth + 1) bt
        if mode.verifiedChecks then
          unless Level.zeronessOf v == mb.pw do
            throw (.notImplemented "sort-annotation mismatch (forall-cod)")
        let iu ← pure (.imax u v)
        pure (Expr.sort iu)
      | _ => throw (.invalid "expected a sort")
    | .lam ty body mb => do
      -- the pure io λ clause, chained; no domain-sort run (task #168
      -- stage 2, as in the spec)
      let fv ← pure (Expr.fvar depth ty)
      let ob ← inst1M body fv
      let bt ← r.infer (depth + 1) ob
      if mode.verifiedChecks then
        match body.lamPw with
        | some pwI =>
          unless mb.pw == pwI do
            throw (.notImplemented
              "sort-annotation mismatch (lam-cod-chain)")
        | none =>
          let btt ← r.infer (depth + 1) bt
          let vb ← ensureSortI r (depth + 1) btt
          unless Level.zeronessOf vb == mb.pw do
            throw (.notImplemented
              "sort-annotation mismatch (lam-cod-leaf)")
      let bAbs ← abstract1M bt depth
      pure (Expr.forallE ty bAbs mb)
    | _ => inferBodyI mode r fe depth e

/-- Twin of `boolTrueShortcut`. -/
def boolTrueShortcutI (r : CoreFnsI) (depth : Nat) (a : Expr) : CheckCM Bool := do
  let w ← r.whnf depth a
  pure (Expr.isBoolTrue w)

/-- Twin of `defeqStep`. -/
def defeqStepI (r : CoreFnsI) (fe : FEnv) (depth : Nat)
    (k : Bool → Expr → Expr → CheckCM Bool) (pi : Bool) (a b : Expr) :
    CheckCM Bool := do
    if a == b then pure true else
    -- the eq-true shortcut (E2), as in the spec
    let bt ← pure (Expr.isBoolTrue b)
    let af ← pure (Expr.hasFvar a)
    if ← (if pi && bt && !af then boolTrueShortcutI r depth a
        else pure false) then pure true else
    let a' ← r.whnfCore depth a
    let b' ← r.whnfCore depth b
    if a' == b' then pure true else
    -- proof irrelevance hoisted before lazy delta, as in the spec
    -- (and the official kernel); the `Prop` branch with the fast arms
    -- (task #168, Option U) — once per entry (`pi`; the spec's D3 note)
    let qp ← pure (Expr.quickPair a' b')
    if ← (if pi && !qp then propIrrelI r fe depth a' b' else pure false) then
      pure true else
    -- Literal folding only when both sides are fvar-free, mirroring
    -- the official kernel (`type_checker.cpp`, `lazy_delta_reduction`)
    -- and lean4lean (`TypeChecker.lean:782`); see `defeqBody` for the
    -- full rationale.  `hasFvarI` is an `O(1)` read of the eager
    -- per-node fvar-range array.
    let fold ← pure (!Expr.hasFvar a' && !Expr.hasFvar b')
    match ← (if fold then reduceNatI r fe depth a' else pure none) with
    | some a₂ => k true a₂ b'
    | none =>
    match ← (if fold then reduceNatI r fe depth b' else pure none) with
    | some b₂ => k true a' b₂
    | none =>
    -- lazy delta, decision before materialization; see `defeqBody`
    match ← pure (unfoldableHeadC fe a'),
        ← pure (unfoldableHeadC fe b') with
    | true, false =>
      match ← unfoldDefinitionI fe a' with
      | some a₂ => k false a₂ b'
      | none => pure false
    | false, true =>
      match ← unfoldDefinitionI fe b' with
      | some b₂ => k false a' b₂
      | none => pure false
    | true, true => do
      let ha ← pure (headHintC fe a')
      let hb ← pure (headHintC fe b')
      if ReducibilityHint.lt hb ha then
        match ← unfoldDefinitionI fe a' with
        | some a₂ => k false a₂ b'
        | none => pure false
      else if ReducibilityHint.lt ha hb then
        match ← unfoldDefinitionI fe b' with
        | some b₂ => k false a' b₂
        | none => pure false
      else if ReducibilityHint.sameRegular ha hb &&
          (← pure (sameConstHeadsC a' b')) then do
        if ← defeqSpineI r fe depth a' b' then pure true
        else
          match ← unfoldDefinitionI fe a', ← unfoldDefinitionI fe b' with
          | some a₂, some b₂ => k false a₂ b₂
          | _, _ => pure false
      else
        match ← unfoldDefinitionI fe a', ← unfoldDefinitionI fe b' with
        | some a₂, some b₂ => k false a₂ b₂
        | _, _ => pure false
    | false, false =>
    match a', b' with
    | .sort u, .sort v => do
      liftFueled "level comparison" (← isEquivLM u v)
    | .lit l₁, .lit l₂ => pure (l₁ == l₂)
    | .lit (.natVal n), .const c us =>
      if (← pure (c == natZeroName)) ∧ us = [] then pure (n == 0)
      else stuckIrrelI mode r fe depth a' b'
    | .const c us, .lit (.natVal n) =>
      if (← pure (c == natZeroName)) ∧ us = [] then pure (n == 0)
      else stuckIrrelI mode r fe depth a' b'
    | .lit (.natVal nn), .app f x => do
      match nn, f with
      | k + 1, .const c [] =>
        if ← pure (c == natSuccName) then do
          let kl ← pure (Expr.lit (.natVal k))
          r.defeq depth kl x
        else stuckIrrelI mode r fe depth a' b'
      | _, _ => stuckIrrelI mode r fe depth a' b'
    | .app f x, .lit (.natVal nn) => do
      match nn, f with
      | k + 1, .const c [] =>
        if ← pure (c == natSuccName) then do
          let kl ← pure (Expr.lit (.natVal k))
          r.defeq depth x kl
        else stuckIrrelI mode r fe depth a' b'
      | _, _ => stuckIrrelI mode r fe depth a' b'
    | .lit (.strVal s), .app fO _x => do
      match fO with
      | .const cO usO =>
        if (← pure (cO == stringOfListName)) ∧ usO = [] ∧ strLitSupportedF fe then do
          let sc ← pure (strLitToConstructor s)
          r.defeq depth sc b'
        else stuckIrrelI mode r fe depth a' b'
      | _ => stuckIrrelI mode r fe depth a' b'
    | .app fO _x, .lit (.strVal s) => do
      match fO with
      | .const cO usO =>
        if (← pure (cO == stringOfListName)) ∧ usO = [] ∧ strLitSupportedF fe then do
          let sc ← pure (strLitToConstructor s)
          r.defeq depth a' sc
        else stuckIrrelI mode r fe depth a' b'
      | _ => stuckIrrelI mode r fe depth a' b'
    | .fvar i _, .fvar j _ =>
      if i == j then pure true
      else stuckIrrelI mode r fe depth a' b'
    | .const n us, .const n' us' =>
      if n = n' then do
        if ← liftFueled "level comparison" (← isEquivListLM us us') then
          pure true
        else stuckIrrelI mode r fe depth a' b'
      else stuckIrrelI mode r fe depth a' b'
    | .forallE ty₁ body₁ m₁, .forallE ty₂ body₂ m₂ => do
      -- prop-ness agreement checked LAST (task #161); see `defeqBody`
      unless ← r.defeq depth ty₁ ty₂ do return false
      let fv ← pure (Expr.fvar depth ty₂)
      let b₁ ← inst1M body₁ fv
      let b₂ ← inst1M body₂ fv
      unless ← r.defeq (depth + 1) b₁ b₂ do return false
      if mode.verifiedChecks && !(m₁.pw == m₂.pw) then
        throw (.notImplemented "sort-annotation mismatch (defeq-forall)")
      pure true
    | .lam ty₁ body₁ m₁, .lam ty₂ body₂ m₂ => do
      unless ← r.defeq depth ty₁ ty₂ do return false
      let fv ← pure (Expr.fvar depth ty₂)
      let b₁ ← inst1M body₁ fv
      let b₂ ← inst1M body₂ fv
      unless ← r.defeq (depth + 1) b₁ b₂ do return false
      if mode.verifiedChecks && !(m₁.pw == m₂.pw) then
        throw (.notImplemented "sort-annotation mismatch (defeq-lam)")
      pure true
    | .app _f₁ _a₁, .app _f₂ _a₂ => do
      -- spine-wise congruence, as in the spec body `defeqBody`
      -- (official `is_def_eq_app`)
      let as₁ ← pure (Expr.getAppArgsC a')
      let as₂ ← pure (Expr.getAppArgsC b')
      if as₁.length = as₂.length then do
        let h₁ ← pure (Expr.getAppFn a')
        let h₂ ← pure (Expr.getAppFn b')
        if ← r.defeq depth h₁ h₂ then do
          if ← defEqListI r fe depth as₁ as₂ then pure true
          else stuckIrrelI mode r fe depth a' b'
        else stuckIrrelI mode r fe depth a' b'
      else stuckIrrelI mode r fe depth a' b'
    | .proj s₁ i₁ e₁, .proj s₂ i₂ e₂ => do
      if s₁ == s₂ && i₁ == i₂ then do
        if ← r.defeq depth e₁ e₂ then pure true
        else stuckIrrelI mode r fe depth a' b'
      else stuckIrrelI mode r fe depth a' b'
    | .lam ty₁ body₁ m₁, _ => do
      if ← etaCertI mode r fe depth ty₁ body₁ m₁ b' then pure true
      else stuckIrrelI mode r fe depth a' b'
    | _, .lam ty₂ body₂ m₂ => do
      if ← etaCertI mode r fe depth ty₂ body₂ m₂ a' then pure true
      else stuckIrrelI mode r fe depth a' b'
    | _, _ => stuckIrrelI mode r fe depth a' b'

/-- Twin of `defeqLoop`. -/
def defeqLoopI (r : CoreFnsI) (fe : FEnv) (depth : Nat) :
    Nat → Bool → Expr → Expr → CheckCM Bool
  | 0, _, _, _ => throw (.internal "fuel exhausted: defeq loop")
  | fl + 1, pi, a, b =>
    defeqStepI mode r fe depth (defeqLoopI r fe depth fl) pi a b

/-- Twin of `defeqBody`. -/
def defeqBodyI (r : CoreFnsI) (fe : FEnv) : Nat → Expr → Expr → CheckCM Bool :=
  fun depth a b => defeqLoopI mode r fe depth defeqLoopFuel true a b

/-- Twin of `isPropType`. -/
def isPropTypeI (r : CoreFnsI) (_fe : FEnv) (depth : Nat) (ty : Expr) :
    CheckCM Bool := do
  let ty' ← r.annotate depth ty
  let tty ← r.inferIO depth ty'
  let s ← ensureSortI r depth tty
  let z ← pure .zero
  liftFueled "level comparison" (← isEquivLM s z)

/-! ### Annotation binder-telescope loops (task #72; see the
`inferLamsI` block comment) -/

/-- Stack entry of the annotation loops: binder name, annotated opened
domain, binder info. -/
abbrev AnnotBinderEntry := Expr × BinderMeta

/-- The cached twin of `annotBinderMeta`. -/
def annotBinderMetaI (pw? : Option PropWhen) (mb : BinderMeta) : BinderMeta :=
  match pw? with
  | some pw => if pwWritten mb.pw then mb else ⟨pw⟩
  | none => mb

/-- Rebuild loop of the annotation binder-telescope loops: fold the
stack (innermost binder first, `j` its binder level), rebuilding one
binder node per entry.

Task #161 P5 — the untrusted write: `pw?` is the datum written just
below, threaded outward (`zeronessOf (imax u v) = zeronessOf v` makes
every ∀ node's codomain-sort zero-ness its inner neighbour's, and the
λ chain rule says the same of λ nodes — so the telescope pays one
computation, in the leaf phase, and every node above reads).  `none` =
no write (unverified mode).  A node whose input datum is a real
annotation (`pwWritten`) is left alone — validation judges it, and it
is that datum that travels on. -/
def annotateBindersOutI (mk : Expr → Expr → BinderMeta → Expr)
    (d : Nat) (pw? : Option PropWhen) :
    List AnnotBinderEntry → Nat → Expr → CheckCM Expr
  | [], _j, cur => pure cur
  | (ty', mb) :: rest, j, cur => do
    let tyAbs ← abstractRangeM ty' d j
    let node ← pure (mk tyAbs cur (annotBinderMetaI pw? mb))
    -- Task #161 P5 (proof-lane repair): thread the datum *just
    -- written* outward rather than re-stamping the leaf's.  The two
    -- differ only above an explicitly-annotated binder, and there the
    -- chain rule is what the spec's `annotPwPi`/`annotPwLam` read —
    -- they see the rebuilt inner node, not the leaf.  One fold, one
    -- rule, both passes.
    annotateBindersOutI mk d
      (pw?.map fun _ => (annotBinderMetaI pw? mb).pw)
      rest (j - 1) node

/-- The ∀ telescope's datum (task #161 P5), computed once: the leaf
codomain sort's zero-ness — shared by every node of the telescope
because `zeronessOf (imax u v) = zeronessOf v`.  A ∀ residual (the
fuel path) supplies its own already-written datum instead, exactly as `annotPwPi` reads it. -/
def annotPwPiI (r : CoreFnsI) (fe : FEnv) (depth : Nat) (body' : Expr) :
    CheckCM PropWhen := do
  -- task #168 stage 2: the head-symbol reader first (it subsumes the
  -- chain read), as in the spec
  match typeSortPW fe.find? body' with
  | some pw => pure pw
  | none => do
    let bt ← r.inferIO depth body'
    let v ← ensureSortI r depth bt
    pure (Level.zeronessOf v)

/-- The telescope loop's write.  UNGATED since 2026-09-06: writing the
datum is part of the real checker's algorithm (the readers and the
licences consume it); only *validating* it is certification-only work,
so the trusted mode annotates exactly as the verified mode does.  The
`Option` shape is kept — `annotBinderMetaI` still leaves an
already-written annotation alone. -/
def annotatePisPwI (r : CoreFnsI) (fe : FEnv) (d k : Nat) (leaf' : Expr) :
    CheckCM (Option PropWhen) := do
  let p ← annotPwPiI r fe (d + k) leaf'
  pure (some p)

/-- Leaf phase of `annotatePisI`: bulk-open and annotate the residual
body, then rebuild outward. -/
def annotatePisLeafI (r : CoreFnsI) (fe : FEnv) (d : Nat) (t : Expr) (k : Nat)
    (fvs : Array Expr) (stk : List AnnotBinderEntry) : CheckCM Expr := do
  let to ← instListRevM t fvs
  let leaf' ← r.annotate (d + k) to
  let pw? ← annotatePisPwI r fe d k leaf'
  let cur ← abstractRangeM leaf' d k
  annotateBindersOutI (fun ty b mb => .forallE ty b mb) d pw?
    stk (k - 1) cur

/-- ∀-telescope annotation loop (task #72; `annotateBodyI`'s forallE
case): peel the raw ∀-chain, annotating each opened domain on the way
in.  `k ≥ 1` counts the opened binders (first binder peeled inline by
the caller), `fvs` their free variables innermost-first. -/
def annotatePisI (r : CoreFnsI) (fe : FEnv) (d : Nat) :
    Nat → Expr → Nat → Array Expr → List AnnotBinderEntry → CheckCM Expr
  | fuel + 1, t, k, fvs, stk => do
    match t with
    | .forallE ty body mb => do
      let tyo ← instListRevM ty fvs
      let ty' ← r.annotate (d + k) tyo
      let fv ← pure (Expr.fvar (d + k) ty')
      annotatePisI r fe d fuel body (k + 1) (fvs.push fv)
        ((ty', mb) :: stk)
    | _ => annotatePisLeafI r fe d t k fvs stk
  | 0, t, k, fvs, stk => annotatePisLeafI r fe d t k fvs stk

/-- The λ chain's datum (task #161 P5): the zero-ness of the sort of
the innermost body's TYPE; every λ node of the chain shares it (the
`(lam-cod-chain)` rule).  A λ residual supplies its own already-written
datum, exactly as `inferLamsLeafI` reads it. -/
def annotPwLamI (r : CoreFnsI) (fe : FEnv) (depth : Nat) (body' : Expr) :
    CheckCM PropWhen := do
  -- task #168 stage 2: the reader first, as in the spec
  match proofPW fe.find? body' with
  | some pw => pure pw
  | none => do
    let bt ← r.inferIO depth body'
    let btt ← r.inferIO depth bt
    let vb ← ensureSortI r depth btt
    pure (Level.zeronessOf vb)

/-- The λ twin of `annotatePisPwI`, ungated with it. -/
def annotateLamsPwI (r : CoreFnsI) (fe : FEnv) (d k : Nat) (leaf' : Expr) :
    CheckCM (Option PropWhen) := do
  let p ← annotPwLamI r fe (d + k) leaf'
  pure (some p)

/-- Leaf phase of `annotateLamsI` (as `annotatePisLeafI`, rebuilding
λ-nodes). -/
def annotateLamsLeafI (r : CoreFnsI) (fe : FEnv) (d : Nat) (t : Expr) (k : Nat)
    (fvs : Array Expr) (stk : List AnnotBinderEntry) : CheckCM Expr := do
  let to ← instListRevM t fvs
  let leaf' ← r.annotate (d + k) to
  let pw? ← annotateLamsPwI r fe d k leaf'
  let cur ← abstractRangeM leaf' d k
  annotateBindersOutI (fun ty b mb => .lam ty b mb) d pw?
    stk (k - 1) cur

/-- λ-telescope annotation loop (task #72; `annotateBodyI`'s lam
case). -/
def annotateLamsI (r : CoreFnsI) (fe : FEnv) (d : Nat) :
    Nat → Expr → Nat → Array Expr → List AnnotBinderEntry → CheckCM Expr
  | fuel + 1, t, k, fvs, stk => do
    match t with
    | .lam ty body mb => do
      let tyo ← instListRevM ty fvs
      let ty' ← r.annotate (d + k) tyo
      let fv ← pure (Expr.fvar (d + k) ty')
      annotateLamsI r fe d fuel body (k + 1) (fvs.push fv)
        ((ty', mb) :: stk)
    | _ => annotateLamsLeafI r fe d t k fvs stk
  | 0, t, k, fvs, stk => annotateLamsLeafI r fe d t k fvs stk

/-- Twin of `annotateBody`. -/
def annotateBodyI (r : CoreFnsI) (fe : FEnv) : Nat → Expr → CheckCM Expr :=
  fun depth e => do
    match e with
    | .bvar _ => pure e
    | .fvar idx _ =>
      if idx < depth then pure e
      else throw (.invalid "free variable out of scope")
    | .sort _ => pure e
    | .const .. => pure e
    | .lit (.natVal _) => do
      if natLitSupportedF fe then pure e
      else throw (.invalid "Nat literal without the Nat basis declarations")
    | .lit (.strVal _) => do
      if strLitSupportedF fe then pure e
      else throw (.notImplemented
        "string literals before the String support declarations")
    | .app f a => do
      -- structural (task #100 stage 6: the application checks moved to
      -- the driver's inference sweep)
      let f' ← r.annotate depth f
      let a' ← r.annotate depth a
      pure (Expr.app f' a')
    | .forallE ty body mb => do
      -- Binder-telescope loop (task #72): peel the whole ∀-chain,
      -- open in bulk, rebuild with `abstractRange`.
      let ty' ← r.annotate depth ty
      let fv ← pure (Expr.fvar depth ty')
      let fuel ← peelFuelM
      annotatePisI r fe depth fuel body 1 #[fv] [(ty', mb)]
    | .lam ty body mb => do
      -- The λ-loop is chain-identical only on bvar-closed nodes (the
      -- chained tails re-open exactly what they closed); disciplined
      -- inputs always are, and the cached bound decides in O(1).
      if (← bvarBoundM e) = 0 then do
        let ty' ← r.annotate depth ty
        let fv ← pure (Expr.fvar depth ty')
        let fuel ← peelFuelM
        annotateLamsI r fe depth fuel body 1 #[fv] [(ty', mb)]
      else do
        let ty' ← r.annotate depth ty
        let fv ← pure (Expr.fvar depth ty')
        let ob ← inst1M body fv
        let body' ← r.annotate (depth + 1) ob
        let bAbs ← abstract1M body' depth
        -- task #161 P5: the single-binder write (the λ-loop's rule at
        -- a chain of length one; see `annotateLamsLeafI`)
        let pw ← if !pwWritten mb.pw then
            annotPwLamI r fe (depth + 1) body'
          else pure mb.pw
        pure (Expr.lam ty' bAbs ⟨pw⟩)
    | .letE ty v b => do
      -- official `infer_let` check order (see the spec body): the
      -- annotation is a type, the value's inferred type matches it,
      -- then the body with the value transparent (zeta at annotate;
      -- `inst1M` keeps the substitution sharing-preserving).  Task #217
      -- (audit follow-up #206-S1) put the triple back: the pass returns
      -- the ζ reduct, so `inferBodyI`'s `.letE` arm never sees the node
      -- — task #241 made that arm a positive `.internal` error.
      let ty' ← r.annotate depth ty
      let tty ← r.infer depth ty'
      let _ ← ensureSortI r depth tty
      let v' ← r.annotate depth v
      let tv ← r.infer depth v'
      unless ← r.defeq depth tv ty' do
        throw (.invalid "let value type mismatch")
      let ob ← inst1M b v
      r.annotate depth ob
    | .proj sn i pe => do
      let e' ← r.annotate depth pe
      let tpe ← r.inferIO depth e'
      let te ← r.whnf depth tpe
      match Expr.getAppFn te with
      | .const T _ => do
        let Tn ← pure T
        match fe.findProj? Tn i with
        | some entry => do
          let targs ← pure (Expr.getAppArgsC te)
          -- TASK #271 (issue #7), as in the pure twin
          unless T = sn do
            throw (.invalid "invalid projection: the node names another structure")
          unless targs.length = entry.numParams do
            throw (.invalid "projection parameter mismatch")
          pure (Expr.proj T i e')
        | none =>
          throw (if (fe.findProj? Tn 0).isSome then
              CheckError.invalid "projection index out of range"
            else .notImplemented "projection on a non-structure-like type")
      | _ => throw (.notImplemented "projection on a non-structure type")

/-! ## The memoized knot -/

/-- Memoize a unary entry point under its node (`O(1)` key).

`@[inline]` (the retired twin's perf-eng E2, now the one knot's): after
inlining the getter/setter lambdas beta-reduce away and the memo probe
compiles into the record field's own closure.  A compiler attribute
only — the term the proofs unfold is unchanged. -/
@[inline] def memoEI (get' : CState → Std.HashMap Expr Expr)
    (set' : CState → Std.HashMap Expr Expr → CState)
    (f : Nat → Expr → CheckCM Expr) : Nat → Expr → CheckCM Expr :=
  fun d e => do
    match (get' (← get))[e]? with
    | some r => pure r
    | none =>
      let r ← f d e
      modify fun st =>
          let mp := get' st
        let st := set' st ∅
        set' st (mp.insert e r)
      pure r

/-- Memoize the definitional-equality entry point under the
index pair (`@[inline]` as `memoEI`). -/
@[inline] def memoBI (f : Nat → Expr → Expr → CheckCM Bool) :
    Nat → Expr → Expr → CheckCM Bool :=
  fun d a b => do
    match (← get).defeqC[(a, b)]? with
    | some r => pure r
    | none =>
      let r ← f d a b
      modify fun st =>
        let mp := st.defeqC
        let st := { st with defeqC := ∅ }
        { st with defeqC := mp.insert (a, b) r }
      pure r

/-- Tie the bodies at the memoizing state monad (fuel only
here, as in `coreKnot`; levels built lazily).

**The knot takes the mode** (task #185; from 2026-09-06 to then it
took a configuration record standing in for it).  `coreKnotI .verified`
is the verified core the capstones are stated about, and
`coreKnotI .trusted` is the trusted core `--trusted` runs — the same
function at the other mode.  The mode-parametric simulation tower
(`ConLeche/Verify/Cached/*`) is stated at `coreKnotI mode` under
`hμ : mode.verifiedChecks = true`. -/
def coreKnotI (fe : FEnv) : Nat → CoreFnsI
  | 0 =>
    { whnfCore := fun _ _ => throw (.internal "fuel exhausted: whnfCore")
      whnf := fun _ _ => throw (.internal "fuel exhausted: whnf")
      infer := fun _ _ => throw (.internal "fuel exhausted: infer")
      defeq := fun _ _ _ => throw (.internal "fuel exhausted: defeq")
      annotate := fun _ _ => throw (.internal "fuel exhausted: annotate")
      inferIO := fun _ _ => throw (.internal "fuel exhausted: infer") }
  | fuel + 1 =>
    -- **NOT a `Thunk`** (task #179).  The previous fuel level used to be
    -- `Thunk`-cached (perf-eng E1: built once per record rather than once
    -- per cache-missing call), and that single word cost 13.8 % of
    -- `init-full`.  `lean_thunk_get_core` calls `mark_mt` on the forced
    -- **value** — the runtime's invariant is that a single-threaded object
    -- may not be reachable from a multi-threaded one, and a thunk may be
    -- forced from another thread — so forcing this thunk marked the whole
    -- reachable graph of its value multi-threaded, and the value's six
    -- closures capture `fe`.  Two consequences, both `O(|env|)` per
    -- *declaration*: (i) the mark itself walks the index's whole bucket
    -- array, and (ii) an MT object is never `lean_is_exclusive`, so
    -- `FEnv.push`'s `idx.insert` stopped updating in place and copied the
    -- bucket array (with an atomic `lean_inc` per slot) at every accepted
    -- constant — the two symbols task #177 left unattributed,
    -- `lean_mark_mt` (7.6 %) and `lean_copy_expand_array` (6.2 %).  The
    -- copy re-created the array as single-threaded, the next force marked
    -- it again, and the loop sustained itself.  A plain `Unit`-closure
    -- forces nothing and marks nothing; it pays E1 back (one record per
    -- cache-missing call) and that is the smaller number by 5×.
    -- `Thunk.get ⟨f⟩` is `f ()` by structure eta, so this is the same
    -- term: no proof in `ConLeche/Verify/Cached/*` moved.
    let prev : Unit → CoreFnsI := fun _ => coreKnotI fe fuel
    -- task #172 B2 / #185: the template's parameter is the mode, an
    -- enum passed down once per *driver* — nothing is built per knot
    -- level or per call (at B2 a record allocation at every
    -- head-normalization entry cost +0.155 % on `init-prelude`).
    { whnfCore := memoEI (·.whnfCoreC)
        (fun st mp => { st with whnfCoreC := mp })
        (fun d e => whnfCoreBodyI mode (prev ()) fe d e)
      whnf := memoEI (·.whnfC) (fun st mp => { st with whnfC := mp })
        (fun d e => whnfBodyI (prev ()) fe d e)
      infer := memoEI (·.inferC) (fun st mp => { st with inferC := mp })
        (fun d e => inferBodyI mode (prev ()) fe d e)
      defeq := memoBI
        (fun d a b => defeqBodyI mode (prev ()) fe d a b)
      annotate := memoEI (·.annotC) (fun st mp => { st with annotC := mp })
        (fun d e => annotateBodyI (prev ()) fe d e)
      -- **The io slot** (task #170 / #172 B4), selected once per knot
      -- level: at `ioGate` the io body under its OWN memo
      -- (`CState.inferIOC` — the task-#170 memo ruling: a hit in the io
      -- memo never serves a full-infer query), tied to the io-grade
      -- view of the previous level (the grade propagates); at
      -- `ioGate = false` — no mode any more — the full inference
      -- closure, verbatim, under one memo, because the two grades are
      -- the same function there (task #170: "in R mode infer_only is
      -- just equivalent to infer").
      inferIO := if mode.ioGate then
          memoEI (·.inferIOC) (fun st mp => { st with inferIOC := mp })
            (fun d e => inferBodyIOI mode (prev ()).ioView fe d e)
        else
          memoEI (·.inferC) (fun st mp => { st with inferC := mp })
            (fun d e => inferBodyI mode (prev ()) fe d e) }

/-! ## The named concrete cores (task #172, batches B2 and B3; the R
half retired 2026-09-05; the T half instantiated 2026-09-06)

The template's whole point, spelled out: these are **definitions, not
clones** — one body, one name per family, and each unfolds to a term
with no `CheckMode` branch left in it.  Since the twin's retirement
the trusted core is the second instantiation of the same four bodies,
at `.trusted` (`…TC` below): of the `CheckMode` functions
(`ConLeche/Kernel/Env.lean`) only `verifiedChecks` and `certs` differ
between the two constructors (`betaGate` does too, but every read of
it here sits under a `certs` read or a `verifiedChecks` read that is
off at `.trusted`), so **the `mode.verifiedChecks` reads plus the
`certAtI`/`certUnlessI`/`betaSkip`/`ioSkip` reads in this module are
the complete list of what the trusted mode omits**.

`whnfCoreBodyPC` is the P core's head normalization:
`CheckMode.betaSkip .verified` is `PropWhen.isNever`, so the surviving
branch reads the redex's **validated annotation datum**.  That is
data, and it is the licence's own subject (`WellDenotedV_beta_gate`), not
a flag.

B3 added the remaining three configured families.  Their config read
is `mode.verifiedChecks` — the λ-codomain sort check and the ∀/λ annotation
validation — which is `true` at `.verified`, so at the named core the `if`
is its own *then* arm by `rfl` and the check is unconditionally
present:

* `inferBodyPC` — the λ-chain codomain sort check and the ∀/λ
  chain-rule `pw` agreement, both unconditional;
* `defeqBodyPC` — the `pw`-agreement comparisons at the ∀/λ conversion
  clauses and inside `etaCertI`, unconditional;
* `annotateBodyPC` — the two annotation `pw` writes, unconditional.

**THE R HALF IS RETIRED** (2026-09-05).  `whnfCoreBodyRC`,
`inferBodyRC`, `defeqBodyRC` and `annotateBodyRC` were the same four
bodies at `cfgR` — every certificate unconditional, the census's part 2
§2(b) core.  The user's ruling removed the collapsed-model consistency
proof that was the R core's whole reason to exist, and with the
acceptance delta against the graded core measured at ZERO (B4: 225
fixtures plus init-full, byte-identical), the core went with its proof.
`cfgR` is gone, with the whole configuration record (task #185).

**`whnf` needs no instantiation and that is a finding, not an
omission.**  `whnfBodyI` (and `whnfStepI`/`whnfLoopI` under it) reads
no mode function at all: the whole δ/ι/β content sits in
`whnfCore`, which `whnf` reaches through the knot.

The `rfl` identities of the mode functions at the two constructors are
in `ConLeche/Verify/BetaGate.lean` (the implementation tier may not
import `Verify`): every landed statement about `inferBodyI mode`
(etc.) is a statement about this core at the concrete mode,
definitionally. -/

/-- **The P core's head-normalization body.**  Flag-free by
construction; the one surviving branch reads the validated annotation
datum. -/
def whnfCoreBodyPC (r : CoreFnsI) (fe : FEnv) : Nat → Expr → CheckCM Expr :=
  whnfCoreBodyI .verified r fe

/-- **The P core's inference body.**  Flag-free:
`CheckMode.verifiedChecks .verified` is `true`, so the λ-codomain sort
check and the chain-rule annotation agreement are unconditional. -/
def inferBodyPC (r : CoreFnsI) (fe : FEnv) : Nat → Expr → CheckCM Expr :=
  inferBodyI .verified r fe

/-- **The P core's conversion body.**  Flag-free: the ∀/λ `pw`
agreement checks are unconditional. -/
def defeqBodyPC (r : CoreFnsI) (fe : FEnv) :
    Nat → Expr → Expr → CheckCM Bool :=
  defeqBodyI .verified r fe

/-- **The P core's annotation pass.**  Flag-free: the two `pw` writes
are unconditional.  (Annotation stays its own pass in every core — the
user's concession; what the template removes is the *flag*, not the
pass.) -/
def annotateBodyPC (r : CoreFnsI) (fe : FEnv) :
    Nat → Expr → CheckCM Expr :=
  annotateBodyI r fe

/-! ### The trusted core — the same bodies at `.trusted`

Unverified by construction (no capstone covers `.trusted`, and none will:
the mode is defined as *unvalidated*), but not a second
implementation: each definition below is its `…PC` sibling with the
mode swapped, and `verifiedChecks`/`certs` (both `false` at
`.trusted`) are the only reads that compute differently.
`annotateBodyI` reads no mode, so the annotation pass has one name for
both cores. -/

/-- **The trusted core's head-normalization body**: the β argument
certificate, the ι telescope certificates and index comparison, the
η/unit/K-rescue certificates and the projection certificate family
are all off (`CheckMode.certs .trusted`, `CheckMode.verifiedChecks
.trusted`); every guard and comparison official performs runs. -/
def whnfCoreBodyTC (r : CoreFnsI) (fe : FEnv) : Nat → Expr → CheckCM Expr :=
  whnfCoreBodyI .trusted r fe

/-- **The trusted core's inference body**: the λ-codomain sort check
and the ∀/λ annotation validations are off; its io grade
(`inferBodyIOI .trusted`, the knot's `inferIO` slot) runs no
per-argument certificate at all (`ioSkip_trusted`). -/
def inferBodyTC (r : CoreFnsI) (fe : FEnv) : Nat → Expr → CheckCM Expr :=
  inferBodyI .trusted r fe

/-- **The trusted core's conversion body**: the ∀/λ `pw` agreement
checks (and `etaCertI`'s) are off, and so are the structure-η,
unit-like and K-rescue certificate families reached through
`stuckIrrelI`/`whnfCore`. -/
def defeqBodyTC (r : CoreFnsI) (fe : FEnv) :
    Nat → Expr → Expr → CheckCM Bool :=
  defeqBodyI .trusted r fe

end ConLeche.Cached
