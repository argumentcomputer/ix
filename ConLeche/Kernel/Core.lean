module

import ConLeche.Kernel.Level
import ConLeche.Kernel.ExprOps
public import ConLeche.Kernel.CoreDefs

@[expose] public section

/-!
# The checker core, in open-recursion style

Every core function is written **once**, as a non-recursive *body*
parameterized over a record of the mutually recursive entry points
(`CoreFns`) and polymorphic in the monad.  All recursion is routed
through the record — bodies never call themselves, and the few helpers
that do recurse (`iotaCerts`, `defEqList`, `structEtaProjCerts`) do so
structurally on a list.  Fuel lives only in the *knots* that tie the
record: the pure knot (`ConLeche.Kernel.TypeChecker`) instantiates the
bodies at `CheckM` and is the verification's subject; the cached knot
(`ConLeche.Cached.CoreC`) instantiates them over the cached
representation with the memo caches and is what the checker executes.
(A third, *memoized* knot over plain `Expr` — `Kernel/TypeCheckerC.lean`
— was the executed one until the cached tier replaced it; it and its
call discipline went at task #221.)  A refinement
bridge relates the two (see DESIGN.md).

The reduction loop follows the official kernel (`whnfCore` never
delta-unfolds; `whnf` iterates `whnfCore → reduceNat → unfold one
definition`), and definitional equality starts with the syntactic fast
path and tries proof irrelevance before structural congruence.
Inference re-checks the application argument and the λ-annotation: the
soundness claims re-derive their membership slots from those checks at
their own fuel.  The official kernel's *infer-only* mode is deferred
until the refinement bridge's fuel-determinism machinery lands
(DESIGN.md).

Verification: `ConLeche.Model.*` and `ConLeche.Verify.*` (claims),
`ConLeche.Verify.*` (inversions), both stated against the bodies with
hypotheses about the record and discharged by one induction at the
knot.

The core's **fuel-free helpers** — everything a body reads that
mentions no monad, no record and no fuel (`unfoldDefinition`, the
literal guards, the certified `Nat` operations' tables, the η
fabrications, the install-time rule bits, `betaGateFires`, …) — live
in `ConLeche/Kernel/CoreDefs.lean` since task #305 (prep) and are
re-exported here, so that a relational description of the core's
moves can name them without importing the bodies.
-/

namespace ConLeche

/-- **The verdict of a failure, everywhere in the binary** — the one
error type the whole accept path reports (task #295): the kernel's
steps, the fold, and the frontend's parse and prelude alike.  The
three cases are the three verdicts the driver exits with
(`CheckError.exitCode`, `Main.lean`): 2 declined, 1 rejected, 3 an
error of unclear cause or a malformed input.

Where a failure has a POSITION the type is `CheckError × Nat`, and the
`Nat` is read in the step's own unit: the input's LINE number in the
frontend (`ConLeche/Frontend/Export.lean`; 0 where no line is meant,
as in the size guard, which refuses the input before reading it) and
the record's position in the list the fold folds
(`ConLeche.Cached.checkDecls`).  The two are in the same type because
the driver chains the steps, and the main corollary states that chain
(`ConLeche/MainTheorem.lean`). -/
inductive CheckError where
  | notImplemented (what : String)
  | invalid (msg : String)
  | internal (msg : String)
  deriving Repr

instance : ToString CheckError where
  toString
    | .notImplemented what => s!"not implemented yet: {what}"
    | .invalid msg => s!"invalid: {msg}"
    | .internal msg => s!"internal error: {msg}"

abbrev CheckM := Except CheckError

/-- **The verdict at a constant the environment does not know.**

`sorryAx` is the one axiom the checker tolerates as a *declaration*
and installs nothing for (`sorryAxName`,
`ConLeche/Kernel/Basis/Names.lean`): an export declares it whenever
its module mentions `sorry`, so the record is skipped and the stream
goes on — but there is no set model for it, so a *use* is a
positively detected unsupported feature and the run DECLINES, at the
record that uses it.  Every other unresolved name is a malformed
stream: a REJECT, with the message unchanged.

This is the choke point, because the guard that keeps unresolved
constants out of stored terms (`Expr.constsResolve`) runs *after* the
annotation pass, and annotation infers every binder domain's sort —
so a `sorryAx` in a domain reaches inference first.  Its companion
`unresolvedConstsError` (`ConLeche/Kernel/CheckerBase.lean`) decides
the same question at the guard, for the `sorryAx` occurrences
inference never reaches. -/
def unknownConstError (n : Name) : CheckError :=
  if n = sorryAxName then .notImplemented "use of the sorryAx axiom"
  else .invalid s!"unknown constant {n}"

/-- The record of mutually recursive core entry points.  `whnfCore`
computes a head normal form without delta; `whnf` is the full reduction
loop; `infer` is type inference;
`defeq` is definitional equality; `annotate` computes binder
annotations (and is the one place typing is checked). -/
structure CoreFns (m : Type → Type u) where
  whnfCore : Nat → Expr → m Expr
  whnf : Nat → Expr → m Expr
  infer : Nat → Expr → m Expr
  defeq : Nat → Expr → Expr → m Bool
  annotate : Nat → Expr → m Expr
  /-- Type inference at the **infer-only grade** (task #170): the
  official kernel's `infer_type_core(e, infer_only = true)`, the entry
  every *internal* inference call site uses — a subject that already
  carries a validated annotation invariant (`WellDenotedV` in the P
  claims) is re-inferred without re-establishing it.  The knot decides
  the grade's meaning per mode: at a gate-off mode (`μ.betaGate =
  false`) this is the full `infer`, verbatim (the flag is ignored,
  task #170's R clause); at the gated mode (`.verified`, the P core)
  it is the io body, whose application clause skips the per-argument
  certificate at a `.never` binder under the graph-regime license
  (`ConLeche/Model/IOLicense.lean`).  The **shipped** trusted core
  selects the io body too (`CheckMode.ioGate` is `true` at both
  modes, the licence ruling of 2026-09-06); this mode-parametric
  spelling is not the thing that ships, so `μ.betaGate` here stays the
  P tier's own bit, and the two agree at `.verified`. -/
  inferIO : Nat → Expr → m Expr

/-- The **io-grade view** of a core record: the record whose full-grade
`infer` slot is the io slot, so that a body written against `r.infer`
recurses at the io grade when handed `r.ioView`.  This is how the io
inference body propagates its own grade (official: `infer_type_core`
passes `infer_only` down) without a textual twin. -/
def CoreFns.ioView {m : Type → Type u} (r : CoreFns m) : CoreFns m :=
  { r with infer := r.inferIO }

section Bodies

variable {m : Type → Type} [Monad m] [MonadExceptOf CheckError m]

/- The three-mode setting (task #147): definitions below that mention
`mode` take it as their first explicit argument (after the monad
instances).  Only the seven TT-lane check sites branch on it, through
`CheckMode.ttChecks`; at `.ttModel` the checker is exactly the pre-#147
one, at `.verified` (the default) the seven checks are skipped. -/
variable (mode : CheckMode)

/-- Lift a fuel-style partial result; `none` is an internal error. -/
def liftFueled (what : String) : Option α → m α
  | some a => pure a
  | none => throw (.internal s!"fuel exhausted: {what}")

/-- Literal acceleration (the official kernel's `reduceNat`, run in the
`whnf` loop *before* delta-unfolding): pack `Nat.succ` applied to a
literal back into a literal.  Binary operations on literal arguments
are added with the verified fast-path capabilities (see DESIGN.md);
until then only the constructor packing reduces. -/
def reduceNat (r : CoreFns m) (env : Env) (depth : Nat) (e : Expr) :
    m (Option Expr) := do
  match e with
  | .app (.const c []) a =>
    if c = natSuccName ∧ natLitSupported env then
      -- the argument is reduced first (as for the operations below):
      -- literals reach `succ` wrapped in `OfNat`/instance towers, and a
      -- missed packing here defeats the binary fast paths downstream,
      -- which then delta-grind the `brecOn` below-tower unarily
      match rawNatLit? (← r.whnf depth a) with
      | some n => pure (some (.lit (.natVal (n + 1))))
      | none => pure none
    -- (the audit's S1: the `Nat.pred` and `Nat.log2` literal fast paths
    -- are gone — official `reduce_nat` (`type_checker.cpp:639-668`) has
    -- `Nat.succ` and the fourteen binary operations, nothing else.
    -- `Nat.pred` stays a certified structural operation because
    -- `Nat.sub`'s recurrence names it; `Nat.log2` is gone entirely)
    else pure none
  | .app (.app (.const c []) a) b =>
    if (c = natAddName ∨ c = natSubName ∨ c = natMulName ∨
        c = natPowName ∨ c = natBeqName ∨ c = natBleName ∨
        c = natDivName ∨ c = natModName ∨ c = natGcdName ∨
        c = natLandName ∨ c = natLorName ∨ c = natXorName ∨
        c = natShiftLeftName ∨ c = natShiftRightName) ∧
        natOpStored env c = true then
      -- Official `reduce_bin_nat_op` (`type_checker.cpp:606-614`):
      -- the FIRST argument is head-normalised and, unless it is a
      -- literal, the step fails WITHOUT touching the second.  The
      -- former two-scrutinee `match` whnf'd both up front — a cost
      -- divergence (DESIGN.md "THE DIVERGENCE AUDIT", D15): on
      -- `Nat.add o (slow n)` with `o` opaque it evaluated `slow n`
      -- where official never does (fuel death at `n = 80000`; the fixture).
      match rawNatLit? (← r.whnf depth a) with
      | some n₁ =>
        match rawNatLit? (← r.whnf depth b) with
        | some n₂ => pure (natOpResult c n₁ n₂)
        | none => pure none
      | none => pure none
    else if natOpWfNames.contains c ∧ natLitSupported env then
      match rawNatLit? (← r.whnf depth a) with
      | some _ =>
        match rawNatLit? (← r.whnf depth b) with
        | some _ => throw (.notImplemented
            s!"native Nat computation on literals ({c})")
        | none => pure none
      | none => pure none
    else pure none
  | _ => pure none

/-- Certify a spine against a recursor telescope: each argument's
inferred type is defeq to the corresponding (instantiated) domain.
This is what hands the soundness proof the memberships the iota
equations need, at every level assignment.

**The ι-slot licence** (the ι batch, 2026-09-05; DESIGN.md "THE ι
AUDIT" §9.1): at a *licensed* walk (`lic = true`, set only by
`iotaRec`'s two calls — the fire-time telescope runs, where the redex
is a subterm of the subject and carries its own `WellDenoted` app slots)
a slot whose `∀`-binder datum is `.never` is skipped: the membership
the run would establish follows from the slot and the head's
membership in the telescope's reading (`io_domain_transfer`,
`Model/IOLicense.lean`, consumed by `Certs.skip_sound` in
`Model/Rules/CertsSound.lean`).  The rescue's
synthetic-spine certifications (`majorToCtor`, the η/unit/K
fabrications) run at `lic = false`: a fabricated spine is not a
subterm of the subject and its grading is *produced* by this very
run, so gating it would be circular.  The fence is
`io_squash_no_transfer`'s witness: at a possibly-zero datum the skip
is unsound model-class-wide, so the licensed fragment is exactly
`.never`. -/
def iotaCerts (r : CoreFns m) (env : Env) (depth : Nat) (lic : Bool) :
    Expr → List Expr → m Bool
  | _, [] => pure true
  | .forallE ty body mb, arg :: rest =>
    if lic && mb.pw.isNever then
      iotaCerts r env depth lic (body.instantiate1 arg) rest
    else do
      -- task #172 B4: the spine certificate's inference at the io grade
      let ta ← r.inferIO depth arg
      if ← r.defeq depth ta ty then
        iotaCerts r env depth lic (body.instantiate1 arg) rest
      else pure false
  | _, _ :: _ => pure false

/-- Pairwise definitional equality of two spines (used to check a
major's constructor parameters against the recursor's). -/
def defEqList (r : CoreFns m) (env : Env) (depth : Nat) :
    List Expr → List Expr → m Bool
  | [], [] => pure true
  | a :: as, b :: bs => do
    if ← r.defeq depth a b then
      defEqList r env depth as bs
    else pure false
  | _, _ => pure false

/-- The canonical-index comparison of a firing ι redex (the ι batch,
2026-09-05).  Where the recursor has indices (`rP < mI`) the residual of
the constructor's telescope `tyCtor` along the major's spine `margs`
must agree, past the `cnP` parameters, with the recursor's index
arguments `idx` — the model's iota equation only speaks about the
canonical indices.  At `mI = rP` there is nothing to compare (the law's
`IotaIndexPin` is discharged by `Or.inl rfl`) and the block is
skipped.  The residual-head test that once stood beside the comparison
(`stripPis` + "the body's head is a constant") was consumed by nothing
in the P lane and is gone. -/
def iotaIndexOk (r : CoreFns m) (env : Env) (depth : Nat) (mI rP cnP : Nat)
    (tyCtor : Expr) (margs idx : List Expr) : m Bool :=
  if mI = rP then pure true
  else
    match piResidual tyCtor margs with
    | some residual => defEqList r env depth (residual.getAppArgs.drop cnP) idx
    | none => pure false

/-- Proof irrelevance certification: both sides' types whnf to the
basis unit type (all of whose inhabitants are the proof point in the
model), or both sides' types' *sorts* are `Prop`.  In the model
everything inhabiting a proposition is the proof point, so any two such
terms are equal — no common-type check is needed: soundness holds
without it, and the annotation-first discipline (every subterm is
checked before definitional equality compares it; congruence compares
argument pairs only after the earlier arguments matched) makes a
heterogeneous comparison unreachable, so the official kernel's check is
implied (see DESIGN.md, design-review triage). -/
def proofIrrel (r : CoreFns m) (env : Env) (depth : Nat) (a b : Expr) :
    m Bool := do
  -- task #172 B4: every inference here is at the io grade (official's
  -- is_def_eq_proof_irrel runs infer_type — always infer_only)
  let ta ← r.inferIO depth a
  if isUnitLikeTy env (← r.whnf depth ta) then
    let tb ← r.inferIO depth b
    if isUnitLikeTy env (← r.whnf depth tb) then
      pure true
    else
      pure false
  else
    match ← r.whnf depth (← r.inferIO depth ta) with
    | .sort uT =>
      let okA ← liftFueled "level comparison" (Level.isEquiv uT .zero)
      let tb ← r.inferIO depth b
      match ← r.whnf depth (← r.inferIO depth tb) with
      | .sort vT =>
        let okB ← liftFueled "level comparison" (Level.isEquiv vT .zero)
        pure (okA && okB)
      | _ => pure false
    | _ => pure false

/-- **The hoisted proof-irrelevance test** (task #168, Option U): the
`Prop` branch of `proofIrrel` alone — official's
`is_def_eq_proof_irrel` has no unit-like branch; that test lives in
`stuckIrrel` (official's `is_def_eq_unit_like`, the last test of
`is_def_eq_core`), which `proofIrrel` still serves.

Before the io inferences, the head-symbol readers decide both fast
arms, **in both modes** (user ruling, 2026-09-06: the fast readers are
part of the real checker, and the trusted mode is the real checker
with certification-only work omitted — a reader that replaces
inference is not certification-only work).  The **"not a proof" arm**:
a side whose annotation datum says "not a proposition" refuses the
shortcut outright (`notProofFast`, `ConLeche/Kernel/PropRead.lean`).
Refusing is always sound — the P row is stated at `.ok true` — and the
arm's obligation is *agreement* with the slow path, recorded by the
landing census (DESIGN.md, task #168: 0 disagreements in 7.5 M calls).
The **"yes" arm** (`isProofFast` on both sides → `true`) is the
squash-regime licence, stage 3 of the same design
(`prf_of_isProofFast`, `ConLeche/Model/Rules/DefEqSoundKit.lean`), which the
verified mode's `DefEq.proofFast` rule consumes; the trusted mode is unverified and
inherits the arm without a row, as it inherits every other body. -/
def propIrrel (r : CoreFns m) (env : Env) (depth : Nat) (a b : Expr) :
    m Bool := do
  if notProofFast env.find? a || notProofFast env.find? b then
    pure false
  else if isProofFast env.find? a && isProofFast env.find? b then
    -- the yes arm (task #168 stage 3): both heads' validated data say
    -- "a proposition at every valuation" — the squash-regime licence
    -- (`prf_of_isProofFast`, `ConLeche/Model/Rules/DefEqSoundKit.lean`)
    pure true
  else
  -- task #172 B4: every inference here is at the io grade
  let ta ← r.inferIO depth a
  match ← r.whnf depth (← r.inferIO depth ta) with
  | .sort uT =>
    let okA ← liftFueled "level comparison" (Level.isEquiv uT .zero)
    let tb ← r.inferIO depth b
    match ← r.whnf depth (← r.inferIO depth tb) with
    | .sort vT =>
      let okB ← liftFueled "level comparison" (Level.isEquiv vT .zero)
      pure (okA && okB)
    | _ => pure false
  | _ => pure false

/-- The per-projection telescope certificates of a structural eta
certification at a **projection-function** slot family (the modeled
path's): for every field index, the installed projection function's
telescope is certified against the type's arguments and the stuck
side.  A tower-backed family (the direct install's table, task #175
S1) has no per-field telescope and needs no certificate: its η law
(`TowerEtaLaw`) is keyed on the family's typing of the stuck side,
which the caller already holds. -/
def structEtaProjCerts (r : CoreFns m) (env : Env) (depth : Nat)
    (T : Name) (us' : List Level) (targs : List Expr) (b : Expr)
    (lpsT : List Name) : List Nat → m Bool
  | [] => pure true
  | i :: rest => do
    match env.find? (projFnName T i) with
    | some (.recInfo cvp _ _ _) =>
      if cvp.levelParams = lpsT ∧
          (cvp.type.stripPis (targs.length + 1)).isSome = true then
        if ← iotaCerts r env depth false
            (cvp.type.instantiateLevelParams cvp.levelParams us')
            (targs ++ [b]) then
          structEtaProjCerts r env depth T us' targs b lpsT rest
        else pure false
      else pure false
    | _ => pure false

/-- The structure-eta certificate against a *given* weak-head-normal
type of the stuck side (callers that already reduced it — the
stuck-major rescue — pass their own copy, so the certificate's facts
are in terms of that expression). -/
def structEtaCertWith (r : CoreFns m) (env : Env) (depth : Nat)
    (a b wtb : Expr) : m Bool := do
  match a.getAppFn with
  | .const c us =>
    match env.find? c with
    | some (.ctorInfo cvc cnP cnF) =>
      if a.getAppArgs.length = cnP + cnF then
        match wtb.getAppFn with
        | .const T us' =>
          match env.find? T with
          | some (.indInfo cvT caps) =>
            if caps.eta = true ∧ caps.etaCtor = c ∧
                reservedBasisNames.contains T = false ∧
                reservedBasisNames.contains c = false ∧
                wtb.getAppArgs.length = caps.etaParams ∧
                us'.length = cvT.levelParams.length ∧
                cvc.levelParams = cvT.levelParams ∧
                -- the former's telescope arity
                -- `(cvT.type.stripPis caps.etaParams).isSome` is
                -- `EnvWF`'s `IndCapsWF` clause: established at the
                -- block's install, read by the η row from the
                -- invariant
                -- the slot discipline (task #175 W4c): one entry kind
                (towerSlotsAll env T caps.etaFields ||
                  recSlotsAll env T caps.etaFields) = true then
              if ← liftFueled "level comparison"
                  (Level.isEquivList us us') then
                if ← iotaCerts r env depth false
                    (cvT.type.instantiateLevelParams cvT.levelParams
                      us') wtb.getAppArgs then
                  -- the per-slot certificates are the projection-function
                  -- kind's; a tabled family has none (task #175 S1)
                  if ← (if towerSlotsAll env T caps.etaFields then pure true
                      else structEtaProjCerts r env depth T us'
                        wtb.getAppArgs b cvT.levelParams
                        (List.range caps.etaFields)) then
                    if ← defEqList r env depth
                        (a.getAppArgs.take caps.etaParams) wtb.getAppArgs then
                      -- synthetic-spine certification (task #137): the
                      -- fabricated constructor application is certified
                      -- against the constructor's own telescope, here
                      -- rather than at the callers, so that both
                      -- consumers get it (`majorToCtor`'s eta rescue ran
                      -- it already, task #71; `defeq`'s `structEtaCert`
                      -- did not).  TT-lane check (task #147): skipped
                      -- unless `mode.ttChecks`.
                      if ← (if mode.ttChecks then
                          iotaCerts r env depth false
                            (cvc.type.instantiateLevelParams
                              cvc.levelParams us)
                            (wtb.getAppArgs ++
                              etaProjs env T us' wtb.getAppArgs b
                                caps.etaFields)
                        else pure true) then
                        defEqList r env depth
                          (a.getAppArgs.drop caps.etaParams)
                          (etaProjs env T us' wtb.getAppArgs b
                            caps.etaFields)
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

/-- Structural eta certification for a stored eta-capable structure:
`a` is a fully applied constructor of a structure whose recorded
capabilities include eta, `b` inhabits that structure type, the
constructor's parameters are the type's arguments, and every field is
the corresponding installed projection function applied to `b`.  The
type application is additionally certified against the type former's
telescope (the memberships the stored eta law consumes).  The
parameter and field counts the certificate works at are the
capability RECORD's, which is what the stored law speaks; the
constructor's own counts gate the redex's shape and nothing else
(`etaCtorShape`). -/
def structEtaCert (r : CoreFns m) (env : Env) (depth : Nat) (a b : Expr) :
    m Bool := do
  -- The constructor-shape test FIRST (the divergence audit's D13):
  -- official `try_eta_struct_core` (`type_checker.cpp:824-829`) reads
  -- `s`'s head and arity syntactically and infers nothing unless they
  -- fit; ours inferred and whnf'd `b`'s type on every stuck pair, both
  -- directions, before `structEtaCertWith` looked at `a`'s head.
  if etaCtorShape env a then
    -- task #172 B4: io grade
    let tb ← r.inferIO depth b
    let wtb ← r.whnf depth tb
    structEtaCertWith mode r env depth a b wtb
  else pure false

/-- Unit-likeness certification: `a` and `b` inhabit the same stored
unit-like family (the types are definitionally equal and the type
application is certified against the family's telescope), so their
values coincide by the stored unit law. -/
def structUnitCert (r : CoreFns m) (env : Env) (depth : Nat) (a b : Expr) :
    m Bool := do
  -- task #172 B4: io grade
  let ta ← r.inferIO depth a
  let wta ← r.whnf depth ta
  match wta.getAppFn with
  | .const T us' =>
    match env.find? T with
    | some (.indInfo cvT caps) =>
      if caps.unitlike = true ∧
          reservedBasisNames.contains T = false ∧
          wta.getAppArgs.length = caps.unitParams ∧
          -- `(cvT.type.stripPis caps.unitParams).isSome` is `EnvWF`'s
          -- `IndCapsWF` clause, established at the block's install
          us'.length = cvT.levelParams.length then
        let tb ← r.inferIO depth b
        let wtb ← r.whnf depth tb
        if ← r.defeq depth wta wtb then
          iotaCerts r env depth false
            (cvT.type.instantiateLevelParams cvT.levelParams us')
            wta.getAppArgs
        else pure false
      else pure false
    | _ => pure false
  | _ => pure false

/-- Eta certification for a one-sided λ against a stuck term `b`: `b`'s
type whnfs to a `∀` whose domain is defeq to the λ's, and the λ's body
is pointwise the application of `b`.  The λ is then `b`'s eta-expansion
(soundness: `SetTheory.lam_eta`). -/
def etaCert (mode : CheckMode) (r : CoreFns m) (_env : Env) (depth : Nat)
    (ty₁ body₁ : Expr) (m₁ : BinderMeta) (b : Expr) :
    m Bool := do
  -- task #172 B4: io grade
  let tb ← r.inferIO depth b
  match ← r.whnf depth tb with
  | .forallE ty₂ _ m₂ =>
    -- Task #161: the λ's prop-ness annotation must agree with the
    -- product it η-expands (`lamR_eta`'s regime agreement) — checked
    -- LAST, like the defeq binder arms, so a mismatch fires only on
    -- an otherwise-successful η certification.  (This is the
    -- validated successor of the cod-agreement comparison task #100
    -- stage 6 deleted.)
    if ← r.defeq depth ty₂ ty₁ then
      unless ← r.defeq (depth + 1)
          (body₁.instantiate1 (.fvar depth ty₁))
          (.app b (.fvar depth ty₁)) do return false
      if mode.verifiedChecks && !(m₁.pw == m₂.pw) then
        throw (.notImplemented "sort-annotation mismatch (eta)")
      pure true
    else pure false
  | _ => pure false

/-- The fallback for structurally distinct stuck terms: structural eta
in either direction, unit-likeness, else proof irrelevance.  (The
pinned-pair certificate `pairEtaCert` that used to lead is retired
with the `PSigma'` pin, task #175 W6: the pair is an ordinary direct
structure and `structEtaCert` covers it.) -/
def stuckIrrel (r : CoreFns m) (env : Env) (depth : Nat) (a b : Expr) :
    m Bool := do
  if ← structEtaCert mode r env depth a b then pure true
  else if ← structEtaCert mode r env depth b a then pure true
  else if ← structUnitCert r env depth a b then pure true
  else proofIrrel r env depth a b

/-- Stuck-major rescue (`to_cnstr_when_K` and `to_cnstr_when_structure`
in the official kernel): a recursor's major premise that does not whnf
to a constructor application may still be *replaced* by one.  For a
K-flagged inductive proposition the parameters-only application of the
single constructor is fabricated from the major's type and certified by
proof irrelevance (in the model both are the proof point); for an
eta-capable structure the constructor of the major's projections is
fabricated and certified by the structure-eta certificate (in the model
both are the tuple of the major's components); for the pinned `And` —
a proposition, which official never η-rescues — the constructor of the
major's projections is fabricated and certified by proof irrelevance
(the `And` branch below).  An uncertified major stays put — sound, the
reduction simply stays stuck. -/
def majorToCtor (r : CoreFns m) (env : Env) (depth : Nat)
    (_recName : Name) (rules : List RecRule) (major : Expr) : m Expr := do
  -- cheap syntactic gates before any inference: a rescue needs a
  -- single-rule recursor whose rule carries the matching install-time
  -- rescue bit (`RecRule.k`/`RecRule.eta`)
  if isCtorApp env major then pure major else
  match rules with
  | [rl] =>
    match env.find? rl.ctor with
    | some (.ctorInfo cvj cnP _cnF) =>
      match (cvj.type.piResult).getAppFn with
      | .const T _ =>
        match env.find? T with
        | some (.indInfo cvT caps) =>
          if rl.k = true then
            -- task #172 B4: io grade (lean4lean toCtorWhenK inferType)
            let tmaj ← r.whnf depth (← r.inferIO depth major)
            match tmaj.getAppFn with
            | .const T' ust =>
              if T' = T ∧ cvj.levelParams.length = ust.length then
                -- no constructor-telescope arity pin: the fabrication
                -- is typed by `iotaCerts` below, and the P row
                -- (`majorToCtorFueled_step`) consumes no such fact
                if cnP ≤ tmaj.getAppArgs.length then
                  let fab := Expr.mkAppN (.const rl.ctor ust)
                    (tmaj.getAppArgs.take cnP)
                  -- scope guard (cf. `annotateProjElim`): scoping of
                  -- the fabricated major is checked syntactically,
                  -- keeping its verification local
                  if fab.wscopedB depth && fab.looseBVarsBounded 0 &&
                      fab.fvarLeaves.all
                        (fun l => major.fvarLeaves.contains l) then
                    -- Synthetic-spine certification (task #71): a
                    -- fabricated constructor spine has no annotated
                    -- application chain for the gated fire-path
                    -- certificates to recover memberships from, so
                    -- the *ungated* telescope certificate runs here,
                    -- relocated from the fire path.
                    if ← iotaCerts r env depth false
                        (cvj.type.instantiateLevelParams
                          cvj.levelParams ust)
                        (tmaj.getAppArgs.take cnP) then
                      -- The official `to_cnstr_when_K` type check on
                      -- the fabrication: the constructor
                      -- application's type must be defeq to the
                      -- major's (for `Eq` this is the endpoint
                      -- condition — `Eq.refl a : Eq a a` against the
                      -- major's `Eq a b` forces `a ≡ b`).  A
                      -- reference-kernel check, kept independently of
                      -- the per-fire iota certificates (during the
                      -- gated era of tasks #49/#71 it was load-bearing
                      -- on its own — arena bad/098_ruleKbad fires at
                      -- `Eq.rec.{3,3}`).  `proofIrrel` stays as the
                      -- soundness certificate (in the model both
                      -- sides are the proof point).
                      if ← r.defeq depth tmaj (← r.inferIO depth fab) then
                        if ← proofIrrel r env depth fab major then
                          pure fab
                        else pure major
                      else pure major
                    else pure major
                  else pure major
                else pure major
              else pure major
            | _ => pure major
          else if rl.eta = true then
            let tmaj ← r.whnf depth (← r.inferIO depth major)
            match tmaj.getAppFn with
            | .const T' ust =>
              -- The official kernel does not eta-rescue propositional
              -- structures (`to_cnstr_when_structure` requires the
              -- structure's result sort to be provably nonzero).  The
              -- test is the *instantiated* one (task #61): a static
              -- `piResultIsProp cvT.type = false` passes a parametric
              -- `Sort u` that a `Prop` instantiation collapses, which
              -- is exactly the case the guard exists for.
              if T' = T ∧ tmaj.getAppArgs.length = caps.etaParams ∧
                  ust.length = cvT.levelParams.length ∧
                  capsNeverZero cvT.levelParams ust caps = true then
                -- no constructor-telescope arity pin, as in the K
                -- branch, and no level-count pin: the η bit is set
                -- only at a constructor stored with the former's own
                -- level parameters (`RecCtorsStored`), which the
                -- fabrication's levels are those of
                let fab := Expr.mkAppN (.const caps.etaCtor ust)
                    (etaFabArgsE env T ust tmaj.getAppArgs major
                      caps.etaFields)
                -- scope guard, as in the K branch
                if fab.wscopedB depth && fab.looseBVarsBounded 0 &&
                    fab.fvarLeaves.all
                      (fun l => major.fvarLeaves.contains l) then
                  -- synthetic-spine certification, as in the K
                  -- branch (task #71)
                  if ← iotaCerts r env depth false
                      (cvj.type.instantiateLevelParams
                        cvj.levelParams ust)
                      (etaFabArgsE env T ust tmaj.getAppArgs major
                        caps.etaFields) then
                    if ← structEtaCertWith mode r env depth fab major
                        tmaj then
                      pure fab
                    -- 0-field rescue for the pinned basis `PUnit`
                    -- (the generic certificate excludes reserved
                    -- names): the fabrication is the bare
                    -- constructor, certified by proof
                    -- irrelevance's unit-likeness branch; the
                    -- instantiated non-Prop test is already in the
                    -- branch guard above
                    else if caps.etaFields = 0 then
                      if ← proofIrrel r env depth fab major then
                        pure fab
                      else pure major
                    else pure major
                  else pure major
                else pure major
              else pure major
            | _ => pure major
          else if T = andName then
            -- THE `And`-ONLY η RESCUE (user ruling: `And` and nothing
            -- else — "this is a hack and we want its blast radius
            -- limited").  `And.rec F h` at a stuck PROOF `h` (a theorem
            -- is opaque to reduction) fires through the fabrication
            -- `And.intro a b (.proj And 0 h) (.proj And 1 h)`,
            -- certified the K branch's way: the synthetic spine against
            -- the constructor's telescope (which types the two `.proj`
            -- nodes through `And`'s projection table), the
            -- fabrication's type against the major's, and proof
            -- irrelevance — sound because in the model every proof is
            -- the point.  Official does not η-rescue a proposition
            -- (`to_cnstr_when_structure` requires a never-zero sort),
            -- so this is an accept-superset there, reported per the
            -- `proofIrrel` ruling; it WORKS AROUND the absence of
            -- https://github.com/leanprover/lean4/pull/14925 (upstream
            -- builds `casesOn`/`recOn` of such a proposition from
            -- projections, so no `And.rec` on a proof is emitted), on
            -- top of opaque theorems, which ANTICIPATE
            -- https://github.com/leanprover/lean4/pull/14896.
            let tmaj ← r.whnf depth (← r.inferIO depth major)
            match tmaj.getAppFn with
            | .const T' ust =>
              if T' = T ∧ tmaj.getAppArgs.length = cnP ∧
                  cvj.levelParams.length = ust.length ∧
                  andRescueSlots env rl.ctor cnP ust = true then
                let fab := Expr.mkAppN (.const rl.ctor ust)
                  (tmaj.getAppArgs ++ [.proj T 0 major, .proj T 1 major])
                -- scope guard, as in the K branch
                if fab.wscopedB depth && fab.looseBVarsBounded 0 &&
                    fab.fvarLeaves.all
                      (fun l => major.fvarLeaves.contains l) then
                  -- synthetic-spine certification, as in the K branch
                  if ← iotaCerts r env depth false
                      (cvj.type.instantiateLevelParams
                        cvj.levelParams ust)
                      (tmaj.getAppArgs ++ [.proj T 0 major, .proj T 1 major]) then
                    -- the fabrication's type against the major's, then
                    -- proof irrelevance as the soundness certificate
                    if ← r.defeq depth tmaj (← r.inferIO depth fab) then
                      if ← proofIrrel r env depth fab major then
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

/-- Convert a literal major premise to constructor form: a `Nat`
literal one layer (`litToCtorIfNat`); a `String` literal to its
*reduced* constructor form — the reference kernels re-reduce after
`strLitToConstructor` (lean4lean `Inductive/Reduce.lean`, nanoda
`str_lit_to_ctor_reducing`) since `String.ofList` is a definition, not
a constructor.  An unsupported literal passes through (stuck; sound,
and unreachable for annotated input). -/
def litMajorToCtor (r : CoreFns m) (env : Env) (depth : Nat) :
    Expr → m Expr
  | .lit (.strVal s) =>
    if strLitSupported env then r.whnf depth (strLitToConstructor s)
    else pure (.lit (.strVal s))
  | e => pure (litToCtorIfNat env e)

/-- Convert a string-literal projection scrutinee to its *reduced*
constructor form — the references' proj expansion site (official
`reduce_proj_core`, `type_checker.cpp:383-384`; lean4lean
`TypeChecker.lean` proj clause; nanoda `tc.rs` `reduce_proj`): the
expansion's head `String.ofList` is a definition, so the whnf grinds it
to the real `String.ofByteArray` constructor form.  Only `String`
literals — no reference touches other scrutinees here.  An unsupported
literal passes through (stuck; sound, and unreachable for annotated
input). -/
def projLitToCtor (r : CoreFns m) (env : Env) (depth : Nat) :
    Expr → m Expr
  | .lit (.strVal s) =>
    if strLitSupported env then r.whnf depth (strLitToConstructor s)
    else pure (.lit (.strVal s))
  | e => pure e

/-- The major premise's preparation before a rule fires, in the
official kernel's order (`inductive_reduce_rec`,
`src/kernel/inductive.cpp`; lean4lean `Inductive/Reduce.lean:66-72`):

* at a K-flagged recursor the K rescue (`to_ctor_when_K`) runs on the
  **raw** major — it reads only the major's *type* and fabricates the
  constructor from it — and only then is the major head-normalized
  (and its literal converted; a no-op on a proof, kept for the
  site-by-site mirror);
* elsewhere the major is head-normalized first, its literal
  converted, and the structure-eta rescue (`to_ctor_when_structure`)
  tried on the reduct.

The two rescues live in one function (`majorToCtor`); the K branch is
reachable exactly at `recRuleK`, the eta branch never is there (an
inductive proposition fails its provably-nonzero guard), so the split
below dispatches each to its official site and neither is attempted
twice.

Why the order matters (2026-09-06, the Mathlib `decide`-over-`Rat`
frontier): with the whnf *first*, an `Eq.rec` whose major is a
theorem application — `Eq.ndrec … (Int.decEq._proof_1 a b h)` with
`h := Nat.eq_of_beq_eq_true …`, the shape `instDecidableEqRat`'s
`h ▸` produces — delta-unfolds the proofs and iota-grinds
`Nat.eq_of_beq_eq_true`'s `Nat.brecOn` tower unarily down the
`604800` literal: one knot level per `succ`, fuel exhaustion.  The
official order fabricates `Eq.refl` from the type (`a ≡ b` by the
`Nat` literal fast paths) and never opens either proof. -/
def prepareMajor (r : CoreFns m) (env : Env) (depth : Nat)
    (recName : Name) (rules : List RecRule) (major : Expr) : m Expr := do
  if recRuleK rules then
    let majorK ← majorToCtor mode r env depth recName rules major
    let major₀ ← r.whnf depth majorK
    litMajorToCtor r env depth major₀
  else
    let major₀ ← r.whnf depth major
    let major₁ ← litMajorToCtor r env depth major₀
    majorToCtor mode r env depth recName rules major₁

/-- One iota step: the expression is a stored recursor applied to
exactly its telescope (params, motives, minors, indices, major), the
major premise whnfs to a fully applied constructor with a matching
rule (a literal major converts to constructor form — see
`litMajorToCtor` —, a
stuck major may be rescued — see `majorToCtor`), and the spine is
certified against the recursor's own (pinned, annotated) type with
`iotaCerts` (per-slot infer+defeq; task #100 de-gating retired the
possibly-Prop annotation gate of tasks #49/#71 — unsound-to-model
under the domain-relative collapse, DESIGN.md).  The
result is the rule's rhs applied to the non-index prefix and the
constructor's fields; over-application is handled by the outer app
recursion. -/
def iotaRec (r : CoreFns m) (env : Env) (depth : Nat) (e : Expr) :
    m (Option Expr) := do
  match e.getAppFn with
  | .const c us =>
    match env.find? c with
    | some (.recInfo cv mI rP rules) =>
      let args := e.getAppArgs
      -- checker change #9: the recursor's level arity, guarded as
      -- `unfoldDefinition` guards it (`Core.lean:174`).  The official
      -- kernel tests this immediately before instantiating the rule's
      -- RHS (`src/kernel/inductive.h:105`, present since v4.0.0);
      -- lean4lean does the same (`Inductive/Reduce.lean:98`) and
      -- nanoda's `subst_expr_levels` asserts it.  Without it
      -- `rl.rhs.instantiateLevelParams cv.levelParams us` can leak a
      -- level parameter the subject never had -- refuted concretely
      -- at `Interp/IotaArity.lean`.  Ungated: the reference has it
      -- unconditionally, so a mode gate would break parity.
      if args.length = mI + 1 ∧ us.length = cv.levelParams.length then
        -- the major's preparation (K rescue / whnf / literal / eta) in
        -- the official order — `prepareMajor`'s docstring
        let major ← prepareMajor mode r env depth c rules
          (args.getD mI (.bvar 0))
        match major.getAppFn with
        | .const cj usj =>
          match env.find? cj with
          | some (.ctorInfo cvj _ _) =>
            match rules.find? (fun r' => r'.ctor == cj) with
            | some rl =>
              let margs := major.getAppArgs
              -- the constructor's counts are read off the stored rule
              -- (install-computed); the defensive spine-length check
              -- stays
              if margs.length = rl.ctorParams + rl.nfields then
               -- A matched *inert* rule is a positive detection of an
               -- unsupported feature: the redex demands firing an
               -- uncertified nested-auxiliary rule (e.g.
               -- `Syntax.rec_1` on an `Array.mk` major with the
               -- nested certification absent).  Staying silently
               -- stuck would surface as a spurious *reject*
               -- downstream (defeq failure in the app rule), so
               -- decline here instead.
               if rl.fire = .inert then
                 throw (.notImplemented
                   "iota reduction over a nested auxiliary recursor rule")
               else
                -- The ι batch (2026-09-05): the two `stripPis` arity
                -- pins that stood here were an environment invariant
                -- re-checked per fire (every install route establishes
                -- them; the P lane bound and never used them) — deleted
                -- per the "invariants over runtime gates" ruling.
                --
                -- the constructor's levels and parameters must agree
                -- with the rule's comparands (canonical: the
                -- recursor's own instantiation and leading arguments;
                -- nested: the stored major-domain instantiations) —
                -- the firing mode was computed once at install
                -- (`Expr.recRulePlain` / the nested certification),
                -- never re-derived per fire
                if ← liftFueled "level comparison" (Level.isEquivList usj
                    (recFireComparands rl cv.levelParams us
                      cvj.levelParams args rP).1) then
                 -- the parameter comparison, run unless the rule is a
                 -- `.plain` one the installing route marked
                 -- `paramsBlind` (`RecRule.compareParams`)
                 if ← (if rl.compareParams then
                    defEqList r env depth (margs.take rl.ctorParams)
                      (recFireComparands rl cv.levelParams us
                        cvj.levelParams args rP).2
                    else pure true) then
                  -- the two telescope runs, *licensed* (`iotaCerts`'
                  -- docstring): the redex is a subterm of the subject.
                  -- The mode read is the β gate's accessor — the one
                  -- place a certificate-skip may read the validated
                  -- datum (`CheckMode.betaGate`'s docstring)
                  if ← iotaCerts r env depth mode.betaGate
                     (cv.type.instantiateLevelParams cv.levelParams us)
                     (args.take mI ++ [major]) then
                   if ← iotaCerts r env depth mode.betaGate
                      (cvj.type.instantiateLevelParams cvj.levelParams usj)
                      margs then
                    -- the recursor's index arguments must match the
                    -- constructor's canonical index tuple, where the
                    -- recursor has indices (`iotaIndexOk`)
                    if ← iotaIndexOk r env depth mI rP rl.ctorParams
                        (cvj.type.instantiateLevelParams cvj.levelParams usj)
                        margs ((args.take mI).drop rP) then
                      pure (some (Expr.mkAppN
                        (rl.rhs.instantiateLevelParams cv.levelParams us)
                        (args.take rP ++ margs.drop rl.ctorParams)))
                    else pure none
                   else pure none
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

/-- **The structural projection's certificate** (task #175 W6, the
squash-regime licence): the redex `proj_i (C p⃗ x⃗)` fires only after
its constructor spine is certified against `C`'s stored type at the
redex's own levels — `iotaCerts`, each argument's inferred type defeq
to its binder domain, the domains instantiated along the spine.  This
is what makes the rule sound-to-model at a squash instantiation: there
the constructor application is the point and so is every field
(every field of a non-`Prop`-declared family is a proposition where
the family is one, by the O5 bound; at a `Prop`-declared family the
fire guard says so of the projected field), and the certified fit is
what pins the selected argument to its domain — a grading alone pins
nothing at bit `0`.  In the graph regime the fit is redundant with
the application's grading, which the tower law consumes there.

History: until task #161 P9 the certificate ran six things (the two
sort legs and their comparisons, on top of the two `inferTypeCore`
runs); P9 cut it to the two runs (the pinned pair's row walked the
spine's typings out of the subject's own run, concretely at arity
four); W6 replaces the two runs by the one telescope certificate,
which is the same per-argument `inferIO` + `defeq` work the subject's
run performed inside `inferSpine`, and drops the field's separate
`inferIO`.  The official kernel's `reduce_proj` certifies nothing —
this is the F4 conformance residue, which the P lane's `ProjStep`
row consumes through `certs_teleLic`.  The spine is a subterm of the
subject, so the certificate is *licensed* like the ι slot's
(`iotaCerts`' docstring): at the verified P mode a `.never` binder's
certificate is skipped — every field binder of an ordinary `structure`
— which is the io skip the retired two-run certificate had through
`inferSpine`. -/
def projCert (r : CoreFns m) (env : Env) (depth : Nat) (lic : Bool)
    (c : Name) (us : List Level) (args : List Expr) : m Bool := do
  match env.find? c with
  | some (.ctorInfo cvC _ _) =>
    iotaCerts r env depth lic
      (cvC.type.instantiateLevelParams cvC.levelParams us) args
  | _ => pure false

/-- **The fire certificate as the mode runs it** (parity mirrors
official, 2026-09-06).  The P core (`verified = true`) certifies the
constructor spine (`projCert`, licensed by the mode's β gate) — the
model's licence for the fire at a squash instantiation.  The parity
core is the official kernel's: `reduce_proj` reduces every
constructor redex with no certificate (`type_checker.cpp`), so at
`verified = false` no certificate runs and the rule fires
unconditionally.  The trusted lane stays an accept-superset of the P
lane, which is all the agreement floor
(`Verify/Cached/AgreeFloor.lean`) asks of it. -/
def projCertAt (r : CoreFns m) (env : Env) (depth : Nat) (verified lic : Bool)
    (c : Name) (us : List Level) (args : List Expr) : m Bool :=
  if verified then projCert r env depth lic c us args else pure true

/-- The head-normalization body: beta (with the per-redex argument
certificate, unconditional since the task-#100 de-gating), iota (with
the stuck-major machinery) and the native basis pair projection — but
**no delta**; unfolding happens in the `whnf` loop.  Values (sorts,
binders, constants, literals) return themselves. -/
def whnfCoreBody (r : CoreFns m) (env : Env) : Nat → Expr → m Expr :=
  fun depth e =>
    match e with
    | .sort u => pure (.sort u)
    | .fvar idx ty => pure (.fvar idx ty)
    | .forallE ty body bi => pure (.forallE ty body bi)
    | .lam ty body mb => pure (.lam ty body mb)
    | .const n us => pure (.const n us)
    | .lit l => pure (.lit l)
    | .app f a => do
      match ← r.whnfCore depth f with
      | .lam ty body mb => do
        -- Certify the argument against the domain before reducing
        -- (the soundness proof needs `⟦a⟧ ∈ ⟦ty⟧` at every level
        -- assignment).  An uncertified redex stays stuck — sound, and
        -- unreachable for well-typed input.  Task #100 de-gating: the
        -- former possibly-Prop annotation gate (skip the certificate
        -- at a provably nonzero codomain sort) is unsound-to-model
        -- under the domain-relative collapse (DESIGN.md), so the
        -- certificate now runs unconditionally — except at the task
        -- #161 β gate, which reads a *validated* annotation instead
        -- (`betaGateFires`, and only at `mode.betaGate`).
        if betaGateFires mode mb.pw then
          r.whnfCore depth (body.instantiate1 a)
        else do
          -- task #172 B4: the certificate's inference runs at the io
          -- grade — the argument sits inside a subject whose WellDenotedV
          -- the P claims carry (the user's criterion: WellDenoted is
          -- around), and official's whnf never infers here at all
          let ta ← r.inferIO depth a
          if ← r.defeq depth ta ty then
            r.whnfCore depth (body.instantiate1 a)
          else pure (.app (.lam ty body mb) a)
      | f' => do
        match ← iotaRec mode r env depth (.app f' a) with
        | some e'' => r.whnfCore depth e''
        | none => pure (.app f' a)
    | .proj sn i pe => do
      let e' ← r.whnf depth pe
      -- A string-literal scrutinee first expands to its reduced
      -- constructor form (`projLitToCtor`) — the references' proj
      -- expansion site.
      let e' ← projLitToCtor r env depth e'
      -- The structural rule `proj_i (ctor p⃗ x⃗) ↦ x_i`, driven by the
      -- projection table (never by basis names): the table entry for
      -- (structName, i) supplies the constructor, the counts, and the
      -- possibly-Prop level guard.
      match env.findProj? sn i with
      | some entry =>
        match e'.getAppFn with
        | .const c us =>
          let args := e'.getAppArgs
          if c = entry.ctor ∧ i < entry.numFields ∧
              args.length = entry.numParams + entry.numFields ∧
              us.length = entry.levelParams.length ∧
              entry.fireOk us = true then
            let arg := args.getD (entry.numParams + i) (.bvar 0)
            -- Certify the reduction at the verified mode: the
            -- constructor spine against the constructor's stored type
            -- (task #175 W6; see `projCert`).  Task #100 de-gating:
            -- the former nonzero-sort gate is unsound-to-model under
            -- the domain-relative collapse, so the certificate runs
            -- unconditionally there; the trusted mode runs none
            -- (`projCertAt`: official's `reduce_proj` certifies
            -- nothing).
            if ← projCertAt r env depth mode.verifiedChecks mode.betaGate c us args then
              r.whnfCore depth arg
            else pure (.proj sn i e')
          else pure (.proj sn i e')
        | _ => pure (.proj sn i e')
      | none => pure (.proj sn i e')
    | .letE _ _ _ =>
      -- **Unreachable by construction** (task #241).  The former ζ step
      -- (official kernel `whnf_core`, `case expr_kind::Let`; nanoda
      -- `whnf_no_unfolding_aux` `Let`; lean4lean `whnfCore'` `.letE`)
      -- is gone: every expression reduction sees is annotate output or
      -- stored rule data, and both are let-free, because
      -- `annotateBody`'s own `.letE` clause runs the official
      -- `infer_let` triple and returns the ζ *reduct* (task #217).
      -- A `letE` here is an invariant violation, not an unsupported
      -- feature, so it is `.internal` (exit 3), never a decline and
      -- never a silent accept.
      throw (.internal "whnfCore: `let` in an annotated expression")
    | .bvar _ =>
      throw (.notImplemented "whnf beyond the supported fragment")

/-- Step budget of the `whnfCore` head-normalization loop (task #106).
Beta, iota and projection steps are *iteration*: the interned
`whnfCoreLoopI` runs them on this budget instead of charging each step
to the shared recursion-depth budget (and to the native stack).  The
`Expr`-level specification below stays chained — the refinement bridge
reproduces a loop run by the chained recursion *at some knot fuel*
(`ConLeche/Verify/BetaSpine.lean`), so the specification and everything
above it are unchanged. -/
@[irreducible] def whnfCoreLoopFuel : Nat := 1000000

/-- Step budget of the `whnf` reduction loop (lean4lean's
`FuelConfig.whnf`, same value).  Literal-acceleration and delta steps
are *iteration*, not recursion: the official kernel's loop is a
`while (true)` and lean4lean's is a fixed-fuel local loop.  Task #106:
routing them through the knot instead charged every unfolding step to
the shared *recursion depth* budget (and to the native stack), so a
long-but-perfectly-ordinary unfolding chain exhausted `checkFuel`. -/
@[irreducible] def whnfLoopFuel : Nat := 100000

/-- One iteration of the reduction loop (the official kernel's `whnf`
body, lean4lean's `whnf'` loop body): head-normalize, try literal
acceleration, unfold one definition — and hand the reduct to the
loop's continuation `k`.  As everywhere in this module, the body never
calls itself: the continuation is abstracted exactly like the record
`r`, so every lemma about the body is proven once, with a hypothesis
about `k`, and the loop lemma is one induction on the budget. -/
def whnfStep (r : CoreFns m) (env : Env) (depth : Nat)
    (k : Expr → m Expr) (e : Expr) : m Expr := do
  let e₁ ← r.whnfCore depth e
  match ← reduceNat r env depth e₁ with
  | some e₂ => k e₂
  | none =>
    match unfoldDefinition env e₁ with
    | some e₂ => k e₂
    | none => pure e₁

/-- The reduction loop: iterate `whnfStep` on its own step budget, so
the whole chain costs one knot level however many steps it takes. -/
def whnfLoop (r : CoreFns m) (env : Env) (depth : Nat) :
    Nat → Expr → m Expr
  | 0, _ => throw (.internal "fuel exhausted: whnf loop")
  | n + 1, e => whnfStep r env depth (whnfLoop r env depth n) e

/-- The reduction loop's body: run `whnfLoop` at its own step budget. -/
def whnfBody (r : CoreFns m) (env : Env) : Nat → Expr → m Expr :=
  fun depth e => whnfLoop r env depth whnfLoopFuel e

/-- Ensure `e` (the type of some expression) is a sort, returning its
level. -/
def ensureSort (r : CoreFns m) (_env : Env) (depth : Nat) (e : Expr) :
    m Level := do
  match ← r.whnf depth e with
  | .sort u => pure u
  | _ => throw (.invalid "expected a sort")

/-- The inference body — **infer-only**: the application rule's
argument check ran once, in the annotation pass, and is trusted here
(so speculative inference inside reduction cannot reject). -/
def inferBody (r : CoreFns m) (env : Env) : Nat → Expr → m Expr :=
  fun depth e => do
    match e with
    | .sort u => pure (.sort (.succ u))
    | .fvar idx ty =>
      -- Scope check at the leaf of a traversal that happens anyway
      -- (O(1); never a fresh walk): a free variable must refer to an
      -- enclosing opened binder.  On raw (closed) input at depth 0 this
      -- rejects any `fvar` outright; internally the checker only opens
      -- variables below the ambient depth, so for disciplined calls the
      -- check always passes (and inference success implies
      -- well-scopedness, the base case of the cache discipline).
      if idx < depth then pure ty
      else throw (.invalid "free variable out of scope")
    | .const n us => do
      match env.find? n with
      | none => throw (unknownConstError n)
      | some ci =>
        -- a projection table is not a term (task #175 W4c): `.proj`
        -- nodes read it, no constant names it
        unless !ci.isTowerEntry do
          throw (.invalid s!"projection table entry used as a constant {n}")
        let cv := ci.toConstantVal
        unless us.length = cv.levelParams.length do
          throw (.invalid s!"incorrect number of universe levels for {n}")
        pure (cv.type.instantiateLevelParams cv.levelParams us)
    | .lit (.natVal _) => do
      if natLitSupported env then pure (.const natName [])
      else throw (.invalid "Nat literal without the Nat basis declarations")
    | .lit (.strVal _) => do
      -- a string literal types as `String` (the reference kernels'
      -- `Literal.typeName`); without the pinned support declarations
      -- this is a positively detected unsupported feature: decline
      if strLitSupported env then pure (.const stringName [])
      else throw (.notImplemented
        "string literals before the String support declarations")
    | .forallE ty body mb => do
      -- The ∀-formation rule, official-kernel style (task #100 stage 6):
      -- the codomain sort is *inferred* from the opened body.  Task
      -- #161: at the verified modes the node's prop-ness annotation is
      -- VALIDATED against the inferred codomain sort — the datum is
      -- canonical, so `==` decides zero-ness agreement, and a mismatch is a decline
      -- (a positively detected annotation the checker cannot certify),
      -- never a reject.  The annotation is never read by reduction.
      match ← r.whnf depth (← r.infer depth ty) with
      | .sort u => do
        let v ← ensureSort r env (depth + 1)
          (← r.infer (depth + 1) (body.instantiate1 (.fvar depth ty)))
        if mode.verifiedChecks then
          unless Level.zeronessOf v == mb.pw do
            throw (.notImplemented "sort-annotation mismatch (forall-cod)")
        pure (.sort (.imax u v))
      | _ => throw (.invalid "expected a sort")
    | .lam ty body mb => do
      -- The domain must be a type (and the model needs its
      -- interpretation defined), exactly as in the ∀ rule.
      match ← r.whnf depth (← r.infer depth ty) with
      | .sort _ => do
        let bt ← r.infer (depth + 1)
          (body.instantiate1 (.fvar depth ty))
        -- The *codomain* sort, at the verified modes only (task #152,
        -- restoring the I6/I7 symmetry task #100 stage 6 broke): the
        -- ∀ clause's own `ensureSort` move, on the body's inferred
        -- type.  It is what the set lane's annotation pass needs —
        -- `HasSort (A :: Δ) B v` — and what no metatheorem supplies:
        -- validity for `Infer` ("every inferred type has a sort") is
        -- refuted at the application clause, and nothing else in the
        -- checker computes a λ's codomain sort, so the fact has to be
        -- computed here.  The reference kernel's `infer_lambda`
        -- does not run it, so `.trusted` — the trusted lane —
        -- does not either.
        --
        -- It fires once per λ **chain**, at the innermost binder (the
        -- `!body.isLam` guard).  At an outer binder the codomain is
        -- the inner λ's own `∀`-type, whose sort is `imax` of the
        -- inner domain's (checked at that binder) and the chain's
        -- (checked here) — so no fact is lost, and this is the
        -- granularity the interned telescope loop (task #72) can
        -- reproduce: it opens a whole λ-chain in bulk and never
        -- materializes the intermediate opened types.
        if mode.verifiedChecks then
          match body.lamPw with
          | some pwI =>
            -- Task #161, the chain rule: an outer λ's codomain is the
            -- inner λ's own ∀-type, whose sort's zero-ness is the
            -- inner codomain's — datum equality with the neighbour,
            -- no inference (this dissolves the #152 chain guard's
            -- information loss: the per-node fact is now checked at
            -- every node, at O(1) each).
            unless mb.pw == pwI do
              throw (.notImplemented
                "sort-annotation mismatch (lam-cod-chain)")
          | none =>
            -- The innermost binder: the task-#152 codomain-sort
            -- computation, now also validating the node's annotation.
            -- task #172 B4: the type-of-a-type leaf at the io grade
            -- (the recursive call just established the body type)
            let btt ← r.inferIO (depth + 1) bt
            let vb ← ensureSort r env (depth + 1) btt
            unless Level.zeronessOf vb == mb.pw do
              throw (.notImplemented
                "sort-annotation mismatch (lam-cod-leaf)")
        pure (.forallE ty (bt.abstract1 depth) mb)
      | _ => throw (.invalid "expected a sort")
    | .app f a => do
      let tf ← r.infer depth f
      match ← r.whnf depth tf with
      | .forallE ty body _mt => do
        -- Per-argument re-check (task #100 de-gating: the former
        -- possibly-Prop annotation gate of task #49 is unsound-to-model
        -- under the domain-relative collapse, so the certificate runs
        -- unconditionally; the soundness proof needs `⟦a⟧ ∈ ⟦ty⟧`).
        let ta ← r.infer depth a
        unless ← r.defeq depth ta ty do
          throw (.invalid "application type mismatch")
        pure (body.instantiate1 a)
      | _ => throw (.invalid "function expected")
    | .proj sn i pe => do
      -- A `.proj` node is typed by its projection-table entry: the
      -- stored body, level-instantiated at the subject type's levels
      -- and instantiated at its arguments and the subject (task #175
      -- S1).  Only stored table entries type bare nodes (task #175
      -- W6: the pinned pair entries and their computed two-member
      -- fast path are retired; tower-flag: every stored table is a
      -- real one, the modeled route installs none).
      let te ← r.whnf depth (← r.infer depth pe)
      match te.getAppFn with
      | .const T us =>
        match env.findProj? T i with
        | some entry =>
          -- task #175 wiring W5: the node's struct name must be the
          -- subject type's head (official `infer_proj`'s
          -- `const_name(I) == proj_sname(e)`); the readings key the
          -- table on the node's name, the checker on the head's
          if T = sn ∧ te.getAppArgs.length = entry.numParams ∧
              us.length = entry.levelParams.length then do
            -- the official `infer_proj` restriction (task #175
            -- W4c/O4): at a `Prop`-declared structure the field —
            -- and every earlier field a later field uses — must be
            -- a proposition at this instantiation; the entry's
            -- guard level joins exactly those sorts
            if Level.isEquiv entry.structSort .zero == some true then
              unless Level.isEquiv
                  (Level.subst entry.levelParams us entry.fieldSort) .zero
                  == some true do
                throw (.invalid
                  "projection from a propositional structure must be a proposition")
            -- the body at the subject type's arguments and the
            -- subject, one `instantiateList` (task #175 S1)
            pure (entry.typeAt us te.getAppArgs pe)
          else throw (.notImplemented "projection without a native entry")
        | none => throw (.notImplemented "projection without a native entry")
      | _ => throw (.notImplemented "projection without a native entry")
    | .letE _ _ _ =>
      -- **Unreachable by construction** (task #241).  The official
      -- kernel's `infer_let` triple (`!infer_only`) is not lost: it is
      -- `annotateBody`'s `.letE` clause, which is the one pass that
      -- meets a `let` from the stream and which returns the ζ reduct
      -- (task #217).  Inference therefore only ever sees annotate
      -- output, which is let-free; see the `whnfCore` arm.
      throw (.internal "inferType: `let` in an annotated expression")
    | .bvar _ =>
      throw (.notImplemented "inferType beyond the supported fragment")

/-- **The io inference body** (task #161 stage 2 / task #170): `inferBody`
with one clause changed — the application rule's per-argument
certificate is skipped when the ∀'s validated annotation licenses it
(`ConLeche/Kernel/CoreIO.lean`'s module docstring holds the design
record).  The gate wraps the *test* only; the computed type
(`body.instantiate1 a`) and the "function expected" rejection are
`inferBody`'s, verbatim, so the lane is annotation-blind in its
results (law 1 (iii)).  Recursion is through `r.infer`: the io knot
ties this body to an io-grade record (`CoreFns.ioView` at the knot's
io slot, or `coreKnotIO`'s leaf lane), which is how the grade
propagates — official's `infer_type_core(e, infer_only)` passing
`infer_only` to every recursive call.

Moved here from `ConLeche/Kernel/CoreIO.lean` (task #172 B4) so the knot
can tie the io slot; the definition is byte-identical to the io-license
batch's. -/
def inferBodyIO (r : CoreFns m) (env : Env) : Nat → Expr → m Expr :=
  fun depth e => do
    match e with
    | .sort u => pure (.sort (.succ u))
    | .fvar idx ty =>
      if idx < depth then pure ty
      else throw (.invalid "free variable out of scope")
    | .const n us => do
      match env.find? n with
      | none => throw (unknownConstError n)
      | some ci =>
        -- a projection table is not a term (task #175 W4c): `.proj`
        -- nodes read it, no constant names it
        unless !ci.isTowerEntry do
          throw (.invalid s!"projection table entry used as a constant {n}")
        let cv := ci.toConstantVal
        unless us.length = cv.levelParams.length do
          throw (.invalid s!"incorrect number of universe levels for {n}")
        pure (cv.type.instantiateLevelParams cv.levelParams us)
    | .lit (.natVal _) => do
      if natLitSupported env then pure (.const natName [])
      else throw (.invalid "Nat literal without the Nat basis declarations")
    | .lit (.strVal _) => do
      if strLitSupported env then pure (.const stringName [])
      else throw (.notImplemented
        "string literals before the String support declarations")
    | .forallE ty body mb => do
      match ← r.whnf depth (← r.infer depth ty) with
      | .sort u => do
        let v ← ensureSort r env (depth + 1)
          (← r.infer (depth + 1) (body.instantiate1 (.fvar depth ty)))
        if mode.verifiedChecks then
          unless Level.zeronessOf v == mb.pw do
            throw (.notImplemented "sort-annotation mismatch (forall-cod)")
        pure (.sort (.imax u v))
      | _ => throw (.invalid "expected a sort")
    | .lam ty body mb => do
      -- Task #168 stage 2: no domain-sort run at the io grade —
      -- official's `infer_lambda` skips it at `infer_only`
      -- (`type_checker.cpp:131`), and the P row (`infer_lam_claimIO`)
      -- never consumed it: the domain's grading comes from the
      -- premise (`WellDenotedV.hoist_lam`).  The codomain validation stays
      -- — it is what makes the λ datum trustworthy.
      let bt ← r.infer (depth + 1)
        (body.instantiate1 (.fvar depth ty))
      if mode.verifiedChecks then
        match body.lamPw with
        | some pwI =>
          unless mb.pw == pwI do
            throw (.notImplemented
              "sort-annotation mismatch (lam-cod-chain)")
        | none =>
          let btt ← r.infer (depth + 1) bt
          let vb ← ensureSort r env (depth + 1) btt
          unless Level.zeronessOf vb == mb.pw do
            throw (.notImplemented
              "sort-annotation mismatch (lam-cod-leaf)")
      pure (.forallE ty (bt.abstract1 depth) mb)
    | .app f a => do
      let tf ← r.infer depth f
      match ← r.whnf depth tf with
      | .forallE ty body mt => do
        -- **THE io SITE.**  At a ∀ whose datum is `never` the
        -- certificate is dead weight: the premise-form io claim
        -- derives `⟦a⟧ ∈ ⟦ty⟧` from the subject's own `WellDenoted` app
        -- slot (`io_domain_transfer` + `piR_dom_unique`,
        -- side-condition free).  At a possibly-zero datum the
        -- certificate runs unconditionally — the squash regime's
        -- membership is model-class-wide unrecoverable
        -- (`io_membership_fails_at_squash`), and that fence is
        -- absolute.  The read is the DATUM ALONE (the licence ruling
        -- of 2026-09-06): it used to carry a `mode.verifiedChecks`
        -- conjunct, which inverted the trusted mode into running a
        -- certificate the verified mode skips.  Validating the datum
        -- is certification-only work; consuming it is not.  The
        -- licensing theorem never read the mode either.
        unless mt.pw.isNever do
          let ta ← r.infer depth a
          unless ← r.defeq depth ta ty do
            throw (.invalid "application type mismatch")
        pure (body.instantiate1 a)
      | _ => throw (.invalid "function expected")
    | .proj sn i pe => do
      let te ← r.whnf depth (← r.infer depth pe)
      match te.getAppFn with
      | .const T us =>
        match env.findProj? T i with
        | some entry =>
          -- task #175 wiring W5: the node's struct name must be the
          -- subject type's head (official `infer_proj`'s
          -- `const_name(I) == proj_sname(e)`); the readings key the
          -- table on the node's name, the checker on the head's
          if T = sn ∧ te.getAppArgs.length = entry.numParams ∧
              us.length = entry.levelParams.length then do
            -- the official `infer_proj` restriction (task #175
            -- W4c/O4), as in `inferBody`
            if Level.isEquiv entry.structSort .zero == some true then
              unless Level.isEquiv
                  (Level.subst entry.levelParams us entry.fieldSort) .zero
                  == some true do
                throw (.invalid
                  "projection from a propositional structure must be a proposition")
            -- the body at the arguments and the subject, as in
            -- `inferBody` (task #175 S1)
            pure (entry.typeAt us te.getAppArgs pe)
          else throw (.notImplemented "projection without a native entry")
        | none => throw (.notImplemented "projection without a native entry")
      | _ => throw (.notImplemented "projection without a native entry")
    | .letE _ _ _ =>
      -- unreachable by construction, as in `inferBody` (task #241)
      throw (.internal "inferType: `let` in an annotated expression")
    | .bvar _ =>
      throw (.notImplemented "inferType beyond the supported fragment")

/-- **The eq-true shortcut** (the divergence audit's E2): official
`is_def_eq_core`'s second clause (`type_checker.cpp:1093-1101`) — when
the right side is the constant `Bool.true` and the left side has no
free variables, the left side is fully head-normalised (`whnf`, the
cached loop) and the verdict is `true` iff the reduct is `Bool.true`; on
failure the step continues.  Only the reduction is here; the guard is
`defeqStep`'s, and it fires only at an `is_def_eq_core` entry (`pi`).
Verdict-neutral against lazy delta (a `whnf` reduct is what the
unfolding loop reaches, one step at a time), one memoised `whnf`
instead of one loop iteration per unfolding. -/
def boolTrueShortcut (r : CoreFns m) (depth : Nat) (a : Expr) : m Bool := do
  let w ← r.whnf depth a
  pure w.isBoolTrue

/-- Levels-and-spine congruence for two applications of the same
stored constant — the lazy delta *same-head short-circuit* (the
official kernel's `try_eq_const_app`): before unfolding both sides of
`f as ≡ f bs`, try pairwise definitional equality of the levels and
the spine arguments.  A `false` verdict is never final — the caller
falls back to unfolding — so an inconclusive level comparison simply
answers `false` here. -/
def defeqSpine (r : CoreFns m) (env : Env) (depth : Nat) (a b : Expr) :
    m Bool := do
  match a.getAppFn with
  | .const n us =>
    match b.getAppFn with
    | .const n' us' =>
      if n = n' ∧ a.getAppArgs.length = b.getAppArgs.length then
        match Level.isEquivList us us' with
        | some true => defEqList r env depth a.getAppArgs b.getAppArgs
        | _ => pure false
      else pure false
    | _ => pure false
  | _ => pure false

/-- The definitional-equality body: syntactic fast path, head
normalization of both sides (**no delta** — `whnfCore`), proof
irrelevance (the official kernel's `is_def_eq_proof_irrel`, run after
`whnf_core` and before any delta), then the
*lazy delta* strategy of real kernels: literal acceleration first
(mirroring the `whnf` loop order), then — when a side's head is an
unfoldable definition — unfold lazily, guided by the reducibility
hints (unfold only the side with the greater hint; at equal hints try
the same-head congruence short-circuit, then unfold both).  Each
literal-acceleration and unfolding step is one **iteration of this
loop** (the reference kernels' `lazy_delta_reduction` loop; lean4lean
runs it on `FuelConfig.lazyDelta`), and every re-entry re-runs the
syntactic fast path and `whnfCore` (the official kernel's `whnf_core`
after each unfold).  Task #106: these steps used to recurse through
`r.defeq`, charging a delta chain to the shared *recursion depth*
budget one unit per step.  Only when neither head unfolds does
structural congruence with the stuck fallbacks decide.  The hints
steer *order only*: every branch below is an independently sound
reduction or comparison, so the verdict never depends on the hint
values. -/
def defeqStep (r : CoreFns m) (env : Env) (depth : Nat)
    (k : Bool → Expr → Expr → m Bool) (pi : Bool) (a b : Expr) : m Bool := do
    -- syntactic fast path (the references' most-hit branch)
    if a == b then pure true else
    -- the eq-true shortcut (E2, `boolTrueShortcut`): right side
    -- `Bool.true`, left side fvar-free, at an entry only — official's
    -- `(!has_fvar(t) || m_eager_reduce) && is_constant(s, Bool.true)`
    -- (`:1097`; the eager flag is not mirrored yet, see the audit)
    if ← (if pi && b.isBoolTrue && !a.hasFvar then boolTrueShortcut r depth a
        else pure false) then pure true else
    let a' ← r.whnfCore depth a
    let b' ← r.whnfCore depth b
    if a' == b' then pure true else
    -- Proof irrelevance, hoisted before lazy delta exactly as in the
    -- official kernel (`is_def_eq_proof_irrel` runs after `whnf_core`
    -- and before `lazy_delta_reduction`): with theorem values
    -- delta-unfolding (task #66), leaving it in the stuck fallback
    -- would grind through proof bodies first (init-prelude probe:
    -- 227 G → recovered by the hoist).  The fallback's copy stays
    -- (memoized; reachable when a reduction step rewrites a side).
    -- Task #168 (Option U): the hoist is the `Prop` branch only, with
    -- the head-symbol fast arms; the unit-like test is `stuckIrrel`'s
    -- (every structural-failure exit below reaches it).
    --
    -- **Once per `is_def_eq_core` entry** (the divergence audit's D3,
    -- DESIGN.md "THE DIVERGENCE AUDIT"): official runs
    -- `is_def_eq_proof_irrel` before `lazy_delta_reduction` and never
    -- inside the loop — after an unfolding only `quick_is_def_eq` runs
    -- (`type_checker.cpp:965-969`, `:1118-1122`).  `pi` is the entry
    -- flag: `true` at the body's entry and at the literal-acceleration
    -- re-entries (official restarts `is_def_eq_core` there,
    -- `:1010-1012`), `false` on the delta continuations.  A re-run
    -- could not answer differently — a proof stays a proof under
    -- unfolding — so the gate is cost only (5× per delta step on the
    -- audit's lockstep-chain witness).
    -- D4: never on a pair official's `quick_is_def_eq` decides itself
    -- (sort/sort, lit/lit, ∀/∀, λ/λ — `Expr.quickPair`): the binder
    -- arms commit their own verdict there, without proof irrelevance
    if ← (if pi && !a'.quickPair b' then propIrrel r env depth a' b'
        else pure false) then
      pure true else
    -- Literal acceleration is guarded on *both* sides being free of
    -- free variables, mirroring the official kernel
    -- (`type_checker.cpp`, `lazy_delta_reduction`:
    -- `if ((!has_fvar(t_n) && !has_fvar(s_n)) || m_eager_reduce)`) and
    -- lean4lean (`TypeChecker.lean:782`).  Unguarded folding is a
    -- forbidden strategy superset (DESIGN.md, reduction-strategy
    -- ruling): on an *open* `Int32`/`Int64` arithmetic pair it whnfs
    -- an open argument and delta-grinds the `Nat.brecOn` tower toward
    -- `2^31`/`2^63` unary `succ` steps; guarded, such pairs fall
    -- through to the `sameRegular` spine congruence below (the
    -- official kernel's `is_def_eq_args`).  The whnf-loop `reduceNat`
    -- (`whnfBody`) stays unguarded — the official whnf loop is too.
    -- The `hasFvar` traversals cost no more than the `a' == b'`
    -- comparison already above (this Expr-level body is the
    -- specification; the executable interned twin reads an `O(1)`
    -- eager per-node fvar range instead).
    match ← (if !a'.hasFvar && !b'.hasFvar then
        reduceNat r env depth a' else pure none) with
    | some a₂ => k true a₂ b'
    | none =>
    match ← (if !a'.hasFvar && !b'.hasFvar then
        reduceNat r env depth b' else pure none) with
    | some b₂ => k true a' b₂
    | none =>
    -- Lazy delta, **decision before materialization** (the official
    -- kernel's `lazy_delta_reduction_step` reads a `delta_step` off
    -- the two heads and their hints and calls `unfold_definition`
    -- only inside the branch that consumes it; lean4lean's
    -- `isDefEqDelta` likewise).  The former spelling built *both*
    -- unfoldings in the match scrutinee before deciding which one it
    -- needed — pure waste on every one-sided step and on every
    -- short-circuited same-head step (measured at ~19 000 unfoldings
    -- per side on `Std.Time…toDays._proof_1`, task #106).  The
    -- `pure false` fallbacks are unreachable — `unfoldableHead env e`
    -- is `(unfoldDefinition env e).isSome` by construction — and
    -- sound (`false` is never a certificate).
    match unfoldableHead env a', unfoldableHead env b' with
    | true, false =>
      match unfoldDefinition env a' with
      | some a₂ => k false a₂ b'
      | none => pure false
    | false, true =>
      match unfoldDefinition env b' with
      | some b₂ => k false a' b₂
      | none => pure false
    | true, true =>
      let ha := headHint env a'
      let hb := headHint env b'
      if ReducibilityHint.lt hb ha then
        match unfoldDefinition env a' with
        | some a₂ => k false a₂ b'
        | none => pure false
      else if ReducibilityHint.lt ha hb then
        match unfoldDefinition env b' with
        | some b₂ => k false a' b₂
        | none => pure false
      else if ReducibilityHint.sameRegular ha hb && sameConstHeads a' b' then
        -- Same constant at equal *regular* hints: cheap congruence
        -- first — this short-circuit is where lazy delta wins on
        -- large proof terms, and (task #106) it now runs *before* any
        -- unfolding is built, as `try_eq_const_app` does.  The
        -- `sameRegular` guard mirrors the reference kernels (nanoda
        -- `try_eq_const_app`, the official kernel) exactly and is
        -- deliberate: at equal `abbrev` (or `opaque`) hints both
        -- sides unfold eagerly instead, because proof authors rely on
        -- abbrevs unfolding eagerly and a spine defeq attempt on
        -- abbrev-headed applications risks reduction bombs (spines
        -- only equal after reduction, retried at every congruence
        -- level).  Do not generalize this guard.
        if ← defeqSpine r env depth a' b' then pure true
        else
          match unfoldDefinition env a', unfoldDefinition env b' with
          | some a₂, some b₂ => k false a₂ b₂
          | _, _ => pure false
      else
        match unfoldDefinition env a', unfoldDefinition env b' with
        | some a₂, some b₂ => k false a₂ b₂
        | _, _ => pure false
    | false, false =>
    match a', b' with
    | .sort u, .sort v => liftFueled "level comparison" (Level.isEquiv u v)
    | .lit l₁, .lit l₂ => pure (l₁ == l₂)
    -- a packed literal against a constructor form: compare
    -- shape-directed (an unpack-and-retry would immediately repack in
    -- `reduceNat` and loop)
    | .lit (.natVal n), .const c us =>
      if c = natZeroName ∧ us = [] then pure (n == 0)
      else stuckIrrel mode r env depth (.lit (.natVal n)) (.const c us)
    | .const c us, .lit (.natVal n) =>
      if c = natZeroName ∧ us = [] then pure (n == 0)
      else stuckIrrel mode r env depth (.const c us) (.lit (.natVal n))
    | .lit (.natVal nn), .app f x =>
      match nn, f with
      | k + 1, .const c [] =>
        if c = natSuccName then r.defeq depth (.lit (.natVal k)) x
        else stuckIrrel mode r env depth (.lit (.natVal nn)) (.app f x)
      | _, _ => stuckIrrel mode r env depth (.lit (.natVal nn)) (.app f x)
    | .app f x, .lit (.natVal nn) =>
      match nn, f with
      | k + 1, .const c [] =>
        if c = natSuccName then r.defeq depth x (.lit (.natVal k))
        else stuckIrrel mode r env depth (.app f x) (.lit (.natVal nn))
      | _, _ => stuckIrrel mode r env depth (.app f x) (.lit (.natVal nn))
    -- a string literal against a unary `String.ofList` application:
    -- expand the literal to its constructor form and compare — the
    -- reference kernels' `tryStringLitExpansion` (lean4lean
    -- `TypeChecker.lean`, nanoda `try_string_lit_expansion`), which
    -- fires exactly when the other side's function part is the bare
    -- `String.ofList` constant
    | .lit (.strVal st), .app (.const cO usO) x =>
      if cO = stringOfListName ∧ usO = [] ∧ strLitSupported env then
        r.defeq depth (strLitToConstructor st) (.app (.const cO usO) x)
      else stuckIrrel mode r env depth (.lit (.strVal st)) (.app (.const cO usO) x)
    | .app (.const cO usO) x, .lit (.strVal st) =>
      if cO = stringOfListName ∧ usO = [] ∧ strLitSupported env then
        r.defeq depth (.app (.const cO usO) x) (strLitToConstructor st)
      else stuckIrrel mode r env depth (.app (.const cO usO) x) (.lit (.strVal st))
    | .fvar i ty₁, .fvar j ty₂ =>
      if i == j then pure true
      else stuckIrrel mode r env depth (.fvar i ty₁) (.fvar j ty₂)
    | .const n us, .const n' us' =>
      if n = n' then
        if ← liftFueled "level comparison" (Level.isEquivList us us') then
          pure true
        else stuckIrrel mode r env depth (.const n us) (.const n' us')
      else stuckIrrel mode r env depth (.const n us) (.const n' us')
    | .forallE ty₁ body₁ m₁, .forallE ty₂ body₂ m₂ => do
      -- Binder congruence.  Task #161: at the verified modes the two
      -- prop-ness annotations must agree (`==`; the datum is canonical) for the
      -- two-regime interpretations to coincide (`piR_zero_agree`'s
      -- premise).  The comparison runs LAST — only a pair that is
      -- otherwise definitionally equal can reach it, so benign
      -- cert-fallthrough `false`s are untouched and a firing mismatch
      -- is exactly the cross-provenance coherence corner, declined
      -- loudly.  (The official kernel compares no annotations; the
      -- pre-#100 zero-ness comparison is back in validated clothing.)
      unless ← r.defeq depth ty₁ ty₂ do return false
      unless ← r.defeq (depth + 1)
          (body₁.instantiate1 (.fvar depth ty₂))
          (body₂.instantiate1 (.fvar depth ty₂)) do return false
      if mode.verifiedChecks && !(m₁.pw == m₂.pw) then
        throw (.notImplemented "sort-annotation mismatch (defeq-forall)")
      pure true
    | .lam ty₁ body₁ m₁, .lam ty₂ body₂ m₂ => do
      unless ← r.defeq depth ty₁ ty₂ do return false
      unless ← r.defeq (depth + 1)
          (body₁.instantiate1 (.fvar depth ty₂))
          (body₂.instantiate1 (.fvar depth ty₂)) do return false
      if mode.verifiedChecks && !(m₁.pw == m₂.pw) then
        throw (.notImplemented "sort-annotation mismatch (defeq-lam)")
      pure true
    | .app f₁ a₁, .app f₂ a₂ => do
      -- Stuck applications: **spine-wise** congruence (the official
      -- kernel's `is_def_eq_app`, lean4lean's `isDefEqApp`, nanoda's
      -- `def_eq_app`): equal spine lengths, one head comparison, then
      -- the argument lists pairwise.  Task #106: the former spelling
      -- recursed `defeq` on the *partial* applications `f₁ ≡ f₂`, so
      -- a length-`n` spine re-entered the whole body `n` times —
      -- `n` syntactic fast paths, `n` `whnfCore` pairs, `n` proof
      -- irrelevance probes (two `infer`s each!) and `n` lazy delta
      -- decisions, at `n` levels of knot recursion.  No reference
      -- kernel does that, and nothing is lost: `whnfCore` already
      -- normalized the function parts, and the `unfoldableHead`
      -- guards above are read off the *head* constant, which the
      -- partial applications share.  Then the stuck fallbacks (proof
      -- irrelevance is additionally hoisted before lazy delta at the
      -- top of this body, as in the official kernel; the fallback
      -- copy here fires when a reduction step rewrote a side after
      -- the hoist ran).
      if (Expr.app f₁ a₁).getAppArgs.length =
          (Expr.app f₂ a₂).getAppArgs.length then
        if ← r.defeq depth (Expr.app f₁ a₁).getAppFn
            (Expr.app f₂ a₂).getAppFn then
          if ← defEqList r env depth (Expr.app f₁ a₁).getAppArgs
              (Expr.app f₂ a₂).getAppArgs then pure true
          else stuckIrrel mode r env depth (.app f₁ a₁) (.app f₂ a₂)
        else stuckIrrel mode r env depth (.app f₁ a₁) (.app f₂ a₂)
      else stuckIrrel mode r env depth (.app f₁ a₁) (.app f₂ a₂)
    | .proj s₁ i₁ e₁, .proj s₂ i₂ e₂ => do
      -- Stuck projections: congruence, else the stuck fallbacks.
      -- Task #175 wiring W5: congruence requires the same struct name
      -- — the entry-kind readings differ across names, and on
      -- annotated terms the name is the subject type's head, so
      -- defeq subjects always agree (transitional: dissolves at W6).
      if s₁ == s₂ && i₁ == i₂ then
        if ← r.defeq depth e₁ e₂ then pure true
        else stuckIrrel mode r env depth (.proj s₁ i₁ e₁) (.proj s₂ i₂ e₂)
      else stuckIrrel mode r env depth (.proj s₁ i₁ e₁) (.proj s₂ i₂ e₂)
    -- One-sided λ: eta, else the stuck fallbacks.
    | .lam ty₁ body₁ m₁, b₂ => do
      if ← etaCert mode r env depth ty₁ body₁ m₁ b₂ then pure true
      else stuckIrrel mode r env depth (.lam ty₁ body₁ m₁) b₂
    | a₁, .lam ty₂ body₂ m₂ => do
      if ← etaCert mode r env depth ty₂ body₂ m₂ a₁ then pure true
      else stuckIrrel mode r env depth a₁ (.lam ty₂ body₂ m₂)
    -- Distinct whnf-stuck head symbols: only the stuck fallbacks can
    -- equate them; `false` is always sound, and `whnf` has already
    -- thrown on unsupported heads, so no unimplemented case can hide
    -- here.
    | e₁, e₂ => stuckIrrel mode r env depth e₁ e₂

/-- The lazy-delta loop: iterate `defeqStep` on its own step budget. -/
def defeqLoop (r : CoreFns m) (env : Env) (depth : Nat) :
    Nat → Bool → Expr → Expr → m Bool
  | 0, _, _, _ => throw (.internal "fuel exhausted: defeq loop")
  | fl + 1, pi, a, b =>
    defeqStep mode r env depth (defeqLoop r env depth fl) pi a b

/-- Step budget of the lazy-delta loop (lean4lean's
`FuelConfig.lazyDelta`, generously sized here because this loop also
absorbs the literal-acceleration re-entries lean4lean routes through
`isDefEqCore`).  Exhaustion is an internal error, never a verdict. -/
@[irreducible] def defeqLoopFuel : Nat := 100000

/-- The definitional-equality body: the lazy-delta loop at its own
step budget. -/
def defeqBody (r : CoreFns m) (env : Env) : Nat → Expr → Expr → m Bool :=
  fun depth a b => defeqLoop mode r env depth defeqLoopFuel true a b

/-- Check that a (raw) type is a `Prop` by annotating it and inferring
its sort. -/
def isPropType (r : CoreFns m) (env : Env) (depth : Nat) (ty : Expr) :
    m Bool := do
  let ty' ← r.annotate depth ty
  -- io grade (task #172 B4): `ty'` is the pass's own output, already
  -- annotated — the bottom-up circularity guard: annotation of a node
  -- consults `inferIO` only on subterms whose annotation is complete
  let s ← ensureSort r env depth (← r.inferIO depth ty')
  liftFueled "level comparison" (Level.isEquiv s Level.zero)

/-! ### The untrusted annotation writes (task #161 P5)

The pass is the existing normalizer: at the verified modes its ∀/λ
clauses *write* the `pw` datum the front door then *validates*.  The
write is untrusted by design — a wrong datum declines, never
unsoundness — and it is a no-op wherever the input already carries a
non-placeholder annotation (`pwWritten`): explicit input annotations
are judged by validation, never overwritten.  The parser's placeholder
for an absent `"pw"` field is `.never`, which is also a legitimate
value; the pass therefore recomputes over `.never` unconditionally
(harmless: a genuinely never-zero codomain recomputes to `.never`),
and the *only* input annotations preserved are the `ifAllZero` ones.
-/

/-- The ∀ node's datum: the zero-ness of the *codomain*'s sort, on the
already-annotated opened body — exactly the value `inferBody`'s ∀
clause validates against (`(forall-cod)`).

**The chain read (task #161 P5, proof-lane repair).**  A ∀ body that is
itself a ∀ reuses its inner neighbour's datum instead of inferring:
`zeronessOf (imax u v) = zeronessOf v`, so every node of a telescope
carries the *leaf* codomain sort's zero-ness.  This is the same rule
`annotPwLam` already applies through `lamPw`, and it is what makes the
spec pass pay **one** inference per ∀ telescope, as the design's
telescope-collapse paragraph claims — and what makes it agree with the
interned pass, which computes at the leaf and threads outward
(`annotateBindersOutI`).

Without it the spec inferred the whole inner telescope at every node,
so it *failed* on terms the interned pass accepts — e.g.
`∀ (x : Prop), ∀ (y : Foo), Prop` with `Foo` absent from the
environment: `annotate` never looks a constant up, but inferring the
inner ∀ node does.  See DESIGN.md, task #161 P5 proof-lane finding. -/
def annotPwPi (r : CoreFns m) (env : Env) (depth : Nat) (body' : Expr) :
    m PropWhen := do
  -- Task #168 stage 2: the head-symbol reader first.  It subsumes the
  -- chain read (`typeSortPW` of a ∀ IS its `forallPw`) and answers
  -- most leaves without inference; the pass is untrusted — `infer`
  -- validates every datum it writes — so the reader owes no licence
  -- here, only the datum's agreement (census: 0 non-equivalent data).
  match typeSortPW env.find? body' with
  | some pw => pure pw
  | none => do
    -- io grade: `body'` is already annotated (bottom-up)
    let v ← ensureSort r env depth (← r.inferIO depth body')
    pure (Level.zeronessOf v)

/-- The λ node's datum: the zero-ness of the sort of the *body's type*.
Mirrors `inferBody`'s λ clause exactly — a λ body reuses its inner
neighbour's datum (the chain rule, no inference), any other body pays
one leaf computation (`(lam-cod-leaf)`). -/
def annotPwLam (r : CoreFns m) (env : Env) (depth : Nat) (body' : Expr) :
    m PropWhen := do
  -- task #168 stage 2: the reader first (it subsumes the `lamPw`
  -- chain read), as in `annotPwPi`
  match proofPW env.find? body' with
  | some pw => pure pw
  | none => do
    -- io grade: `body'` is already annotated (bottom-up)
    let bt ← r.inferIO depth body'
    let vb ← ensureSort r env depth (← r.inferIO depth bt)
    pure (Level.zeronessOf vb)

/-- The annotation body: compute the codomain-sort annotations of every
binder, bottom-up, by real inference on the opened (already annotated)
body.  For a `forallE` the annotation is the body's sort (so this also
checks that the body *is* a type — the ∀-formation rule); for a `lam`
it is the sort of the body's type.  The `.app` clause is structural:
the application rule is not checked here.  The inference sweep that
follows re-checks every application and every binder body and
validates each annotation against its own result; what it takes from
the annotations is a licence to skip a *certificate* at a binder whose
datum is `never`, never a typing it does not redo. -/
def annotateBody (r : CoreFns m) (env : Env) : Nat → Expr → m Expr :=
  fun depth e =>
    match e with
    | .bvar i => pure (.bvar i)
    | .fvar idx ty =>
      -- Leaf scope check, as in `inferBody`: annotation is the pass raw
      -- input enters through, so a dangling free variable in the input
      -- is rejected here (depth 0: any `fvar` fails).
      if idx < depth then pure (.fvar idx ty)
      else throw (.invalid "free variable out of scope")
    | .sort u => pure (.sort u)
    | .const n us => pure (.const n us)
    | .lit (.natVal n) => do
      -- a literal is well-formed exactly when its type's declarations
      -- are stored in the expected shape
      if natLitSupported env then pure (.lit (.natVal n))
      else throw (.invalid "Nat literal without the Nat basis declarations")
    | .lit (.strVal s) => do
      -- as for `Nat` literals; the missing-support verdict is a
      -- decline (exit 2), the feature being positively detected
      if strLitSupported env then pure (.lit (.strVal s))
      else throw (.notImplemented
        "string literals before the String support declarations")
    | .app f a => do
      -- structural (task #100 stage 6: the application rule's checks
      -- moved to the driver's inference sweep — `inferBody`'s app
      -- clause re-checks every argument unconditionally)
      let f' ← r.annotate depth f
      let a' ← r.annotate depth a
      pure (.app f' a')
    | .forallE ty body mb => do
      -- structural (task #100 stage 6: no annotation to compute and no
      -- checks — the driver's inference sweep re-checks every binder
      -- body via the ∀/λ rules)
      let ty' ← r.annotate depth ty
      let body' ← r.annotate (depth + 1) (body.instantiate1 (.fvar depth ty'))
      let pw ← if !pwWritten mb.pw then
          annotPwPi r env (depth + 1) body'
        else pure mb.pw
      pure (.forallE ty' (body'.abstract1 depth) ⟨pw⟩)
    | .lam ty body mb => do
      let ty' ← r.annotate depth ty
      let body' ← r.annotate (depth + 1) (body.instantiate1 (.fvar depth ty'))
      let pw ← if !pwWritten mb.pw then
          annotPwLam r env (depth + 1) body'
        else pure mb.pw
      pure (.lam ty' (body'.abstract1 depth) ⟨pw⟩)
    | .letE ty v b => do
      -- The body is annotated *with the value transparent* — nanoda's
      -- `infer_let` instantiates the body with the value and recurses
      -- (the official kernel gets the same transparency from valued
      -- let-fvars in its local context).  ConLeche fvars carry no value,
      -- so the body is annotated as its zeta reduct; an opened opaque
      -- variable was tried and rejects real streams (elaborated `let`
      -- bodies rely on the value definitionally — see DESIGN.md).
      --
      -- Task #217 (audit follow-up #206-S1): the official `infer_let`
      -- triple — `ensure_sort_core(infer(type))`, `infer(val)`,
      -- `is_def_eq(val_type, type)` — runs HERE, on the annotated
      -- annotation and the annotated value, before the reduct is taken.
      --
      -- Task #161 item C2 dropped it as redundant with `inferBody`'s
      -- own `.letE` clause.  That was wrong: this clause returns the ζ
      -- reduct, so the stored term is let-free and `inferBody`'s
      -- `.letE` arm never sees a `letE` node the driver produced —
      -- `def x : Nat := let y : Nat := Bool.true; Nat.zero` was
      -- accepted where the official kernel rejects ("(kernel)
      -- let-declaration type mismatch").  The annotation pass is the
      -- only pass that meets a `letE`, so it is where the triple must
      -- run.
      let ty' ← r.annotate depth ty
      let _ ← ensureSort r env depth (← r.infer depth ty')
      let v' ← r.annotate depth v
      let tv ← r.infer depth v'
      unless ← r.defeq depth tv ty' do
        throw (.invalid "let value type mismatch")
      r.annotate depth (b.instantiate1 v)
    | .proj sn i pe => do
      let e' ← r.annotate depth pe
      -- Run the projection rule (the one place it is checked; this
      -- establishes the semantic proj clause of `AnnotOk`).  A table
      -- entry types the node directly (the display name is normalized
      -- to the type's head, so reduction's table lookup is complete on
      -- annotated terms); a family without a table is a modeled one
      -- and has no `.proj` typing at all.
      let te ← r.whnf depth (← r.inferIO depth e')
      match te.getAppFn with
      | .const T _ =>
        match env.findProj? T i with
        | some entry => do
          -- TASK #271 (issue #7): the node's OWN structure name is
          -- official's `infer_proj` premise `const_name(I) ==
          -- proj_sname(e)`, and it is checked HERE and not only on the
          -- annotated term: the normalization to the type's head below
          -- would otherwise repair a node that names another
          -- inductive, and official rejects it ("invalid projection").
          unless T = sn do
            throw (.invalid "invalid projection: the node names another structure")
          unless te.getAppArgs.length = entry.numParams do
            throw (.invalid "projection parameter mismatch")
          pure (.proj T i e')
        | none =>
          -- task #175 wiring W5: the elimination fallbacks are gone —
          -- every supported projection is a native table entry.
          -- An out-of-range index on a projectable structure (its
          -- field 0 has an entry) is invalid; a shape without any
          -- projection support declines
          throw (if (env.findProj? T 0).isSome then
              CheckError.invalid "projection index out of range"
            else .notImplemented "projection on a non-structure-like type")
      | _ => throw (.notImplemented "projection on a non-structure type")

end Bodies

/-- Tie the bodies together at a monad: the record whose entry points
are the bodies applied to the record one fuel level down.  Fuel is
*only* here — exhaustion is an internal error, never a verdict.  The
next level is constructed lazily, inside each entry point's closure
(constant work per call; an eager tower would cost `fuel` allocations
per instantiation). -/
def coreKnot {m : Type → Type} [Monad m] [MonadExceptOf CheckError m]
    (mode : CheckMode) (env : Env)
    (wrap : CoreFns m → CoreFns m) : Nat → CoreFns m
  | 0 =>
    { whnfCore := fun _ _ => throw (.internal "fuel exhausted: whnfCore")
      whnf := fun _ _ => throw (.internal "fuel exhausted: whnf")
      infer := fun _ _ => throw (.internal "fuel exhausted: infer")
      defeq := fun _ _ _ => throw (.internal "fuel exhausted: defeq")
      annotate := fun _ _ => throw (.internal "fuel exhausted: annotate")
      inferIO := fun _ _ => throw (.internal "fuel exhausted: infer") }
  | fuel + 1 =>
    wrap
      { whnfCore := fun d e =>
          whnfCoreBody mode (coreKnot mode env wrap fuel) env d e
        whnf := fun d e => whnfBody (coreKnot mode env wrap fuel) env d e
        infer := fun d e =>
          inferBody mode (coreKnot mode env wrap fuel) env d e
        defeq := fun d a b =>
          defeqBody mode (coreKnot mode env wrap fuel) env d a b
        annotate := fun d e =>
          annotateBody (coreKnot mode env wrap fuel) env d e
        -- **The io slot** (task #170 / #172 B4).  The grade's meaning is
        -- the mode's: at the gated mode the io body, tied to the io-grade
        -- view of the knot one level down (the grade propagates, as
        -- official's `infer_only` does); at every other mode the full
        -- inference body, verbatim — "in R mode infer_only is just
        -- equivalent to infer" (the task-#170 order).  The selection
        -- reads mode-and-datum-free data (`mode.betaGate`, the same bit
        -- the β gate reads) and is made once per knot level.
        inferIO := fun d e =>
          if mode.betaGate then
            inferBodyIO mode
              (CoreFns.ioView (coreKnot mode env wrap fuel)) env d e
          else inferBody mode (coreKnot mode env wrap fuel) env d e }

/-- The shared fuel for the checker core: bounds the recursion depth of
reduction, inference and definitional equality.  Exhaustion is an
internal error, never a verdict. -/
def checkFuel : Nat := 100000

end ConLeche
