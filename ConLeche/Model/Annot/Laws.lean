module

public import ConLeche.Model.Currency
public import ConLeche.Semantics.DivModEval
public import ConLeche.Verify.ProjTele
public import ConLeche.Verify.Denote.OpenVars
public import ConLeche.Verify.EnvGuards

public section

/-!
# The environment laws (task #305 closing)

The environment laws (task #305 closing): the definitions `EnvModelM`'s
fields are stated over — the `Nat` recurrences, the `Eq` and opaque
laws, the structure-capability laws, the fired modeled-iota contract,
the tower projection law — in a module of their own so that the rules
tier's inputs (`Model/Rules/Inputs.lean`) can name them without
importing `EnvModelM`'s establishment surface.  They were in
`Model/Annot/EnvModelM.lean` until task #305 closing; the docstrings
are the ones they carried there.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (CheckMode Env Expr Name Level ConstantInfo ConstantVal
  ReducibilityHint IndCaps projFnName RecRule)

universe w

-- `EnvModelM.lean` declares this variable EXPLICIT, for the structure's
-- sake; here it is implicit, so that the residues below and
-- `teleFit_nil_inv` keep the signatures their source files gave them.
-- No definition moved here reads it: each binds its own `V`.
variable {V : Type w} [SetTheory V]

/-- **The structural-`Nat` recurrence law at the validated-annotation
tier** (task #161, the wall's supplier): every stored structural
operation's defining equations read under `denoteMeta` and hold as
`interp` equalities at the two-variable `Nat` context — `NatOpsV`
(`Sound/Motives.lean`) with `denote`/`interp`/`cval` replaced by
`denoteMeta`/`interp`/`acval`, and the level composition normalized to
the plain assignment (the heads are level-monomorphic).

Supplied as an `EnvModelM` field: established at the operation's own
install from the recorded `isDefEqCore` runs (`NatEqsRun`) through
`DefEqClaim` — the run-certificate route (`Interp/NatEqsP.lean`)
— and preserved across every other fresh cons.  Consumed by the
numeral-transport inductions (`Sound/NatOps`' shape at `interp`),
which close the literal rows `NatSuccRow`/`NatOpRow` of
`Model/Rules/Inputs.lean` (`Model/NatStep.lean`). -/
@[expose] def NatOps {V : Type w} [SetTheory V] {env : Env}
    (m : EnvModel V env) (φ : Name → Nat) : Prop :=
  ∀ c ∈ ConLeche.natOpNames, ∀ cv v hint,
    env.find? c = some (.defnInfo cv v hint) →
    ConLeche.natOpGuard env c = true ∧
    ∀ eq ∈ ConLeche.natOpEquations 0 c, ∃ L R,
      denoteMeta m.acval env φ 2 eq.1 = some L ∧
      denoteMeta m.acval env φ 2 eq.2 = some R ∧
      ∀ (ρ : Nat → V) (x y : V),
        x ∈ˢ interp V ρ (m.acval ConLeche.natName φ) →
        y ∈ˢ interp V ρ (m.acval ConLeche.natName φ) →
        interp V (cons y (cons x ρ)) L
          = interp V (cons y (cons x ρ)) R

/-- **The pin-certified WF-recursive operations' guarded value
recurrences at the validated-annotation tier** — `DivModV`
(`Sound/Motives.lean`) with `interp`/`cval` replaced by
`interp`/`acval`.  `DivModClausesV` is already valuation-generic, so
it is reused verbatim: only the valuation it is fed changes.

Supplied as an `EnvModelM` field: established at the operation's own
install from the recorded certificate runs (`DivModPinR`'s
`checkDivModCerts` verdict) through `InferClaim`/`DefEqClaim` —
the run-certificate route again (`Interp/DivMod.lean`) — and
preserved across every other fresh cons.  Consumed by the WF-op
numeral transports (`Sound/NatOpsWf`' shape at `interp`). -/
@[expose] def DivMod {V : Type w} [SetTheory V] {env : Env}
    (m : EnvModel V env) (φ : Name → Nat) : Prop :=
  ∀ c ∈ ConLeche.natDivModNames, ∀ cv v hint,
    env.find? c = some (.defnInfo cv v hint) →
    ConLeche.natOpGuard env c = true ∧
    ∀ (ρ : Nat → V) (x y : V),
      x ∈ˢ interp V ρ (m.acval ConLeche.natName φ) →
      y ∈ˢ interp V ρ (m.acval ConLeche.natName φ) →
      DivModClausesV V (fun n => interp V ρ (m.acval n φ)) c x y

/-- **The pinned `Eq` spine's value at `interp`** — `EnvS.eq_lawV`'s
mirror one currency over, stated directly at the three-fold
application (the only form the certificate consumers read; v1 states
the two-fold `lamC` form because its η/unit consumers need the
rigidity clause, which nothing here does).

**This is an environment law, exactly as in v1**: `EqLawV` is an
`EnvS` *field*, not a theorem, because the `Eq` leaf's value is fixed
by the basis install (`Install/BasisS.lean`'s `eqValT` — the `.eqE`
former η-expanded) and by nothing else.  The P mirror is a field for
the same reason, and its supplier is the P basis install
(`BasisStepPB`, routed): the annotated `Eq` tower's *regime bits* are
invisible to every other `EnvModelM` field, and the erasure factoring
that would import the v1 law is refuted at exactly the λ-nodes this
tower is made of (the literal-tier seal II finding 1).  See the task
#161 LITERAL TIER seal III record. -/
@[expose] def EqLaw {V : Type w} [SetTheory V] {env : Env}
    (m : EnvModel V env) : Prop :=
  env.find? eqName = some eqA →
  ∀ ψ : Name → Nat,
    -- the spine's **value**: the truth set of the equation
    (∀ (ρ : Nat → V) (A a b : V),
      A ∈ˢ (univ (ψ uN) : V) → a ∈ˢ A → b ∈ˢ A →
      SetTheory.app (SetTheory.app (SetTheory.app
          (interp V ρ (m.acval eqName ψ)) A) a) b = eqv a b) ∧
    -- the spine's **grading**, and that it is a proposition.  (v1
    -- needs neither: `AnnotOkV` has no bit content and `CtxOkR` asks
    -- for no grading.  Both are stated here for the same reason v1
    -- restated `EqLawV` at the two-fold application — an interface
    -- field is stated at the shape its consumers read, and the
    -- certificate frame reads exactly these.)
    ∀ (ρ : Nat → V) (Aa la ra : AnnotTerm),
      WellDenotedV V ρ Aa → WellDenotedV V ρ la → WellDenotedV V ρ ra →
      interp V ρ Aa ∈ˢ (univ (ψ uN) : V) →
      interp V ρ la ∈ˢ interp V ρ Aa →
      interp V ρ ra ∈ˢ interp V ρ Aa →
      WellDenotedV V ρ
          (.app (.app (.app (m.acval eqName ψ) Aa) la) ra) ∧
        interp V ρ (.app (.app (.app (m.acval eqName ψ) Aa) la) ra)
          ∈ˢ (univZero : V)

/-- **The compiler-trust opaques are the identity, at `interp`** —
`EnvS.reduce_ops` (`ReduceOpsV`, `SetR/EnvS.lean:138`) one currency
over, with `interp`/`cval` replaced by `interp`/`acval`.  The stored
`Lean.reduceNat`/`Lean.reduceBool` leaf, applied to a member of its
element type's reading, *is* that member.

**This is an environment law, exactly as `eq_law` is**: the opaque's
leaf value is fixed by its own install (`checkReducePin`'s identity
certificate) and by nothing else, so the only possible supplier is
that install.  The v1 field cannot be imported — the transfer would
be an erasure factoring of `interp` through `interp`, refuted at
exactly the λ-nodes the operation's leaf is made of (the literal-tier
seal II finding 1, the same refutation that makes `EqLaw` a field).

**Establishment**: `reduceOps_install` (`Interp/ReduceOps.lean`),
at the opaque cons, from `ReducePinR`'s *recorded* identity-certificate
run (`isDefEqCore μ env F 1 (.app valA (reduceCertVar c))
(reduceCertVar c) = .ok true`) through `DefEqClaim` at the
one-entry element context — the run-certificate route's fifth
execution.  **Preservation**: `reduceOps_cons_fresh` at every other
fresh cons (the law mentions two stored leaves, so it crosses).
**Consumer**: the `ofReduceNat`/`ofReduceBool` axiom branch
(`Interp/AxiomReduceP.lean`), whose innermost membership obligation
is exactly `op a = a`. -/
@[expose] def ReduceOps {V : Type w} [SetTheory V] {env : Env}
    (m : EnvModel V env) : Prop :=
  ∀ c ∈ ConLeche.reduceOpNames, ∀ cv : ConstantVal,
    env.find? c = some (.axiomInfo cv) →
    ConstantVal.matchesPin cv (ConLeche.reduceOpCvA c) = true →
    (env.find? (ConLeche.reduceElemName c)).isSome = true ∧
    ∀ (ψ : Name → Nat) (ρ : Nat → V) (x : V),
      x ∈ˢ interp V ρ (m.acval (ConLeche.reduceElemName c) ψ) →
      SetTheory.app (interp V ρ (m.acval c ψ)) x = x

/-! ## The structure-capability laws (task #161, caps tier)

`CapsOkV`'s mirror at the validated-annotation currency: the stored
families' fired η and unit-like laws, value-level, keyed exactly as
the v1 field (`Sound/Motives.lean:309`) on the stored `indInfo`, the
capability flag, the non-reserved name, and the completed family
(`EtaFamilyStored`).

Design decisions, recorded (the lane lead's freeze; the statements
below are unchanged from `Interp/CapsP.lean`'s first landing, which
is now the *preservation* file — the definitions moved here because
the `EnvModelM` field must import them and `CapsP` imports `EnvModelM`):

* **The telescope fit is `TeleFit`, not `TeleFit2`.**  `TeleFit2`
  (`Annot/Spine2.lean`) demands every product in the graph regime
  (`v ≠ 0`), which a `Prop`-valued family's telescope violates.
  `TeleFit` mirrors `TeleFitV` instead — memberships only, the
  peeled body read under the extended environment (the `interp`
  analogue of `B.inst a`), no positivity anywhere.  Consumers recover
  residual memberships through `app_mem_piR`, whose `v = 0` fibre
  premise is the type reading's `AnnotValid` — the literal tier's
  establishment move, reused (`NatEqsP.lean`'s finding: no bit
  positivity is ever needed).
* **The laws carry their readings** (`∃ TVa, …`), the `NatOps`
  pattern: establishment stores the instantiated type's reading at
  its own environment; preservation transfers it *forward*
  (`denoteMeta_cons_fresh_mono`); consumers identify it with their own
  reading by determinism.  The equality-form crossing is refutable
  at support-completing installs (the `LitStabilityP` lesson), so no
  backward transfer ever appears.
* **The fired content is value-level** (the divmod-leg lesson): `ts`,
  `x`, `y` are bare `V`s, and the fabricated η spine is
  `projSpines`/`etaFabArgsV` — `projSpinesV`/`etaFabArgsV`
  (`Rel.lean:98/106`) with `cval`-leaves replaced by `interp` values
  of the `acval` leaves at the same assignment.

**Establishment**: at the inductive install — `IndStepPB`'s bill (the
routed bundle already owes the whole `EnvModelM` at an `indDecl` cons;
this adds no census entry).  The v1 establishment path is the
capability pipeline (kernel pin → `EtaPins` → rule_fold → `ModeledOk`
law → cert+sound, `Install/EtaLawS.lean`); the P path re-runs its
defeq certificates through the claims — the run-certificate route —
when the ind tier lands.  Consumers: the structure-η and unit-like
rules' soundness (`DefEq.structEta_sound`/`DefEq.structUnit_sound`,
`Model/Rules/DefEqSound.lean`; the `Steps/CapsRows.lean` rows until
the task #305 closing). -/

/-- **The annotated telescope fit** (`TeleFitV`'s `interp` mirror):
each argument value inhabits its progressively-peeled domain, the
peeled body read under the extended environment.  No positivity — the
squash-regime products fit too, and consumers recover memberships
through `app_mem_piR` with the validity fibre facts. -/
inductive TeleFit (V : Type w) [SetTheory V] :
    (Nat → V) → AnnotTerm → List V → V → Prop where
  | nil {ρ : Nat → V} {T : AnnotTerm} : TeleFit V ρ T [] (interp V ρ T)
  | cons {ρ : Nat → V} {u v : Nat} {A B : AnnotTerm} {a : V}
      {as : List V} {rest : V} :
      a ∈ˢ interp V ρ A →
      TeleFit V (cons a ρ) B as rest →
      TeleFit V ρ (.pi u v A B) (a :: as) rest

section
variable {V : Type w} [SetTheory V]

/-- The empty fit pins its residual (the inversion `cases` cannot do
in place, because the fit's type index is not a variable there). -/
theorem teleFit_nil_inv {ρ : Nat → V} {T : AnnotTerm} {rest : V}
    (h : TeleFit V ρ T [] rest) : rest = interp V ρ T := by
  cases h; rfl

end

/-- The projection spines' values: each stored projection function
applied to the type arguments and the stuck member
(`projSpinesV`'s value level). -/
@[expose] noncomputable def projSpines {V : Type w} [SetTheory V]
    (val : Name → V) (T : Name) (ts : List V) (b : V) (nF : Nat) :
    List V :=
  (List.range nF).map fun j =>
    (ts ++ [b]).foldl SetTheory.app (val (projFnName T j))

/-- The fabricated η spine's values (`etaFabArgsV`'s value level). -/
@[expose] noncomputable def etaFabArgsV {V : Type w} [SetTheory V]
    (val : Name → V) (T : Name) (ts : List V) (b : V) (nF : Nat) :
    List V :=
  ts ++ projSpines val T ts b nF

/-- **The fired structural-η law of an η-capable stored family**
(`EtaLawV`'s mirror; see the note above for the shape). -/
@[expose] def EtaLaw {V : Type w} [SetTheory V] {env : Env}
    (m : EnvModel V env) (φ' : Name → Nat) (T : Name)
    (cvT : ConstantVal) (caps : IndCaps) : Prop :=
  ∀ us : List Level, us.length = cvT.levelParams.length →
  ∃ TVa : AnnotTerm,
    denoteMeta m.acval env φ' 0
      (cvT.type.instantiateLevelParams cvT.levelParams us)
      = some TVa ∧
    (∀ ρ : Nat → V, WellDenotedV V ρ TVa) ∧
    ∀ (ρ : Nat → V) (ts : List V) (rest : V) (x : V),
      ts.length = caps.etaParams →
      TeleFit V ρ TVa ts rest →
      x ∈ˢ ts.foldl SetTheory.app
        (interp V ρ (m.acval T (Level.substFn φ' cvT.levelParams us))) →
      x = (etaFabArgsV
            (fun n => interp V ρ
              (m.acval n (Level.substFn φ' cvT.levelParams us)))
            T ts x caps.etaFields).foldl SetTheory.app
          (interp V ρ
            (m.acval caps.etaCtor
              (Level.substFn φ' cvT.levelParams us)))

/-- **The fired unit-like law of a unit-like stored family**
(`UnitLawV`'s mirror). -/
@[expose] def UnitLaw {V : Type w} [SetTheory V] {env : Env}
    (m : EnvModel V env) (φ' : Name → Nat) (T : Name)
    (cvT : ConstantVal) (caps : IndCaps) : Prop :=
  ∀ us : List Level, us.length = cvT.levelParams.length →
  ∃ TVa : AnnotTerm,
    denoteMeta m.acval env φ' 0
      (cvT.type.instantiateLevelParams cvT.levelParams us)
      = some TVa ∧
    (∀ ρ : Nat → V, WellDenotedV V ρ TVa) ∧
    ∀ (ρ : Nat → V) (ts : List V) (rest : V) (x y : V),
      ts.length = caps.unitParams →
      TeleFit V ρ TVa ts rest →
      x ∈ˢ ts.foldl SetTheory.app
        (interp V ρ (m.acval T (Level.substFn φ' cvT.levelParams us))) →
      y ∈ˢ ts.foldl SetTheory.app
        (interp V ρ (m.acval T (Level.substFn φ' cvT.levelParams us))) →
      x = y

/-- **The stored families' capability laws at `interp`**
(`CapsOkV`'s mirror, keyed identically; established at the inductive
install — `IndStepPB`'s bill). -/
@[expose] def CapsOk {V : Type w} [SetTheory V] {env : Env}
    (m : EnvModel V env) : Prop :=
  (∀ (T : Name) (cvT : ConstantVal) (caps : IndCaps),
    env.find? T = some (.indInfo cvT caps) → caps.eta = true →
    ConLeche.reservedBasisNames.contains T = false →
    ConLeche.EtaFamilyStored env T caps →
    ∀ φ' : Name → Nat, EtaLaw m φ' T cvT caps) ∧
  -- The unit half carries NO `EtaFamilyStored` premise — exactly as
  -- v1's `CapsOkV` unit half (`Sound/Motives.lean:315`).  The freeze
  -- transcribed the eta half's premise here by mistake; the caps
  -- batch mechanized the refutation (`etaFamilyStored_not_derivable`:
  -- a WF environment with a non-reserved unitlike-only family where
  -- the premise is false and the law vacuous), and the deletion was
  -- ratified — it strengthens the field, consumers and the
  -- `IndStepPB` establishment unchanged.
  (∀ (T : Name) (cvT : ConstantVal) (caps : IndCaps),
    env.find? T = some (.indInfo cvT caps) → caps.unitlike = true →
    ConLeche.reservedBasisNames.contains T = false →
    ∀ φ' : Name → Nat, UnitLaw m φ' T cvT caps)

/-! ## The fired modeled-iota contract (task #161, iota tier)

`RecRuleLawV`/`RecRulesV`'s mirror (`Sound/Motives.lean:145/207`) at
the validated-annotation currency.  This is the campaign's long pole;
the statement-freeze discipline is at its strictest here, and every
deviation from the v1 shape is a recorded decision:

* **The law stays `AnnotTerm`-indexed**, exactly as `RecRuleLawV` is
  `Term`-indexed.  The caps/divmod value-level lesson does NOT
  transfer: the truthfulness transport is inherently about the
  applied reduct's *reading* (the producing `IotaStep` row must hand
  the whnf loop a graded reading), and `WellDenotedV` is `AnnotTerm`-indexed.
  An earlier value-level draft of this block died on exactly that
  conjunct.
* **`TeleFitPA` is `TeleFitV`'s transpose, substitution-peeling** —
  `B.inst a` at the argument's *reading*, one ambient environment,
  exactly v1's shape one currency over.  The consumer-validation pass
  killed the earlier cons-environment draft: its residual diverged
  syntactically from the substituted readings the certificate's
  `defEqList` runs compare, re-opening the seal-22 gap the fit was
  meant to close.  Substitution-peeling is available here because the
  arguments are readings (the caps tier's `TeleFit` had bare values
  and could not substitute — hence its `teleFit_of_inst` detour,
  which this fit never needs): `denoteMeta_beta` gives the residual
  identity (`Tele.residual`'s mirror) directly, and the index pin
  decomposes the residual at the ambient environment, v1-verbatim.
* **The `.nested` pin clause quantifies the pin's own open reading**
  (`denoteMeta` at depth `rP`), concluding at the reading substituted
  along the argument prefix — `AnnotTerm.instRevChain`, the exact v1
  spelling one currency over.  The consumer's bridge is then the
  `denoteMeta` mirror of the existing `denote_openRev`/
  `denote_openRev_base` pair (`Verify/Denote/OpenRevDenote.lean`);
  the supplier converts the recorded comparand runs through the
  claims.
* **The fired equality is present** (the seal-22 draft omitted it),
  and the transport clause is `RecRuleLawV`'s final conjunct verbatim
  at the new currency.
* The law **carries the RHS reading** (`∃ Ra`), with the bare-`R`
  grading unconditional (the seal-22 correction; the
  `NatOps`/caps carried-reading pattern — establishment stores,
  preservation transfers forward, consumers identify by determinism).

The statements are FROZEN (task #161, after the consumer validation
pass); they landed in `Interp/IotaLawP.lean` and moved here verbatim
when `RecRules` became an `EnvModelM` field, exactly as the caps
statements did — the field must mention them and `IotaLawP` imported
this file.

**Establishment**: the inductive install — `IndStepPB`'s bill, where
the flagged new mathematics lives (a `Prop`-valued motive's minors at
the squash regime).  **Consumers**: the ι rule's soundness
(`Red.iota_sound`, `Model/Rules/IotaSound.lean`; the `IotaStep`/
`IotaReads` rows of `Steps/{Whnf,Reads,IotaRows}.lean` until the task
#305 closing). -/

/-- **The annotated telescope fit** (`TeleFitV`'s transpose,
substitution-peeling): each argument reading inhabits its
progressively-substituted domain, one ambient environment, the
residual an `AnnotTerm` at that environment. -/
inductive TeleFitPA (V : Type w) [SetTheory V] (ρ : Nat → V) :
    AnnotTerm → List AnnotTerm → AnnotTerm → Prop where
  | nil {T : AnnotTerm} : TeleFitPA V ρ T [] T
  | cons {u v : Nat} {A B rest : AnnotTerm} {a : AnnotTerm}
      {as : List AnnotTerm} :
      interp V ρ a ∈ˢ interp V ρ A →
      TeleFitPA V ρ (B.inst a) as rest →
      TeleFitPA V ρ (.pi u v A B) (a :: as) rest

/-- A fit's prefix fits, to some intermediate residual
(`TeleFitV.take`).  Lives beside the inductive: the part-6 probe
repair's consumer (`IotaRowsP`) needs it upstream of the stage kits. -/
theorem TeleFitPA.take {V : Type w} [SetTheory V] {ρ : Nat → V} :
    ∀ {T rest : AnnotTerm} {as : List AnnotTerm}, TeleFitPA V ρ T as rest →
      ∀ n : Nat, ∃ mid, TeleFitPA V ρ T (as.take n) mid := by
  intro T rest as h
  induction h with
  | @nil T' =>
    intro n
    refine ⟨T', ?_⟩
    rw [List.take_nil]
    exact TeleFitPA.nil
  | @cons u v A B rest' a as' hmem htail ih =>
    intro n
    cases n with
    | zero => exact ⟨_, TeleFitPA.nil⟩
    | succ n =>
      obtain ⟨mid, hm⟩ := ih n
      exact ⟨mid, TeleFitPA.cons hmem hm⟩

/-- The annotated reverse-opening substitution chain
(`Term.instRevChain`'s `AnnotTerm` twin, `Verify/Denote/OpenVars.lean:80`
— outermost argument consumed first, each at cut `0`, lifted past the
arguments still to come). -/
@[expose] def _root_.ConLeche.Model.AnnotTerm.instRevChain :
    List AnnotTerm → AnnotTerm → AnnotTerm
  | [], X => X
  | v :: vs, X =>
    ConLeche.Model.AnnotTerm.instRevChain vs (X.inst (v.liftN vs.length) 0)

/-- **The constructor residual's index pin** (`IotaIndexPinV`'s
mirror, v1-verbatim at `AnnotTerm`): the residual decomposes as a spine
whose trailing arguments agree with the recursor's index arguments,
all at the ambient environment. -/
@[expose] def IotaIndexPin {V : Type w} [SetTheory V] (ρ : Nat → V)
    (restC : AnnotTerm) (cnP mI rP : Nat) (xs : List AnnotTerm) : Prop :=
  ∃ (Ha : AnnotTerm) (cargsa : List AnnotTerm),
    restC = AnnotTerm.mkAppN Ha cargsa ∧
    (mI = rP ∨ cargsa.length = cnP + (mI - rP)) ∧
    ∀ i, i < mI - rP →
      interp V ρ (cargsa.getD (cnP + i) default)
        = interp V ρ (xs.getD (rP + i) default)

/-- **One rule's fired modeled-iota contract at `interp`**
(`RecRuleLaw`; `RecRuleLawV`'s mirror — see the note above for
every deviation). -/
@[expose] def RecRuleLaw {V : Type w} [SetTheory V] {env : Env}
    (m : EnvModel V env) (φ : Name → Nat)
    (n : Name) (cv : ConstantVal) (mI rP : Nat) (rl : RecRule) :
    Prop :=
  rP ≤ mI ∧
  ∀ us : List Level, us.length = cv.levelParams.length →
    ∃ Ra : AnnotTerm,
      denoteMeta m.acval env φ 0
        ((RecRule.rhs rl).instantiateLevelParams cv.levelParams us)
        = some Ra ∧
      (∀ ρ : Nat → V, WellDenotedV V ρ Ra) ∧
      -- The nested pins' open readings are carried with a
      -- CONTEXT-GUARDED chain grading (task #161 part-6 probe
      -- repair, ratified: the unconditional `∀ ρ` form was REFUTED —
      -- `not_uniform_wellDenoted_open_app` — because the checker's
      -- `checkAnnotList` certificate is about `pinsP`, the pins
      -- instantiated at the public frame, and converts only
      -- context-guarded).  The grading is stated of the chained term
      -- the equality half names, at the chain's own environment:
      -- `TeleFitPA` is that environment's `Sat` in closed form.
      -- It stays an OUTER conjunct (the consumer feeds it to
      -- `DefEqClaim` to *produce* the equality clause consumed
      -- by the inner block — inner placement is circular).
      (∀ lvls pins, RecRule.fire rl = .nested lvls pins →
        ∀ i, i < RecRule.ctorParams rl →
        ∃ vpa : AnnotTerm,
          denoteMeta m.acval env φ rP
            (ConLeche.Verify.openRev 0 rP
              ((pins.getD i default).instantiateLevelParams
                cv.levelParams us)) = some vpa ∧
          ∀ (ρ : Nat → V) (zs : List AnnotTerm) (TVa restR : AnnotTerm),
            zs.length = rP →
            (∀ z ∈ zs, WellDenotedV V ρ z) →
            denoteMeta m.acval env φ 0
              (cv.type.instantiateLevelParams cv.levelParams us)
              = some TVa →
            TeleFitPA V ρ TVa zs restR →
            WellDenotedV V ρ
              (ConLeche.Model.AnnotTerm.instRevChain zs vpa)) ∧
      ∀ (cvj : ConstantVal) (cnP cnF : Nat),
        env.find? (RecRule.ctor rl) = some (.ctorInfo cvj cnP cnF) →
      ∀ (usj : List Level) (ρ : Nat → V) (xs ys : List AnnotTerm)
        (TVa TVja restR restC : AnnotTerm),
        xs.length = mI →
        ys.length = RecRule.ctorParams rl + RecRule.nfields rl →
        usj.length = cvj.levelParams.length →
        Level.substFn φ cvj.levelParams usj
          = Level.substFn φ cvj.levelParams
              (ConLeche.recFireComparands rl cv.levelParams us
                cvj.levelParams [] rP).1 →
        -- the ι step's parameter comparison, supplied only for a rule
        -- that is not `paramsBlind`
        (RecRule.paramsBlind rl = false → RecRule.fire rl = .plain →
          ∀ i, i < RecRule.ctorParams rl → i < mI →
            interp V ρ (ys.getD i default)
              = interp V ρ (xs.getD i default)) →
        (∀ lvls pins, RecRule.fire rl = .nested lvls pins →
          ∀ i, i < RecRule.ctorParams rl →
          ∀ vpa : AnnotTerm,
            denoteMeta m.acval env φ rP
              (ConLeche.Verify.openRev 0 rP
                ((pins.getD i default).instantiateLevelParams
                  cv.levelParams us)) = some vpa →
            interp V ρ (ys.getD i default)
              = interp V ρ
                  (ConLeche.Model.AnnotTerm.instRevChain (xs.take rP)
                    vpa)) →
        IotaIndexPin (V := V) ρ restC (RecRule.ctorParams rl)
          mI rP xs →
        denoteMeta m.acval env φ 0
          (cv.type.instantiateLevelParams cv.levelParams us)
          = some TVa →
        denoteMeta m.acval env φ 0
          (cvj.type.instantiateLevelParams cvj.levelParams usj)
          = some TVja →
        TeleFitPA V ρ TVa
          (xs ++ [AnnotTerm.mkAppN
            (m.acval (RecRule.ctor rl)
              (Level.substFn φ cvj.levelParams usj)) ys]) restR →
        TeleFitPA V ρ TVja ys restC →
        interp V ρ
            (AnnotTerm.mkAppN
              (m.acval n (Level.substFn φ cv.levelParams us))
              (xs ++ [AnnotTerm.mkAppN
                (m.acval (RecRule.ctor rl)
                  (Level.substFn φ cvj.levelParams usj)) ys]))
          = interp V ρ
              (AnnotTerm.mkAppN Ra
                (xs.take rP ++ ys.drop (RecRule.ctorParams rl))) ∧
        ((∀ a ∈ xs, WellDenotedV V ρ a) → (∀ b ∈ ys, WellDenotedV V ρ b) →
          WellDenotedV V ρ
            (AnnotTerm.mkAppN Ra
              (xs.take rP ++ ys.drop (RecRule.ctorParams rl))))

/-- The fired modeled-iota contract, keyed on every stored recursor
(`RecRulesV`'s mirror). -/
@[expose] def RecRules {V : Type w} [SetTheory V] {env : Env}
    (m : EnvModel V env) (φ : Name → Nat) : Prop :=
  ∀ (n : Name) (cv : ConstantVal) (mI rP : Nat)
    (rules : List RecRule),
    env.find? n = some (.recInfo cv mI rP rules) →
    ∀ rl ∈ rules, RecRule.fire rl ≠ .inert →
      RecRuleLaw m φ n cv mI rP rl

/-! ## The tower projection law (task #175 wiring, W5)

A projection-table entry (the direct-structure install's native
entries — task #175 tower-flag: the only ones) is typed by the checker
generically — the stored `ty` peeled along the parameters and the
subject (`inferBody`'s tower branch) — and reduced by the structural
rule `proj_i (ctor p⃗ x⃗) ↦ x_i`; the reading is the uniform
`projAV i` (`denoteMeta`'s tower branch).  The P `.proj` rows therefore
need, per stored tower entry, exactly two semantic facts about the
environment: the **typing law** (the projection of a member of the
family lands in the peeled entry type's reading, graded) and the
**iota law** (the projection of a certified constructor spine is the
selected field's reading).  Both are **environment laws** in the sense
of `caps_ok`/`rec_rules` — fixed by the direct install and by nothing
else — so they are a field of `EnvModelM`, established at the install
(`Model/StructInstallP`, W4c) and transported across every other cons
(`towerOk_cons_fresh`, `Model/RecRulesCons.lean`).

**Why the typing law is stated over a syntactic peel** (`peelPis`)
rather than a `TeleFitPA` fit: the `.proj` infer row holds the
subject's *reduced type* as a graded reading (`WellDenotedV` of the family
application) and the subject's membership in it — never a certified
parameter spine, since the family application is a *type* the run
produced, not an application it checked.  Building a fit from the
grading alone would need the leaf's λ-domains pinned to the type
reading's Π-domains at every row; the law takes the grading and the
membership as its premises instead, and the install discharges the
pinning once.  The residual is then the *syntactic* peel of the
entry-type reading along the readings (`denoteP_piResidual_peel`,
the fit-free mirror of `teleFitPA_residual`), which the row computes
from the checker's own `instPisAt` run.

The iota law takes the constructor application's grading alone (see
its clause). -/

/-- The syntactic Π-peel along a list of readings: the fit's residual
without the memberships (`TeleFitPA`'s spine, data only). -/
@[expose] def _root_.ConLeche.Model.AnnotTerm.peelPis : AnnotTerm → List AnnotTerm → Option AnnotTerm
  | T, [] => some T
  | .pi _ _ _ B, a :: as => ConLeche.Model.AnnotTerm.peelPis (B.inst a) as
  | _, _ :: _ => none

/-- A fit's residual is the peel's. -/
theorem TeleFitPA.peelPis {V : Type w} [SetTheory V] {ρ : Nat → V} :
    ∀ {T rest : AnnotTerm} {as : List AnnotTerm}, TeleFitPA V ρ T as rest →
      ConLeche.Model.AnnotTerm.peelPis T as = some rest := by
  intro T rest as h
  induction h with
  | nil => rfl
  | cons _ _ ih => exact ih

/-- **The structural-η law of a tower-backed family** (task #175 W4c;
`EtaLaw`'s twin at the tower kind, keyed on the entry): a member of
the family instance is the constructor at the parameters and the tower
readings (`projS`) of its own projections — the value-level content of
the η certificate's `.proj T j b` fabrication (`etaProjs`).  Keyed on
the entry so that the direct install alone answers it (the modeled
route stores no tower entries); the η row reads it through slot `0` of
an all-tower family. -/
@[expose] def TowerEtaLaw {V : Type w} [SetTheory V] {env : Env}
    (m : EnvModel V env) (φ : Name → Nat) (T : Name)
    (entry : ProjEntry) : Prop :=
  ∀ (cvT : ConstantVal) (capsT : IndCaps),
    env.find? T = some (.indInfo cvT capsT) →
    ∀ us : List Level, us.length = entry.levelParams.length →
    ∃ TVa : AnnotTerm,
      denoteMeta m.acval env φ 0
        (cvT.type.instantiateLevelParams cvT.levelParams us) = some TVa ∧
      (∀ ρ : Nat → V, WellDenotedV V ρ TVa) ∧
      ∀ (ρ : Nat → V) (ts : List V) (rest : V) (x : V),
        ts.length = entry.numParams →
        TeleFit V ρ TVa ts rest →
        x ∈ˢ ts.foldl SetTheory.app
          (interp V ρ (m.acval T (Level.substFn φ entry.levelParams us))) →
        x = (ts ++ (List.range entry.numFields).map fun j =>
              ConLeche.SetTheory.Tower.projS (j + entry.off) x).foldl SetTheory.app
            (interp V ρ
              (m.acval entry.ctor (Level.substFn φ entry.levelParams us)))

/-- **The `Prop` guard at a use's valuation** (task #175 W4c/O4): if
the structure is a proposition there, so is the field's guard level.
The typing and iota laws of a tower entry hold under it — a data
field of a `Prop`-declared structure has no projection law (its value
is not the point).  Consumers discharge it from the kernel's syntactic
guard (`inferTypeCore`'s tower branch, `ProjEntry.fireOk`) through
`towerGuardAt_of`. -/
@[expose] def TowerGuardAt (φ : Name → Nat) (entry : ProjEntry) (us : List Level) :
    Prop :=
  Level.eval (Level.substFn φ entry.levelParams us) entry.structSort = 0 →
    Level.eval (Level.substFn φ entry.levelParams us) entry.fieldSort = 0

/-- **The O5 conjunct**: a non-`Prop` family's guard level is bounded
by its result sort at every valuation (the field sorts are checked
`≤` the result sort, `checkStructFieldSorts`), so the guard holds
wherever the structure happens to be a proposition. -/
@[expose] def TowerO5 (entry : ProjEntry) : Prop :=
  (Level.isEquiv entry.structSort .zero == some true) = false →
    ∀ ψ : Name → Nat,
      Level.eval ψ entry.structSort = 0 → Level.eval ψ entry.fieldSort = 0

/-- The guard at a valuation, from the kernel's syntactic guard and O5. -/
theorem towerGuardAt_of {entry : ProjEntry} {us : List Level} {φ : Name → Nat}
    (hO5 : TowerO5 entry)
    (hg : (Level.isEquiv entry.structSort .zero == some true) = true →
      (Level.isEquiv (Level.subst entry.levelParams us entry.fieldSort) .zero
        == some true) = true) :
    TowerGuardAt φ entry us := by
  intro hs
  by_cases hp : (Level.isEquiv entry.structSort .zero == some true) = true
  · have h1 := Level.isEquiv_sound (beq_iff_eq.mp (hg hp)) φ
    rw [Level.eval_subst] at h1
    simpa [Level.eval] using h1
  · exact hO5 (by simpa using hp) _ hs

/-- **The guard at a valuation, from the fire guard** (task #175 W6):
`whnfCore`'s tower fire (`ProjEntry.fireOk`) is the tower infer
branch's own guard — a `Prop`-declared family fires only where the
field's guard level is a proposition, any other family unconditionally
— so with O5 it yields `TowerGuardAt` exactly as the infer branch
does.  (Until W6 the fire was gated on the structure's sort being
provably nonzero, `TowerStructPos`, and the iota law was stated in the
graph regime only; the squash regime is now licensed by the certified
spine's fit, see `TowerEntryLaw`'s clause (B).) -/
theorem towerGuardAt_of_fireOk {entry : ProjEntry} {us : List Level}
    {φ : Name → Nat} (hO5 : TowerO5 entry)
    (hfire : entry.fireOk us = true) : TowerGuardAt φ entry us := by
  unfold ProjEntry.fireOk at hfire
  refine towerGuardAt_of hO5 (fun hp => ?_)
  rw [hp] at hfire
  simpa using hfire

/-- **One tower-backed entry's projection law** (see the section
docstring): the entry's stored data agrees with the stored former and
constructor (whose η capability is the entry's at a non-`Prop` family
— task #175 W4c/O4), the O5 bound, and at every level instantiation
the typing law and the iota law hold under the `Prop` guard at the
entry's own body reading and the constructor's, and the family's
structural-η law holds (clause (C), `TowerEtaLaw`).

Task #175 S1: the entry stores a *body* scoped at the parameters and
the subject, not a type; the typing law is stated over the reading
of `projTele (nP + 1) body` — the body under `nP + 1` dummy binders
(`ConLeche/Verify/ProjTele.lean`) — whose `instPisAt` peel along the
parameters and the subject is exactly the checker's one
`instantiateList` (`ProjEntry.typeAt`, `instPisAt_typeAt`).  The
dummy binders carry the reading only; the law never reads them. -/
@[expose] def TowerEntryLaw {V : Type w} [SetTheory V] {env : Env}
    (m : EnvModel V env) (φ : Name → Nat)
    (T : Name) (i : Nat) (entry : ProjEntry) : Prop :=
  entry.structName = T ∧ entry.idx = i ∧
  i < entry.numFields ∧
  (∃ (cvT : ConstantVal) (capsT : IndCaps),
    env.find? T = some (.indInfo cvT capsT) ∧
    cvT.levelParams = entry.levelParams ∧
    -- the η record, IF the family claims η (task #210 Part A: a
    -- recursive structure-like stores a table but claims no η —
    -- official's `is_structure_like` has `!is_rec`): the family is
    -- not a proposition, and the record names this table's shape
    (capsT.eta = true →
      (Level.isEquiv entry.structSort .zero == some true) = false ∧
      capsT.etaCtor = entry.ctor ∧
      capsT.etaParams = entry.numParams ∧
      capsT.etaFields = entry.numFields)) ∧
  TowerO5 entry ∧
  ∃ cvC : ConstantVal,
    env.find? entry.ctor
      = some (.ctorInfo cvC entry.numParams entry.numFields) ∧
    cvC.levelParams = entry.levelParams ∧
    (∀ us : List Level, us.length = entry.levelParams.length →
      -- (A) the typing law
      (∃ Ta : AnnotTerm,
        denoteMeta m.acval env φ 0
          (ConLeche.projTele (entry.numParams + 1)
            (entry.body.instantiateLevelParams entry.levelParams us)) = some Ta ∧
        (TowerGuardAt φ entry us →
        ∀ (ρ : Nat → V) (vs : List AnnotTerm) (x rest : AnnotTerm),
          vs.length = entry.numParams →
          WellDenotedV V ρ (AnnotTerm.mkAppN
            (m.acval T (Level.substFn φ entry.levelParams us)) vs) →
          WellDenotedV V ρ x →
          interp V ρ x ∈ˢ interp V ρ (AnnotTerm.mkAppN
            (m.acval T (Level.substFn φ entry.levelParams us)) vs) →
          ConLeche.Model.AnnotTerm.peelPis Ta (vs ++ [x]) = some rest →
          WellDenotedV V ρ (projAV (i + entry.off) x) ∧ WellDenotedV V ρ rest ∧
            interp V ρ (projAV (i + entry.off) x) ∈ˢ interp V ρ rest)) ∧
      -- (B) the iota law: the projection of a *graded* constructor
      -- application is the selected field, at every valuation under
      -- the guard (task #175 W6).  Two premises: the application's
      -- grading (its slot chain — the graph regime's whole premise,
      -- where every constructor binder is graph-regime and graph
      -- rigidity pins the memberships), and the certified spine's fit
      -- against the constructor's own type reading (`projCert`'s
      -- `iotaCerts`, through `certs_tele`) — the squash regime's
      -- premise, where the application is the point and the fit pins
      -- the selected field to a proposition's domain (its sort is `0`
      -- there: the O5 bound at a non-`Prop` family, the guard at a
      -- `Prop`-declared one).
      (∃ TCa : AnnotTerm,
        denoteMeta m.acval env φ 0
          (cvC.type.instantiateLevelParams cvC.levelParams us) = some TCa ∧
        (TowerGuardAt φ entry us →
        ∀ (ρ : Nat → V) (ys : List AnnotTerm) (rest : V),
        ys.length = entry.numParams + entry.numFields →
        WellDenotedV V ρ (AnnotTerm.mkAppN
          (m.acval entry.ctor (Level.substFn φ entry.levelParams us)) ys) →
        TeleFit V ρ TCa (ys.map (interp V ρ)) rest →
        interp V ρ (projAV (i + entry.off) (AnnotTerm.mkAppN
            (m.acval entry.ctor (Level.substFn φ entry.levelParams us)) ys))
          = interp V ρ (ys.getD (entry.numParams + i) default)))) ∧
    -- (C) the structural-η law (task #175 W4c)
    TowerEtaLaw m φ T entry

/-- **The tower projection law, keyed on every stored entry**
(`RecRules`'s sibling).  Task #175 tower-flag: every stored table is
a real one, so the law is uniform — no flag premise. -/
@[expose] def TowerOk {V : Type w} [SetTheory V] {env : Env}
    (m : EnvModel V env) (φ : Name → Nat) : Prop :=
  ∀ (T : Name) (i : Nat) (entry : ProjEntry),
    env.findProj? T i = some entry →
    TowerEntryLaw m φ T i entry

/-! ## The install-tier residues (from `Model/Steps/*`, task #305 closing) -/

/-- **The leaf-validity residue** (the P tier's one new routed
obligation): every stored leaf of the annotated valuation is
bit-valid.  The `WellDenoted` half is already an `EnvModelU` field
(`acval_wellDenoted`); this is its `AnnotValid` companion, to be discharged
at the install tier — a stored type's annotations went through the
checker's own front door, which is establishment — and folded into the
environment structure there (with the owed `EnvWF` records, if the
seal's invariants state them naturally). -/
@[expose] def AcvalValid {env : Env} (m : EnvModel V env) : Prop :=
  ∀ (n : Name) (ψ : Name → Nat) (ρ : Nat → V),
    AnnotValid V ρ (m.acval n ψ)

/-- **The `const` clause's residue, P currency** (`ConstType2C`
transposed: no fuel, `WellDenotedV` conclusion). -/
@[expose] def ConstType {env : Env} (m : EnvModel V env)
    (φ : Name → Nat) : Prop :=
  ∀ (d : Nat) (n : Name) (ci : ConLeche.ConstantInfo) (us : List Level),
    env.find? n = some ci → ci.isTowerEntry = false →
    us.length = ci.toConstantVal.levelParams.length →
    ∃ ta,
      denoteMeta m.acval env φ d
        (ci.toConstantVal.type.instantiateLevelParams
          ci.toConstantVal.levelParams us) = some ta ∧
      (∀ ρ : Nat → V, WellDenotedV V ρ ta) ∧
      ∀ ρ : Nat → V,
        interp V ρ (m.acval n
            (Level.substFn φ ci.toConstantVal.levelParams us))
          ∈ˢ interp V ρ ta

/-- **The `Nat`-literal clause's residue, over the core**
(`Steps/InferQ.lean`'s `NatHeads2`, body for body): the zero's
membership and the successor's, at the annotated valuation's own
`Nat` leaf. -/
@[expose] def NatHeads {env : Env} (m : EnvModel V env)
    (φ : Name → Nat) : Prop :=
  ConLeche.natLitSupported env = true →
  ∀ ρ : Nat → V,
    interp V ρ (m.acval natZeroName (Level.substFn φ [] []))
      ∈ˢ interp V ρ (m.acval natName (Level.substFn φ [] [])) ∧
    interp V ρ (m.acval natSuccName (Level.substFn φ [] []))
      ∈ˢ piR 1 (interp V ρ (m.acval natName (Level.substFn φ [] [])))
        (fun _ => interp V ρ
          (m.acval natName (Level.substFn φ [] [])))

/-- **The unfolding supplier the P-tier delta exit consumes**: a stored
definition's validated annotation *is* the constant's own leaf, at
every level assignment.  Definitions only: a theorem is opaque to
reduction (`unfoldDefinition` has no `thmInfo` arm), so the invariant
keeps no equation between a theorem's value and its leaf — the leaf is
an inhabitant of the statement, and that is all the install
establishes.

Routed.  The install tier discharges it; `acvalDefnInst_noParams`
(`Steps/Whnf.lean`) is the canonical tier's evidence that the shape is
inhabited well beyond vacuity, and the P shape asks for *less* than
that one (no `us`, no instantiation). -/
@[expose] def AcvalDefnInst {env : Env} (m : EnvModel V env) : Prop :=
  ∀ (ψ : Name → Nat) (cv : ConstantVal) (value : Expr),
    (∃ hint : ReducibilityHint,
      ConstantInfo.defnInfo cv value hint ∈ env.consts) →
    denoteMeta m.acval env ψ 0 value = some (m.acval cv.name ψ)

end ConLeche.Model
