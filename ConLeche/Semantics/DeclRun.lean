module

public import ConLeche.Semantics.Decl

@[expose] public section

/-!
# `DeclRun` — the run/guard projection of `DeclR` (task #161 S4, THE
SEPARATION; the design census's **C3**)

The layering diagram's own sentence about the shared base reads

> bridge RECORDS (`SetR/Decl.lean`: run conjuncts → P, derivation
> conjuncts → R)

and this module is that split made into a statement.  `DeclR`
(`SetBase/Decl.lean`) is *one* record family with *two* kinds of
conjunct:

* **guards and runs** — `Bool` side conditions on stored data,
  `annotateCore`/`inferTypeCore`/`isDefEqCore`/`ensureSortCore`
  verdicts, and the `env₂ = ⟨… :: env.consts⟩` shapes.  These mention
  no valuation at all.  They are what the P lane consumes (task #161
  P4 H1 widened `DeclR` five times precisely to record them);
* **derivations** — the trailing `∀ φ : Name → Nat, ∃ …, denote cval
  … ∧ Infer … ∧ DefEq …` conjuncts.  These are keyed by a
  `TConstVal` and are what the *collapsed* lane's installs consume.

`DeclRun` below is `DeclR` with the second kind deleted.  It is
**valuation-free**: no `cval` parameter, no `denote`, no `Infer`, no
`DefEq`, no `V`.  `DeclR.toRun` projects onto it, so the records stay
shared and single-sourced: the R lane keeps proving `DeclR` (nothing
in `Bridge/*` moves), and the P lane states over the projection.

**Which conjuncts it carries, and why each** (the seal's table; every
one is read off a measured consumer, per D6's house rule that no
statement is frozen before a consumer has exercised it):

| record | dropped | kept, and its P consumer |
|---|---|---|
| `ConstantValR` | the `∀ φ, ∃ Tv tT u, denoteClosed … ∧ Infer … ∧ DefEq …` front door | the six freshness/reservation/level/scoping guards (`hfresh` at every harvest and at `declEtaStep`), the annotate output (`annotate_syntax`), the two `allLevelParamsDefined`/`constsResolve` guards, and H1's own run chain `∃ stype u, inferTypeCore … ∧ ensureSortCore …` (the type's reading, through `acceptedReads_of`) |
| `ValueFrontR` | the `∀ φ, ∃ Tv Vv tv, …` front door | the value's two syntactic guards, its annotate output, its two resolution guards, and H1's run **pair** `∃ vtype, inferTypeCore … ∧ isDefEqCore …` (the leaf's reading, and the membership crossing) |
| `NatEqsR` | **the whole relation** | replaced by its twin `NatEqsRun`, which `DeclDefnR` already carries beside it (H1); `natOps_install` consumes the runs |
| `DivModPinR` | nothing — it is already valuation-free (its `_cval` parameter is unused) | re-stated without the dead parameter as `DivModPinRun`; `divMod_install` consumes the guards and the certificate verdict |
| `ReducePinR` | the `∀ φ, ∃ E V, … DefEq …` identity | the three storage guards, both annotate outputs and the recorded identity-certificate run; `reduceOps_install` consumes exactly these |
| `DeclThmR` | the `∀ φ, ∃ Tv sT, … DefEq … (.sort 0)` is-a-proposition front | H1's prop-check run triple (`inferTypeCore` + `ensureSortCore` + `Level.isEquiv`) |
| `DeclAxiomR` | (via `ConstantValR`) | the four-way branch disjunction verbatim — pure stored-data guards |
| `DeclBasisRun` | nothing | re-used **verbatim**: it is already guards only |
| `DeclIndRun` | — | **not projected here.**  See the `Ind` parameter below. |

**The inductive kind is a parameter, not a projection.**  `DeclIndRun`'s
run/guard projection is not this batch's: S3's stop-and-name refuted
the census's C4 at `indDecl` (the block's η-closure is proved
*interleaved* with the model-carrying `indMembersS`/`indRecsS` folds),
and the same interleaving is what the ind kind's run projection has to
undo — S5's named "DeclIndS η-only unit".  Rather than freeze a
statement now and edit it then, `DeclRun` takes the inductive kind's
payload as a **`Prop`-valued parameter** `Ind`, exactly as `declStepS`
takes its five per-kind install obligations and as `declEtaStep`
(`SetBase/DeclEta.lean`) takes the ind kind's η-closure as its one
premise.  Today every caller instantiates `Ind := DeclIndRun μ F env
cval`; when the ind unit lands, callers instantiate `Ind :=
DeclIndRun μ F env` and **`DeclRun`'s own text does not change**.
-/

namespace ConLeche.Semantics

open ConLeche.Term ConLeche.Verify

/-! ## Shared syntactic plumbing

Moved here from `SetR/Install/ValueKinds.lean` at task #161 S4 (the
design census §3.3's last open split): the lemma is a pure
`annotateCore` inversion — no `EnvS`, no `V` — and it is the first
thing every consumer of a `*Run` record's annotate conjunct calls, on
both lanes. -/

/-- The annotate outputs' syntactic facts, packaged: no fvars, bounded,
from the annotate run and the input's own guards. -/
theorem annotate_syntax {μ : CheckMode} {F : Nat} {env : Env} {e e' : Expr}
    (hann : annotateCore μ env F 0 e = .ok e')
    (hef : e.hasFvar = false) (heb : e.looseBVarsBounded 0 = true) :
    e'.hasFvar = false ∧ e'.looseBVarsBounded 0 = true :=
  ⟨Expr.not_hasFvar_of_fvarsBelow_zero
      ((annotateCore_WScoped F e hann
        (Expr.WScoped.of_not_hasFvar hef)).fvarsBelow),
    annotateCore_looseBVars F e hann heb⟩

/-! ## The shared front doors, run half -/

/-- `ConstantValR`'s run/guard half: everything but the trailing
front-door derivation. -/
def ConstantValRun (μ : CheckMode) (F : Nat) (env : Env)
    (cv : ConstantVal) (type' : Expr) : Prop :=
  (env.find? cv.name).isNone = true ∧
  reservedBasisNames.contains cv.name = false ∧
  cv.name.isProjFnShape = false ∧
  Name.nodup cv.levelParams = true ∧
  cv.type.looseBVarsBounded 0 = true ∧
  cv.type.hasFvar = false ∧
  annotateCore μ env F 0 cv.type = .ok type' ∧
  type'.allLevelParamsDefined cv.levelParams = true ∧
  type'.constsResolve env = true ∧
  (∃ stype u, inferTypeCore μ env F 0 type' = .ok stype ∧
    ensureSortCore μ env F 0 stype = .ok u)

/-- `ValueFrontR`'s run/guard half: everything but the trailing
front-door derivation. -/
def ValueFrontRun (μ : CheckMode) (F : Nat) (env : Env)
    (cv : ConstantVal) (value : Expr) (type' value' : Expr) : Prop :=
  value.looseBVarsBounded 0 = true ∧
  value.hasFvar = false ∧
  annotateCore μ env F 0 value = .ok value' ∧
  value'.allLevelParamsDefined cv.levelParams = true ∧
  value'.constsResolve env = true ∧
  (∃ vtype, inferTypeCore μ env F 0 value' = .ok vtype ∧
    isDefEqCore μ env F 0 vtype type' = .ok true)

/-! ## The conditional pin packs, run half -/

/-- `DivModPinR` without its dead valuation parameter.  The pack was
already run-only (task #148 T6 recorded the reason: the pin comparison
is not transposed and the certificates enter as the checker's verdict),
so this is a re-statement, not a projection.

**The matched variant is existential and unlisted** (task #304): the
pack used to say `∃ ps ∈ natOpPinSets`, and the install gate's pin
list is now a parameter of the fold, so naming the shipped list here
would have tied the whole run tier to it.  Nothing downstream reads
the membership — the model's conversion (`divMod_install`,
`ConLeche/Model/DivModCert.lean`) is over an arbitrary
`ps : NatOpPinSet`, because what it consumes is the certificates'
verdict *in this environment* and not where the variant came from.  So
the pack says only that SOME variant's guards passed and certificates
checked, which is what an install at any pin list establishes. -/
def DivModPinRun (μ : CheckMode) (F : Nat) (env env₂ : Env)
    (c : Name) (value' : Expr) : Prop :=
  divModEnvGuard env₂ c = true ∧
  -- the pin variant that matched (task #273): its guards, its pin
  -- annotated, its certificates checked
  ∃ ps : NatOpPinSet,
    divModPinGuard ps env c = true ∧
    divModCertsGuard ps env c value' = true ∧
    ∃ pinA, annotateCore μ env F 0 (divModDeclPin ps c) = .ok pinA ∧
      checkDivModCerts (m := CheckM) (fueledOps μ F) env c value'
        (divModCertStmts c) (divModCertProofs ps c) = .ok true

/-- `ReducePinR`'s run/guard half: the storage guards, both annotate
outputs and the recorded identity-certificate run, without the
derivation the identity carries beside it. -/
def ReducePinRun (μ : CheckMode) (F : Nat) (env env₂ : Env)
    (c : Name) (value : Expr) : Prop :=
  reduceStoredOk env₂ c = true ∧
  reduceElemOk env c = true ∧
  reducePinGuard env c = true ∧
  ∃ valA pinA,
    annotateCore μ env F 0 value = .ok valA ∧
    annotateCore μ env F 0 (reduceDeclPin c) = .ok pinA ∧
    isDefEqCore μ env F 1 (.app valA (reduceCertVar c))
      (reduceCertVar c) = .ok true

/-! ## The value kinds, run half -/

/-- `DeclDefnR`'s run/guard half. -/
def DeclDefnRun (μ : CheckMode) (F : Nat) (env : Env)
    (cv : ConstantVal) (value : Expr) (hint : ReducibilityHint)
    (env₂ : Env) : Prop :=
  ∃ type' value',
    ConstantValRun μ F env cv type' ∧
    ValueFrontRun μ F env cv value type' value' ∧
    env₂ = ⟨.defnInfo ⟨cv.name, cv.levelParams, type'⟩ value' hint ::
      env.consts⟩ ∧
    (natOpNames.contains cv.name = true →
      natOpGuard env₂ cv.name = true ∧
      (natOpDeps cv.name).all (natOpStoredOk env₂) = true ∧
      NatEqsRun μ F env
        ((natOpEquations 0 cv.name).map fun eq =>
          (Expr.substConst0 cv.name value' eq.1,
           Expr.substConst0 cv.name value' eq.2))) ∧
    (natDivModNames.contains cv.name = true →
      DivModPinRun μ F env env₂ cv.name value')

/-- `DeclThmR`'s run/guard half. -/
def DeclThmRun (μ : CheckMode) (F : Nat) (env : Env)
    (cv : ConstantVal) (value : Expr) (env₂ : Env) : Prop :=
  ∃ type' value',
    ConstantValRun μ F env cv type' ∧
    (∃ stype u, inferTypeCore μ env F 0 type' = .ok stype ∧
      ensureSortCore μ env F 0 stype = .ok u ∧
      Level.isEquiv u .zero = some true) ∧
    ValueFrontRun μ F env cv value type' value' ∧
    -- stored by statement: the constant carries the record's own
    -- (raw) value, which nothing reads
    env₂ = ⟨.thmInfo ⟨cv.name, cv.levelParams, type'⟩ value ::
      env.consts⟩

/-- `DeclOpaqueR`'s run/guard half. -/
def DeclOpaqueRun (μ : CheckMode) (F : Nat) (env : Env)
    (cv : ConstantVal) (value : Expr) (env₂ : Env) : Prop :=
  ∃ type' value',
    ConstantValRun μ F env cv type' ∧
    ValueFrontRun μ F env cv value type' value' ∧
    env₂ = ⟨.axiomInfo ⟨cv.name, cv.levelParams, type'⟩ :: env.consts⟩ ∧
    (reduceOpNames.contains cv.name = true →
      ReducePinRun μ F env env₂ cv.name value)

/-- `DeclAxiomR`'s run/guard half: the branch disjunction is pure
stored-data guards and is carried verbatim. -/
def DeclAxiomRun (μ : CheckMode) (F : Nat) (env : Env)
    (cv : ConstantVal) (env₂ : Env) : Prop :=
  -- **`Quot.sound`** (task #293): the pinned quotient block's own
  -- record, compared with the pin BEFORE the common checks (its name is
  -- a reserved basis name) and installing nothing of its own — the
  -- block installs it.  No `ConstantValRun`: the record's type is not
  -- annotated, exactly as the parser's comparison did not annotate it.
  (cv.name = quotSoundName ∧ env₂ = env) ∨
  ∃ type',
    ConstantValRun μ F env cv type' ∧
    (let cvA : ConstantVal := ⟨cv.name, cv.levelParams, type'⟩
     (stdAxiomOk env cvA = true ∧
        env₂ = ⟨.axiomInfo cvA :: env.consts⟩) ∨
     (cvA.name = trustCompilerName ∧ trustCompilerOk env cvA = true ∧
        env₂ = ⟨.axiomInfo cvA :: env.consts⟩) ∨
     ((cvA.name = ofReduceNatName ∨ cvA.name = ofReduceBoolName) ∧
        ofReduceAxOk env cvA = true ∧
        env₂ = ⟨.axiomInfo cvA :: env.consts⟩) ∨
     (stdAxiomOk env cvA = false ∧
        cvA.name ≠ trustCompilerName ∧
        cvA.name ≠ ofReduceNatName ∧ cvA.name ≠ ofReduceBoolName ∧
        cvA.name ≠ propextName ∧ cvA.name ≠ choiceName ∧
        cvA.name = sorryAxName ∧
        env₂ = env))

/-! ## The assembly -/

/-- **The per-declaration run relation**: `DeclR`'s kind dispatch with
every derivation conjunct deleted, and the inductive kind's payload
taken as a parameter (see the module docstring — S5's unit replaces the
instantiation, not this text).

`DeclBasisRun` is re-used verbatim: that kind's record was already guards
only. -/
def DeclRun (μ : CheckMode) (F : Nat)
    (Ind : List ConstantInfo → Nat → Env → Prop) (env : Env) :
    Declaration → Env → Prop
  | .defnDecl cv value hint, env₂ => DeclDefnRun μ F env cv value hint env₂
  | .thmDecl cv value, env₂ => DeclThmRun μ F env cv value env₂
  | .opaqueDecl cv value, env₂ => DeclOpaqueRun μ F env cv value env₂
  | .axiomDecl cv, env₂ => DeclAxiomRun μ F env cv env₂
  | .basisDecl kind, env₂ => DeclBasisRun env kind env₂
  -- **The pinned blocks are recognised in the FOLD** (task #293): a
  -- stream block that IS one of the five pins installs the pin, and the
  -- quotient package's `type` record installs the sixth (its other
  -- records are members of the block that one installs).
  | .indDecl block nP, env₂ =>
    match basisPinHit block with
    | some kind => DeclBasisRun env kind env₂
    | none => Ind block nP env₂
  | .quotDecl k _, env₂ =>
    match k with
    | .type => DeclBasisRun env .quotK env₂
    | _ => env₂ = env

/-! ## The projections, retired (2026-09-05)

`ConstantValR.toRun`, `ValueFrontR.toRun`, `DivModPinR.toRun`,
`ReducePinR.toRun`, the four per-kind `toRun`s and `DeclR.toRun` sat
here under the note *"one source of truth: the R lane keeps proving
`DeclR`, and these discard the derivation halves."*  There is no R lane
and no `DeclR`: the SetR removal's Stage C deleted the relation family
and every derivation record over it, so the projections have nothing
left to project FROM.  The run records below them are now the only
source of truth, which is what S11a was aiming at — the projections
were the compatibility shim across the transition. -/

end ConLeche.Semantics
