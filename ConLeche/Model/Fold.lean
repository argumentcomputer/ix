module

public import ConLeche.Model.AxiomReduce
import ConLeche.Model.DeclInd
import ConLeche.Model.Inductives.DeclStruct
import ConLeche.Semantics.IndBlockFacts
public import ConLeche.Semantics.Bridge.Sound
import ConLeche.Semantics.Inductives.DeclSumEta
import ConLeche.Model.Inductives.DeclSum
public import ConLeche.Model.Inductives.DeclNative
import ConLeche.Model.BasisFalse
public section

/-!
# The P declaration fold, and the conditional capstone (task #161, P4)

`foldPM` carries `EnvModelOk` — the P invariant plus the η-family
closure — through an accepted stream, and
`no_proof_of_Empty_pure` is the campaign's **close**, at the frozen letter
(`CapstoneP.lean`'s docstring): input-level hypotheses only.  The
milestone-shaped `no_proof_of_Empty_pure_of` is kept beside it, now
carrying no bundle at all — every tier step is discharged.

The η half of the fold invariant is `declEtaStepRun`
(`SetBase/DeclEta.lean`, task #161 S3) and is now **model-free at every
kind**: S3 left `indDecl` premised on `declIndS memberKeyS mp.base` —
the one kind whose η-closure was proved interleaved with the `EnvS`
member/recursor folds — and S5's ind unit (`declIndEtaClosed`,
`SetBase/IndBlockR.lean`) proves it from `DeclIndRun` alone.  No install
obligation is consulted for the η half; the harvests keep their own
uses of `divModPinS` and `reducePinS`, which are value-kind
obligations, not fold ones.  The v1 base at every prefix is
`EnvModelM.base`, the S3 residue.

The routed bundles, by tier:

* (`LitStabilityP` is GONE: the guard equality it asserted is
  refutable at a support-completing install, and the monotone
  crossing + `natLitSupported_cons_back` made the harvests
  premise-free on the literal guards — the census shrank here);
* nothing.  `AxiomStepPB` (ENDGAME D, `axiomStepPB_of`),
  `BasisStepPB` (ENDGAME H, `basisStepPB_of`) and `IndStepPB`
  (IND TIER part 10, `indStepPB_of`) are all discharged; the census
  is `hμ` alone.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics ConLeche.SetModel
open ConLeche (CheckMode Env Expr Name Level ConstantInfo ConstantVal
  Declaration checkDecl checkDeclsPure fueledOps)

universe w

variable {V : Type w} [SetTheory V]
variable {μ : CheckMode}
variable {pins : List ConLeche.NatOpPinSet}

/-- The axiom kind's whole step — **no longer routed** (ENDGAME D):
`axiomStepPB_of` below discharges it.  The definition is kept because
the pin tier's four branches are stated against it and the census is
read off these signatures. -/
def AxiomStepPB (V : Type w) [SetTheory V] (μ : CheckMode) : Prop :=
  -- task #161 S4: the relation premise is now the run projection
  -- (`DeclAxiomRun`), which names no valuation — so the carrier `_mp`
  -- no longer appears in the premise's *type*.  It stays as the
  -- invariant the four branches consume.
  ∀ {F : Nat} {env : Env} (_mp : EnvModelM V μ env)
    {cv : ConstantVal} {env₂ : Env},
    DeclAxiomRun μ F env cv env₂ →
    Nonempty (EnvModelM V μ env₂)

/-- **`AxiomStepPB`, discharged — THE PIN BUNDLE IS CLOSED.**  All four
`DeclAxiomR` branches: the two standard axioms (`axiomStd`, ENDGAME
C), `Lean.trustCompiler` (`axiomTrustCompiler`, ENDGAME A part 2),
`ofReduceNat`/`ofReduceBool` (`axiomOfReduce`, ENDGAME D, on the new
`ReduceOps` field), and the tolerated skip (`axiomSkip`, which stores
nothing). -/
theorem axiomStepPB_of (hμ : μ.verifiedChecks = true) : AxiomStepPB V μ := by
  intro _F _env mp _cv _env₂ hR
  -- the `Quot.sound` arm (task #293) installs nothing
  rcases hR with ⟨-, rfl⟩ | hR
  · exact ⟨mp⟩
  obtain ⟨type', hcv, hbranch⟩ := hR
  rcases hbranch with ⟨hok, rfl⟩ | ⟨hname, hok, rfl⟩ |
    ⟨hor, hok, rfl⟩ | ⟨-, -, -, -, -, -, -, rfl⟩
  · exact axiomStd hμ mp hcv hok
  · exact axiomTrustCompiler hμ mp hcv hname hok
  · exact axiomOfReduce hμ mp hcv hor hok
  · exact axiomSkip mp

/-- The basis kind's whole step, routed (basis tier). -/
def BasisStepPB (V : Type w) [SetTheory V] (μ : CheckMode) : Prop :=
  ∀ {env : Env}, EnvModelM V μ env →
    ∀ {kind : ConLeche.BasisKind} {env₂ : Env},
      DeclBasisRun env kind env₂ →
      Nonempty (EnvModelM V μ env₂)

/-- **`BasisStepPB`, discharged** (task #161, ENDGAME H; the `False` block
at task #181): all pinned basis blocks install at the P tier.  Exactly `declBasisS`'s
dispatch shape, and — as there — `quotK` is the one branch whose
`DeclBasisRun` guard is not vacuous: it needs `Eq` in the prefix, which
is what the block's `Eq` bridge consumes. -/
theorem basisStepPB_of : BasisStepPB V μ := by
  intro env mp kind env₂ h
  obtain ⟨hEq, hchain⟩ := h
  cases kind with
  | eqK => exact declBasisPB_eqK mp hchain
  | natK => exact declBasisPB_natK mp hchain
  | punitK => exact declBasisPB_punitK mp hchain
  | emptyK => exact declBasisPB_emptyK mp hchain
  | falseK => exact declBasisPB_falseK mp hchain
  | quotK => exact declBasisPB_quotK mp (hEq rfl) hchain

/-- The inductive kind's whole step — **no longer routed** (task #161,
IND TIER part 10): `indStepPB_of` below discharges it.  The definition
is kept because the census is read off these signatures.

The `EtaFamiliesClosed` premise is part of the bundle's *shape*, not a
residue: `declStep_preserves` carries it as the v1 fold's second half and hands
it over at the call site, and the inductive install genuinely consumes
it (`EtaFamiliesClosedO` at the block, the member fold's η side
condition).  It is an environment fact the fold already owns, never a
hypothesis of the capstone. -/
def IndStepPB (V : Type w) [SetTheory V] (μ : CheckMode) : Prop :=
  -- the input carrier is the bundle's *subject*, not a datum the
  -- premise mentions: since S11b the ind premise is the **run**
  -- record, which names no valuation, so `_mp` appears only in the
  -- conclusion's shape ("a carrier here gives a carrier there").
  ∀ {F : Nat} {env : Env} (_mp : EnvModelM V μ env)
    {block : List ConstantInfo} {env₂ : Env},
    ConLeche.EtaFamiliesClosed env →
    DeclIndRun μ F env block env₂ →
    Nonempty (EnvModelM V μ env₂)

/-- **`IndStepPB`, discharged — THE INDUCTIVE TIER IS CLOSED**
(`declInd`, `Interp/DeclIndP.lean`): the member fold, the recursor
group (provision/fire/swap) and the projection functions, all three at
the reading. -/
theorem indStepPB_of (hμ : μ.verifiedChecks = true) : IndStepPB V μ := by
  intro _F _env mp _block _env₂ hE h
  exact declInd hμ mp hE h

/-- **The P fold invariant**: the P environment invariant plus the
η-family closure (the v1 fold's second half, reused verbatim). -/
@[expose] def EnvModelOk (V : Type w) [SetTheory V] (μ : CheckMode) (env : Env) :
    Prop :=
  Nonempty (EnvModelM V μ env) ∧ EtaFamiliesClosed env

/-- **The per-declaration P step, by dispatch.**

**Task #161 S11a — the premise is the RUN record, not `DeclR`.**  Since
S4 this theorem took `DeclR` and projected (`DeclR.toRun`) on its first
line, which made every P step's *statement* valuation-free while its
*proof path* still ran through the derivation bridge: the S10 seal's
residual B ("a projection composed with a bridge is not a projection").
The projection is now done by the *producer* instead — the five
non-`ind` kinds have run-only bridges (`checkDeclRun_of`,
`SetBase/Bridge/DeclRun.lean`) and the `ind` kind arrives through
`DeclRun`'s `Ind` parameter — so this step consumes exactly what it
reads, and no step below changed a line. -/
theorem declStep_preserves (hμ : μ.verifiedChecks = true) {F : Nat} {env env₂ : Env} {d : Declaration}
    (mp : EnvModelM V μ env) (hE : EtaFamiliesClosed env)
    (hrun : DeclRun μ F (ConLeche.Semantics.DeclIndRunDispatch μ F env)
      env d env₂) :
    EnvModelOk V μ env₂ := by
  -- the η half: `declEtaStepRun` (task #161 S3, the census's C4), now
  -- MODEL-FREE at every kind.  S3's stop-and-name left `indDecl`'s
  -- η-closure premised on `declIndS memberKeyS mp.base`; S5's ind unit
  -- (`SetBase/IndBlockR.lean`) proves it from `DeclIndRun` alone, so the
  -- fold consults no install obligation for its η half at all.
  -- task #175 wiring W5: the η half is FLAG-AGNOSTIC — the `.indDecl`
  -- dispatch's own case split (`declIndRunDispatchEtaClosed`)
  refine ⟨?_, ConLeche.Semantics.declEtaStepRun
    (fun h' => ConLeche.Semantics.declIndRunDispatchEtaClosed hE h') hE hrun⟩
  cases d with
  | defnDecl cv value hint =>
    have hsh := hrun
    obtain ⟨type', value', hcv, -, henv2, -, -⟩ := hsh
    subst henv2
    exact harvestDefn hμ mp hrun
  | thmDecl cv value =>
    have hsh := hrun
    -- one dash fewer than the `DeclR` pattern: the run record has no
    -- is-a-proposition derivation row (task #161 S11a)
    obtain ⟨type', value', hcv, -, -, henv2⟩ := hsh
    subst henv2
    exact harvestThm hμ mp hrun
  | opaqueDecl cv value =>
    have hsh := hrun
    obtain ⟨type', value', hcv, -, henv2, -⟩ := hsh
    subst henv2
    exact harvestOpaque hμ mp hrun
  | axiomDecl cv => exact axiomStepPB_of hμ mp hrun
  | basisDecl kind => exact basisStepPB_of mp hrun
  | quotDecl k cv =>
    -- task #293: the quotient package's `type` record installs the
    -- pinned block; its other records install nothing
    cases k with
    | type => exact basisStepPB_of mp hrun
    | _ => exact (show env₂ = env from hrun) ▸ ⟨mp⟩
  | indDecl block nP =>
    -- task #293: a block the fold recognises as one of the five pinned
    -- ones installs the PIN; everything else takes the `.indDecl`
    -- dispatch — a RECOGNISED block directly (ONE ROUTE, task #210),
    -- the rest through the modeled path, the kernel's own two-way case
    -- split (task #219)
    simp only [ConLeche.Semantics.DeclRun] at hrun
    split at hrun
    · exact basisStepPB_of mp hrun
    · have hrun' : ConLeche.Semantics.DeclIndRunDispatch μ F env block nP env₂ := hrun
      unfold ConLeche.Semantics.DeclIndRunDispatch at hrun'
      cases hdf : ConLeche.nativeParts? nP block with
      | some p =>
        rw [hdf] at hrun'
        exact declNative hμ mp hE hdf hrun'
      | none =>
        rw [hdf] at hrun'
        exact indStepPB_of hμ mp hE hrun'

/-- **The P fold**: `foldlM_R`'s recursion at the P invariant. -/
theorem foldPM (hμ : μ.verifiedChecks = true) {F : Nat} :
    ∀ (ds : List Declaration) (env : Env) {env' : Env},
      EnvModelOk V μ env →
      ds.foldlM (checkDecl μ (fueledOps μ F) pins) env = .ok env' →
      EnvModelOk V μ env'
  | [], _, _, hm, h => by
    simp only [List.foldlM, pure, Except.pure, Except.ok.injEq] at h
    exact h ▸ hm
  | d :: ds, env, _, hm, h => by
    simp only [List.foldlM, Bind.bind, Except.bind] at h
    cases hd : checkDecl μ (fueledOps μ F) pins env d with
    | error e => rw [hd] at h; exact nomatch h
    | ok env1 =>
      rw [hd] at h
      obtain ⟨⟨mp⟩, hE⟩ := hm
      exact foldPM hμ ds env1
        (declStep_preserves hμ mp hE
          -- **the RUN bridge, from the P carrier's own `EnvFacts`**
          -- (task #161 S11a).  S7 (Wall C step (e)) made the bridge
          -- model-free, so the fold's last v1 round trip became the
          -- projection `EnvModelM.toEnvFacts`; S11a makes it
          -- *derivation*-free at the five non-`ind` kinds, so the only
          -- route from here into the relation tier is the `Ind`
          -- premise `checkDeclRun_ofEnvFactsE` fills with `declIndRR`.
          (ConLeche.Semantics.checkDeclRun_ofEnvFactsE hd)) h

/-- **The acceptance theorem, P route — milestone shape** (conditional
on the tier bundles; the final form replaces them with the tiers'
theorems). -/
theorem checkDeclsPure_sound_of (hμ : μ.verifiedChecks = true) {F : Nat}
    {ds : List Declaration} {env' : Env}
    (h : checkDeclsPure μ (fueledOps μ F) pins ds = .ok env') :
    Nonempty (EnvModelM V μ env') :=
  (foldPM hμ ds Env.empty
    ⟨⟨EnvModelM.empty V μ⟩, EtaFamiliesClosed.empty⟩ h).1

/-- **The capstone, milestone shape**: no proof of `Empty` is ever
accepted — the collapse-free model of the validated annotations, at
the frozen final statement's hypotheses plus the named tier
bundles. -/
theorem no_proof_of_Empty_pure_of (V : Type w) [SetTheory V]
    {μ : CheckMode} (hμ : μ.verifiedChecks = true) {F : Nat}
    {ds : List Declaration} {env' : Env}
    (h : checkDeclsPure μ (fueledOps μ F) pins ds = .ok env')
    (c : ConstantInfo) (hc : c ∈ env'.consts)
    (hty : c.toConstantVal.type = .const emptyName []) : False := by
  obtain ⟨mp⟩ := checkDeclsPure_sound_of (V := V) hμ h
  exact no_constant_of_Empty mp c hc hty

/-- **THE CAPSTONE, at the frozen letter** (`CapstoneP.lean`'s
docstring, checked against the goal's own words): *the checker,
running in a validating mode, never accepts a declaration stream in
which some stored constant has type `Empty`.*

Hypotheses are **input-level only** — the accepted run, the stored
constant, its type, plus the validating mode, which is part of the
goal's letter (the annotated checker *is* the verified mode;
`--trusted` ignores annotations by design).  No residue: every tier
step is discharged (`axiomStepPB_of`, `basisStepPB_of`,
`indStepPB_of`), so the conditional milestone form
`no_proof_of_Empty_pure_of` above now carries nothing either.  The #16
hypothesis-minimal precedent, met.

`SetTheory V` is the standing parametricity of the consistency
argument (project rule: consistency proofs stay parametric in the
`SetTheory` interface), not a hypothesis about the input. -/
theorem no_proof_of_Empty_pure (V : Type w) [SetTheory V]
    {μ : CheckMode} (hμ : μ.verifiedChecks = true) {F : Nat}
    {ds : List Declaration} {env' : Env}
    (h : checkDeclsPure μ (fueledOps μ F) pins ds = .ok env') :
    ∀ c ∈ env'.consts,
      c.toConstantVal.type = .const emptyName [] → False :=
  fun c hc hty => no_proof_of_Empty_pure_of V hμ h c hc hty

/-- **THE CAPSTONE ABOUT `False`** (task #181): *the checker, running
in a validating mode, never accepts a declaration stream in which some
stored constant has type `False`.*  The same letter as
`no_proof_of_Empty_pure`, at the pinned `False` block
(`ConLeche/Kernel/Basis/False.lean`): `False` is a reserved basis name
whose stored declaration and leaf are fixed by the pin, so — exactly as
for `Empty` — the statement carries no hypothesis about how the stream
declared `False`.  Hypotheses are input-level only: the validating
mode, the accepted run, the stored constant, its type. -/
theorem no_proof_of_False_pure (V : Type w) [SetTheory V]
    {μ : CheckMode} (hμ : μ.verifiedChecks = true) {F : Nat}
    {ds : List Declaration} {env' : Env}
    (h : checkDeclsPure μ (fueledOps μ F) pins ds = .ok env') :
    ∀ c ∈ env'.consts,
      c.toConstantVal.type = .const falseName [] → False := by
  obtain ⟨mp⟩ := checkDeclsPure_sound_of (V := V) hμ h
  exact fun c hc hty => no_constant_of_False mp c hc hty

end ConLeche.Model
