module

public import ConLeche.Semantics.DeclRun
import ConLeche.Semantics.Bridge.Decl
import ConLeche.Verify.ReducePinInv
import ConLeche.Verify.DivModInv

@[expose] public section

/-!
# The **run-only** declaration bridges (task #161 S11a, THE SEPARATION)

`Bridge/Decl.lean` bridges `checkDecl`'s six branches into `DeclR`,
whose per-kind records carry *two* kinds of conjunct: guards/runs and
derivations (the trailing `∀ φ, ∃ …, denote … ∧ Infer … ∧ DefEq …`).
Every one of those bridges therefore **welds** two independent proofs:

* a checker inversion — `checkConstantVal_inv`, `checkReducePin_inv`,
  `checkDivModPin_inv` and the branch's own control-flow inversion,
  all relation-free;
* a derivation construction — `checkBridge`, which is where
  `Red.beta`/`Infer.app`/`DefEq.trans` enter the proof term.

The S10 seal measured the consequence (`DeclR.toRun` is clean,
`checkDeclRun_sound = toRun ∘ checkDeclR_sound` is **not**): projecting
*after* the weld keeps the relation tier on the proof path, so the P
lane's own fold inherited `Red.beta` through a record it never reads.

This module **cuts the weld at the five non-`ind` kinds**: each bridge
below is the same inversion feeding `SetBase/DeclRun.lean`'s run record
directly, with no derivation on the path.  The records are re-used, not
duplicated — `DeclRun`'s payload is zero (task #161 S10 ruling 1: the
family is valuation-free outright, since `acceptedReads_of` supplies
every reading the P lane wants from the runs).

**What is *not* here**: the `ind` kind.  It stays `DeclRun`'s `Ind`
parameter — the slot S4 built for exactly this staging — and is
supplied at the call site (today by `declIndRR`, the relation-carrying
bridge; S11b replaces it with the ind run bridge).  So `checkDeclRun_of`
below is relation-free *outright*, and the only door left into the
derivation tier is the `Ind` premise.

**The `basisDecl` kind is `declBasisRun` verbatim** (`Bridge/Decl.lean`):
that kind's record was already guards-only, `DeclRun` re-uses
`DeclBasisRun` as-is (the S4 table's "re-used verbatim" row), and its
bridge builds no derivation.  Importing `Bridge/Decl.lean` for it (and
for `natEqsRun_of_certs`, likewise already run-only) costs the *proof
term* nothing — the separation's criterion is the proof-term closure,
not the import graph, which is S9's own finding.
-/

namespace ConLeche.Semantics

open ConLeche.Term ConLeche.Verify

variable {pins : List NatOpPinSet}

/-! ## The shared front doors, run half -/

/-- **`checkConstantVal`, inverted into the run record.**  The
relation-free half of `constantValR_of`: the same inversion, the same
two closedness facts beside it, and `ConstantValRun` instead of
`ConstantValR`.  No `EnvFacts`, no valuation, no `checkBridge`. -/
theorem constantValRun_of {env : Env} {μ : CheckMode} {F : Nat}
    {cv cv' : ConstantVal}
    (h : checkConstantVal (fueledOps μ F) env cv = .ok cv') :
    ∃ type', cv' = { cv with type := type' } ∧
      type'.hasFvar = false ∧ type'.looseBVarsBounded 0 = true ∧
      ConstantValRun μ F env cv type' := by
  obtain ⟨hfind, hres, hpsh, hnd, hlbt, hitf, type, stype, u, hann, htp,
    htr, hst, hsort, rfl⟩ := checkConstantVal_inv h
  obtain ⟨htf, hbt'⟩ := annotate_syntax hann hitf hlbt
  exact ⟨type, rfl, htf, hbt',
    Option.isNone_iff_eq_none.mpr hfind, hres, hpsh, hnd, hlbt, hitf,
    hann, htp, htr, ⟨stype, u, hst, hsort⟩⟩

/-- **The value front door, run half.**  `valueFrontR_of`'s premises
*are* `ValueFrontRun`'s conjuncts — the run record was read off this
very destructuring (task #161 P4 H1) — so the run bridge is the
packing, and the `m`/`checkBridge` half of `valueFrontR_of` is what
does not happen here. -/
theorem valueFrontRun_of {env : Env} {μ : CheckMode} {F : Nat}
    {cv : ConstantVal} {value type' value' vtype : Expr}
    (hlbv : value.looseBVarsBounded 0 = true)
    (hivf : value.hasFvar = false)
    (hannv : annotateCore μ env F 0 value = .ok value')
    (hvp : value'.allLevelParamsDefined cv.levelParams = true)
    (hvr : value'.constsResolve env = true)
    (hvt : inferTypeCore μ env F 0 value' = .ok vtype)
    (hde : isDefEqCore μ env F 0 vtype type' = .ok true) :
    ValueFrontRun μ F env cv value type' value' :=
  ⟨hlbv, hivf, hannv, hvp, hvr, ⟨vtype, hvt, hde⟩⟩

/-! ## The conditional pin packs, run half -/

/-- **`checkReducePin`, run half.**  `checkReducePin_inv`'s output
re-associated: `ReducePinRun` is exactly the inversion minus the
elaborator-drift verdict (`hp1`, which no record ever carried) and
minus the identity's `DefEq` transport (`reducePinR_of`'s whole
`fun φ` block). -/
theorem reducePinRun_of {env env' : Env} {μ : CheckMode} {F : Nat}
    {c : Name} {value : Expr}
    (h : checkReducePin (m := CheckM) (fueledOps μ F) env env' c value
      = .ok ()) :
    ReducePinRun μ F env env' c value := by
  obtain ⟨hstored, helem, hpg, valA, pinA, hva, hpa, -, hp2⟩ :=
    checkReducePin_inv h
  exact ⟨hstored, helem, hpg, valA, pinA, hva, hpa, hp2⟩

/-- **`checkDivModPin`, run half.**  `DivModPinR` was already
valuation-free (its `_cval` is a dead parameter), so this is
`divModPinR_of`'s script with the `EnvFacts` dropped — the one kind where
"the projection is the identity" was true all along. -/
theorem divModPinRun_of {env env' : Env} {μ : CheckMode} {F : Nat}
    {c : Name} {cv0 : ConstantVal} {v : Expr} {hint0 : ReducibilityHint}
    (hstore : env'.find? c = some (.defnInfo cv0 v hint0))
    (h : checkDivModPin (m := CheckM) (fueledOps μ F) pins env env' c
      = .ok ()) :
    DivModPinRun μ F env env' c v := by
  obtain ⟨henv, cv', value', hint', hfind, ps, -, hguards,
    ⟨pinA, hpa, -⟩, hcerts⟩ := checkDivModPin_inv h
  obtain rfl : value' = v := by
    rw [hstore] at hfind
    exact (ConstantInfo.defnInfo.inj (Option.some.inj hfind)).2.1.symm
  obtain ⟨hpin, hcertsG⟩ := by
    simpa only [Bool.and_eq_true] using hguards
  exact ⟨henv, ps, hpin, hcertsG, pinA, hpa, hcerts⟩

/-! ## The four value/axiom kinds, run half

Each is its branch's control-flow inversion — `declThmR`'s,
`declOpaqueR`'s, `declDefnR`'s and `declAxiomR`'s scripts up to the
point where those build a derivation.  The S10 bill priced them as
"the `refine` line before each `fun φ => ?_`", and that is what they
are: the same case analysis, stopping at the run record. -/

/-- **`thmDecl`, run half.** -/
theorem declThmRun_of {env env₂ : Env} {μ : CheckMode} {F : Nat}
    {cv : ConstantVal} {value : Expr}
    (h : checkDecl μ (fueledOps μ F) pins env (.thmDecl cv value)
      = .ok env₂) :
    DeclThmRun μ F env cv value env₂ := by
  simp only [checkDecl, checkThmVal, fueledOps_annotate,
    fueledOps_inferType, fueledOps_isDefEq, fueledOps_ensureSort,
    Bind.bind, Except.bind] at h
  cases hccv : checkConstantVal (fueledOps μ F) env cv with
  | error e => rw [hccv] at h; exact nomatch h
  | ok cv' =>
  rw [hccv] at h
  try dsimp only at h
  obtain ⟨type, rfl, -, -, hcv⟩ := constantValRun_of hccv
  simp only [Pure.pure, Except.pure] at h
  cases hst2 : inferTypeCore μ env F 0 type with
  | error e => rw [hst2] at h; exact nomatch h
  | ok stype2 =>
  rw [hst2] at h
  try dsimp only at h
  cases hsort2 : ensureSortCore μ env F 0 stype2 with
  | error e => rw [hsort2] at h; exact nomatch h
  | ok u2 =>
  rw [hsort2] at h
  try dsimp only at h
  cases hpz : Level.isEquiv u2 Level.zero with
  | none => rw [hpz] at h; simp [liftFueled] at h
  | some bz =>
  rw [hpz] at h
  cases bz with
  | false => simp [liftFueled, pure, Except.pure] at h
  | true =>
  simp only [liftFueled, pure, Except.pure] at h
  try dsimp only at h
  by_cases hlbv : value.looseBVarsBounded 0 = true
  case neg => simp [hlbv] at h
  simp only [hlbv] at h
  by_cases hivf : value.hasFvar = true
  case pos => simp [hivf] at h
  simp only [hivf] at h
  have hivf' : value.hasFvar = false := by
    revert hivf; cases value.hasFvar <;> simp
  cases hannv : annotateCore μ env F 0 value with
  | error e => rw [hannv] at h; exact nomatch h
  | ok value' =>
  rw [hannv] at h
  try dsimp only at h
  by_cases hvp : value'.allLevelParamsDefined cv.levelParams = true
  case neg => simp [hvp] at h
  simp only [hvp] at h
  by_cases hvr : value'.constsResolve env = true
  case neg => simp [hvr] at h
  simp only [hvr] at h
  cases hvt : inferTypeCore μ env F 0 value' with
  | error e => rw [hvt] at h; exact nomatch h
  | ok vtype =>
  rw [hvt] at h
  try dsimp only at h
  cases hde : isDefEqCore μ env F 0 vtype type with
  | error e => rw [hde] at h; exact nomatch h
  | ok b =>
  rw [hde] at h
  cases b with
  | false => exact nomatch h
  | true =>
  simp only [Bool.false_eq_true, ↓reduceIte, Except.ok.injEq] at h
  exact ⟨type, value', hcv, ⟨stype2, u2, hst2, hsort2, hpz⟩,
    valueFrontRun_of hlbv hivf' hannv hvp hvr hvt hde, h.symm⟩

/-- **`axiomDecl`, run half.**  Nothing but stored-data guards happens
past the front door here, so this is `declAxiomR`'s script with its one
`constantValR_of` call swapped for the run inversion. -/
theorem declAxiomRun_of {env env₂ : Env} {μ : CheckMode} {F : Nat}
    {cv : ConstantVal}
    (h : checkDecl μ (fueledOps μ F) pins env (.axiomDecl cv) = .ok env₂) :
    DeclAxiomRun μ F env cv env₂ := by
  simp only [checkDecl, Bind.bind, Except.bind] at h
  -- **`Quot.sound`** (task #293): compared with the pin before the
  -- common checks, installing nothing.
  by_cases hqs : cv.name = quotSoundName
  · rw [if_pos hqs] at h
    by_cases hpin : ConstantInfo.canonEq (.axiomInfo cv)
        (quotBasis.getD 4 (.axiomInfo default)) = true
    · rw [if_pos hpin] at h
      simp only [pure, Except.pure, Except.ok.injEq] at h
      exact Or.inl ⟨hqs, h.symm⟩
    · rw [if_neg hpin] at h; exact nomatch h
  rw [if_neg hqs] at h
  refine Or.inr ?_
  cases hccv : checkConstantVal (fueledOps μ F) env cv with
  | error e => rw [hccv] at h; exact nomatch h
  | ok cvA =>
  rw [hccv] at h
  try dsimp only at h
  obtain ⟨type, rfl, -, -, hcv⟩ := constantValRun_of hccv
  refine ⟨type, hcv, ?_⟩
  by_cases hstd : stdAxiomOk env { cv with type := type } = true
  · rw [if_pos hstd] at h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    exact Or.inl ⟨hstd, h.symm⟩
  rw [if_neg hstd] at h
  have hstdF : stdAxiomOk env { cv with type := type } = false := by
    revert hstd; cases stdAxiomOk env { cv with type := type } <;> simp
  by_cases htc : cv.name = trustCompilerName
  · rw [if_pos htc] at h
    by_cases htco : trustCompilerOk env { cv with type := type } = true
    · rw [if_pos htco] at h
      simp only [pure, Except.pure, Except.ok.injEq] at h
      exact Or.inr (Or.inl ⟨htc, htco, h.symm⟩)
    · rw [if_neg htco] at h
      simp [throw, throwThe, MonadExceptOf.throw] at h
  rw [if_neg htc] at h
  by_cases hofr : cv.name = ofReduceNatName ∨ cv.name = ofReduceBoolName
  · rw [if_pos hofr] at h
    by_cases hofro : ofReduceAxOk env { cv with type := type } = true
    · rw [if_pos hofro] at h
      simp only [pure, Except.pure, Except.ok.injEq] at h
      exact Or.inr (Or.inr (Or.inl ⟨hofr, hofro, h.symm⟩))
    · rw [if_neg hofro] at h
      simp [throw, throwThe, MonadExceptOf.throw] at h
  rw [if_neg hofr] at h
  by_cases hpc : cv.name = propextName ∨ cv.name = choiceName
  · rw [if_pos hpc] at h
    simp [throw, throwThe, MonadExceptOf.throw] at h
  rw [if_neg hpc] at h
  by_cases htol : cv.name = sorryAxName
  · rw [if_pos htol] at h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    refine Or.inr (Or.inr (Or.inr ⟨hstdF, htc, ?_, ?_, ?_, ?_, htol,
      h.symm⟩))
    · exact fun hh => hofr (Or.inl hh)
    · exact fun hh => hofr (Or.inr hh)
    · exact fun hh => hpc (Or.inl hh)
    · exact fun hh => hpc (Or.inr hh)
  · rw [if_neg htol] at h
    simp [throw, throwThe, MonadExceptOf.throw] at h

/-- **`opaqueDecl`, run half**, with the compiler-trust pin's run
inversion in place of the pin bridge. -/
theorem declOpaqueRun_of {env env₂ : Env} {μ : CheckMode} {F : Nat}
    {cv : ConstantVal} {value : Expr}
    (h : checkDecl μ (fueledOps μ F) pins env (.opaqueDecl cv value)
      = .ok env₂) :
    DeclOpaqueRun μ F env cv value env₂ := by
  simp only [checkDecl, checkOpaqueVal, fueledOps_annotate,
    fueledOps_inferType, fueledOps_isDefEq, Bind.bind, Except.bind] at h
  cases hccv : checkConstantVal (fueledOps μ F) env cv with
  | error e => rw [hccv] at h; exact nomatch h
  | ok cv' =>
  rw [hccv] at h
  try dsimp only at h
  obtain ⟨type, rfl, -, -, hcv⟩ := constantValRun_of hccv
  simp only [Pure.pure, Except.pure] at h
  by_cases hlbv : value.looseBVarsBounded 0 = true
  case neg => simp [hlbv] at h
  simp only [hlbv] at h
  by_cases hivf : value.hasFvar = true
  case pos => simp [hivf] at h
  simp only [hivf] at h
  have hivf' : value.hasFvar = false := by
    revert hivf; cases value.hasFvar <;> simp
  cases hannv : annotateCore μ env F 0 value with
  | error e => rw [hannv] at h; exact nomatch h
  | ok value' =>
  rw [hannv] at h
  try dsimp only at h
  by_cases hvp : value'.allLevelParamsDefined cv.levelParams = true
  case neg => simp [hvp] at h
  simp only [hvp] at h
  by_cases hvr : value'.constsResolve env = true
  case neg => simp [hvr] at h
  simp only [hvr] at h
  cases hvt : inferTypeCore μ env F 0 value' with
  | error e => rw [hvt] at h; exact nomatch h
  | ok vtype =>
  rw [hvt] at h
  try dsimp only at h
  cases hde : isDefEqCore μ env F 0 vtype type with
  | error e => rw [hde] at h; exact nomatch h
  | ok b =>
  rw [hde] at h
  cases b with
  | false => exact nomatch h
  | true =>
  simp only [Bool.false_eq_true, ↓reduceIte] at h
  refine ⟨type, value', hcv,
    valueFrontRun_of hlbv hivf' hannv hvp hvr hvt hde, ?_, ?_⟩
  · by_cases hro : reduceOpNames.contains cv.name = true
    · rw [if_pos hro] at h
      cases hrpin : checkReducePin (m := CheckM) (fueledOps μ F) env
          ⟨.axiomInfo { cv with type := type } :: env.consts⟩ cv.name
          value with
      | error e => rw [hrpin] at h; exact nomatch h
      | ok u =>
        rw [hrpin] at h
        simp only [Except.ok.injEq] at h
        exact h.symm
    · rw [if_neg hro] at h
      simp only [Except.ok.injEq] at h
      exact h.symm
  · intro hro
    rw [if_pos hro] at h
    cases hrpin : checkReducePin (m := CheckM) (fueledOps μ F) env
        ⟨.axiomInfo { cv with type := type } :: env.consts⟩ cv.name
        value with
    | error e => rw [hrpin] at h; exact nomatch h
    | ok u =>
      rw [hrpin] at h
      simp only [Except.ok.injEq] at h
      subst h
      exact reducePinRun_of hrpin

/-- **`defnDecl`, run half**, with the two structural-`Nat` pins' run
inversions (`natEqsRun_of_certs`, `divModPinRun_of`) in place of the
pin bridges.  The `key` block — the dispatch on the two pin guards — is
`declDefnR`'s verbatim: it is pure control flow and names nothing
semantic. -/
theorem declDefnRun_of {env env₂ : Env} {μ : CheckMode} {F : Nat}
    {cv : ConstantVal} {value : Expr} {hint : ReducibilityHint}
    (h : checkDecl μ (fueledOps μ F) pins env (.defnDecl cv value hint)
      = .ok env₂) :
    DeclDefnRun μ F env cv value hint env₂ := by
  simp only [checkDecl, checkDefnVal, fueledOps_annotate,
    fueledOps_inferType, fueledOps_isDefEq, Bind.bind, Except.bind] at h
  cases hccv : checkConstantVal (fueledOps μ F) env cv with
  | error e => rw [hccv] at h; exact nomatch h
  | ok cv' =>
  rw [hccv] at h
  try dsimp only at h
  obtain ⟨type, rfl, -, -, hcv⟩ := constantValRun_of hccv
  simp only [Pure.pure, Except.pure] at h
  by_cases hlbv : value.looseBVarsBounded 0 = true
  case neg => simp [hlbv] at h
  simp only [hlbv] at h
  by_cases hivf : value.hasFvar = true
  case pos => simp [hivf] at h
  simp only [hivf] at h
  have hivf' : value.hasFvar = false := by
    revert hivf; cases value.hasFvar <;> simp
  cases hannv : annotateCore μ env F 0 value with
  | error e => rw [hannv] at h; exact nomatch h
  | ok value' =>
  rw [hannv] at h
  try dsimp only at h
  by_cases hvp : value'.allLevelParamsDefined cv.levelParams = true
  case neg => simp [hvp] at h
  simp only [hvp] at h
  by_cases hvr : value'.constsResolve env = true
  case neg => simp [hvr] at h
  simp only [hvr] at h
  cases hvt : inferTypeCore μ env F 0 value' with
  | error e => rw [hvt] at h; exact nomatch h
  | ok vtype =>
  rw [hvt] at h
  try dsimp only at h
  cases hde : isDefEqCore μ env F 0 vtype type with
  | error e => rw [hde] at h; exact nomatch h
  | ok b =>
  rw [hde] at h
  cases b with
  | false => exact nomatch h
  | true =>
  simp only [Bool.false_eq_true, ↓reduceIte] at h
  -- the environment the two pin blocks run against, and its own lookup
  have hfind2 : (⟨ConstantInfo.defnInfo { cv with type := type } value'
        hint :: env.consts⟩ : Env).find? cv.name
      = some (.defnInfo { cv with type := type } value' hint) := by
    rw [Env.find?_cons]; exact if_pos rfl
  -- **the dispatch, once**: the stored environment and the two packs
  have key : env₂ = ⟨ConstantInfo.defnInfo { cv with type := type }
        value' hint :: env.consts⟩ ∧
      (natOpNames.contains cv.name = true →
        natOpGuard ⟨ConstantInfo.defnInfo { cv with type := type }
            value' hint :: env.consts⟩ cv.name = true ∧
        (natOpDeps cv.name).all (natOpStoredOk
          ⟨ConstantInfo.defnInfo { cv with type := type } value' hint ::
            env.consts⟩) = true ∧
        certifyNatEqs (m := CheckM) (fueledOps μ F) env
          ((natOpEquations 0 cv.name).map fun eq =>
            (Expr.substConst0 cv.name value' eq.1,
             Expr.substConst0 cv.name value' eq.2)) = .ok true) ∧
      (natDivModNames.contains cv.name = true →
        checkDivModPin (m := CheckM) (fueledOps μ F) pins env
          ⟨ConstantInfo.defnInfo { cv with type := type } value' hint ::
            env.consts⟩ cv.name = .ok ()) := by
    by_cases hno : natOpNames.contains cv.name = true
    · rw [if_pos hno] at h
      by_cases hg : (natOpGuard ⟨ConstantInfo.defnInfo
            { cv with type := type } value' hint :: env.consts⟩ cv.name
          && (natOpDeps cv.name).all (natOpStoredOk
            ⟨ConstantInfo.defnInfo { cv with type := type } value'
              hint :: env.consts⟩)) = true
      · rw [if_pos hg] at h
        rw [hfind2] at h
        dsimp only at h
        cases hcert : certifyNatEqs (m := CheckM) (fueledOps μ F) env
            ((natOpEquations 0 cv.name).map fun eq =>
              (Expr.substConst0 cv.name value' eq.1,
               Expr.substConst0 cv.name value' eq.2)) with
        | error e => rw [hcert] at h; exact nomatch h
        | ok v =>
        rw [hcert] at h
        cases v with
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte, throw, throwThe,
            MonadExceptOf.throw] at h
          exact nomatch h
        | true =>
        simp only [↓reduceIte] at h
        obtain ⟨hg1, hg2⟩ := Bool.and_eq_true _ _ |>.mp hg
        by_cases hdn : natDivModNames.contains cv.name = true
        · rw [if_pos hdn] at h
          cases hpin : checkDivModPin (m := CheckM) (fueledOps μ F) pins env
              ⟨ConstantInfo.defnInfo { cv with type := type } value'
                hint :: env.consts⟩ cv.name with
          | error e => rw [hpin] at h; exact nomatch h
          | ok u =>
            rw [hpin] at h
            simp only [Except.ok.injEq] at h
            subst h
            exact ⟨rfl, fun _ => ⟨hg1, hg2, rfl⟩, fun _ => rfl⟩
        · rw [if_neg hdn] at h
          simp only [Except.ok.injEq] at h
          subst h
          exact ⟨rfl, fun _ => ⟨hg1, hg2, rfl⟩, fun hc => absurd hc hdn⟩
      · rw [if_neg hg] at h
        simp only [throw, throwThe, MonadExceptOf.throw] at h
        exact nomatch h
    · rw [if_neg hno] at h
      by_cases hdn : natDivModNames.contains cv.name = true
      · rw [if_pos hdn] at h
        cases hpin : checkDivModPin (m := CheckM) (fueledOps μ F) pins env
            ⟨ConstantInfo.defnInfo { cv with type := type } value'
              hint :: env.consts⟩ cv.name with
        | error e => rw [hpin] at h; exact nomatch h
        | ok u =>
          rw [hpin] at h
          simp only [Except.ok.injEq] at h
          subst h
          exact ⟨rfl, fun hc => absurd hc hno, fun _ => rfl⟩
      · rw [if_neg hdn] at h
        simp only [Except.ok.injEq] at h
        subst h
        exact ⟨rfl, fun hc => absurd hc hno, fun hc => absurd hc hdn⟩
  obtain ⟨rfl, hnatK, hdmK⟩ := key
  exact ⟨type, value', hcv,
    valueFrontRun_of hlbv hivf' hannv hvp hvr hvt hde,
    rfl,
    fun hc => ⟨(hnatK hc).1, (hnatK hc).2.1,
      natEqsRun_of_certs _ (hnatK hc).2.2⟩,
    fun hc => divModPinRun_of
      (by rw [Env.find?_cons]; exact if_pos rfl) (hdmK hc)⟩

/-! ## The assembly -/

/-- **The run dispatch — task #161 S11a's deliverable.**

`checkDeclR_of`'s twin at `DeclRun`, with a decisive difference: five
of the six per-kind obligations are **discharged here**, not taken as
parameters, because their bridges need no carrier at all.  What is left
is the `Ind` premise — `DeclRun`'s own parameter slot, built at S4 for
exactly this staging.

**The separation property, stated**: this theorem's proof term reaches
no constructor of `Red`/`Infer`/`DefEq`.  Every route into the
derivation tier goes through `Ind`, so a caller that supplies a
relation-free `Ind` gets a relation-free run record, and a caller that
supplies `declIndRR` (today's, until S11b) has exactly **one** door.
`tests/proofdeps.sh` pins both readings. -/
theorem checkDeclRun_of {μ : CheckMode} {F : Nat}
    {Ind : List ConstantInfo → Nat → Env → Prop} {env env₂ : Env}
    (hind : ∀ {block : List ConstantInfo} {nP : Nat},
      basisPinHit block = none →
      checkDecl μ (fueledOps μ F) pins env (.indDecl block nP) = .ok env₂ →
      Ind block nP env₂)
    {d : Declaration}
    (h : checkDecl μ (fueledOps μ F) pins env d = .ok env₂) :
    DeclRun μ F Ind env d env₂ := by
  cases d with
  | defnDecl cv value hint => exact declDefnRun_of h
  | thmDecl cv value => exact declThmRun_of h
  | opaqueDecl cv value => exact declOpaqueRun_of h
  | axiomDecl cv => exact declAxiomRun_of h
  | basisDecl kind => exact declBasisRun h
  | quotDecl k cv =>
    -- task #293: the `type` record installs the pinned block, the other
    -- members install nothing
    simp only [checkDecl] at h
    cases k <;> simp only [DeclRun] <;> split at h
    case type.isTrue => exact declBasisRunOf h
    case type.isFalse => exact nomatch h
    all_goals first
      | (simp only [pure, Except.pure, Except.ok.injEq] at h; exact h.symm)
      | exact nomatch h
  | indDecl block nP =>
    -- task #293: a block the fold recognises as a pinned one installs
    -- the pin; everything else is the caller's `Ind`
    show (match basisPinHit block with
      | some kind => DeclBasisRun env kind env₂
      | none => Ind block nP env₂)
    have h' := h
    simp only [checkDecl] at h'
    cases hpin : basisPinHit block with
    | some kind =>
      rw [hpin] at h'
      exact declBasisRunOf h'
    | none => exact hind hpin h

end ConLeche.Semantics
