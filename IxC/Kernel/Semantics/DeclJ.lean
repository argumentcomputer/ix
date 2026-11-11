module

public import IxC.Kernel.Semantics.DeclRun
public import IxC.Kernel.Verify.DivModInv
public import IxC.Kernel.Semantics.DeclEta

@[expose] public section

/-!
# The declaration records over a judgement package

`DeclRun` (`Semantics/DeclRun.lean`) records what the kernel's fold checked
for a declaration: guards on stored data, and runs of the checker's own
fueled functions (`annotateCore`, `inferTypeCore`, `isDefEqCore`,
`ensureSortCore`, `checkDivModCerts`). The model tier (`Model/Harvest.lean`
and the installs it calls) reads those runs only through what they establish
about a model: the claims (`checkSoundAt`), readability (`acceptedReads_of`,
`inferReads_of`) and the scoping of their outputs.

This module states the same records over an abstract **judgement package**
(`Judgements`): one relation per checker function the records mention. Its two
instances are

* `runJ μ F`, the kernel's own runs at fuel `F`: `DeclRunJ (runJ μ F)` *is*
  `DeclRun μ F` (`declRun_eq_runJ`, by `rfl`), so nothing proved over
  `DeclRun` changes;
* the rules tier's derivations (`Rules.Infer`, `Rules.DefEq`, `Rules.Red`, an
  annotation relation, semantic level tests), the record an IxVM refinement
  produces (`IxVM.consistent`'s obligation L5).

A model-tier proof stated once over a package and the facts it needs about it
serves both. The one place the records differ by design is a theorem's stored
value (`Judgements.thmValue`): the kernel installs a theorem by its statement
and keeps the record's raw value (`Cached/Installed.lean`, phase A), while the
restated record stores the annotated value, so that the value can be read in
the model.

The divisibility certificates (`checkDivModCerts`, `Checker.lean:156`) become
the relation `DivModCertsJ`, one row per certificate: the guard, the applied
statement's annotation at depth 4, its inferred type, and that type's
definitional equality with the characteristic equation. -/

namespace Ix.Kernel.Semantics

open Ix.Kernel.Term Ix.Kernel.Verify

/-- **A judgement package**: one relation for each checker function the
declaration records mention. -/
structure Judgements (md : Mode) where
  /-- `e'` is the annotation of `e` at depth `d` (`annotateCore`). -/
  annot : Env md → Nat → Expr md → Expr md → Prop
  /-- `t` is the inferred type of `e` at depth `d` (`inferTypeCore`). -/
  infer : Env md → Nat → Expr md → Expr md → Prop
  /-- `a` and `b` are definitionally equal at depth `d` (`isDefEqCore = true`). -/
  defeq : Env md → Nat → Expr md → Expr md → Prop
  /-- `t` reduces to the sort `u` at depth `d` (`ensureSortCore`). -/
  sort : Env md → Nat → Expr md → Level → Prop
  /-- `u` is zero (the theorem's proposition test, `Level.isEquiv u .zero`). -/
  isZero : Level → Prop
  /-- The value a theorem is stored with, from its raw and its annotated value. -/
  thmValue : Expr md → Expr md → Expr md

/-- **The kernel's runs at fuel `F`**: the package `DeclRun μ F` is stated over. -/
def runJ (μ : CheckMode) (F : Nat) : Judgements md where
  annot env d e e' := annotateCore μ env F d e = .ok e'
  infer env d e t := inferTypeCore μ env F d e = .ok t
  defeq env d a b := isDefEqCore μ env F d a b = .ok true
  sort env d t u := ensureSortCore μ env F d t = .ok u
  isZero u := Level.isEquiv u .zero = some true
  thmValue value _ := value

/-! ## The records -/

/-- `ConstantValRun` over a package. -/
def ConstantValRunJ (J : Judgements md) (env : Env md) (cv : ConstantVal md)
    (type' : Expr md) : Prop :=
  (env.find? cv.name).isNone = true ∧
  reservedBasisNames.contains cv.name = false ∧
  cv.name.isProjFnShape = false ∧
  LevelParam.nodup cv.levelParams = true ∧
  cv.type.looseBVarsBounded 0 = true ∧
  cv.type.hasFvar = false ∧
  J.annot env 0 cv.type type' ∧
  type'.allLevelParamsDefined cv.levelParams = true ∧
  type'.constsResolve env = true ∧
  (∃ stype u, J.infer env 0 type' stype ∧ J.sort env 0 stype u)

/-- `ValueFrontRun` over a package. -/
def ValueFrontRunJ (J : Judgements md) (env : Env md) (cv : ConstantVal md)
    (value : Expr md) (type' value' : Expr md) : Prop :=
  value.looseBVarsBounded 0 = true ∧
  value.hasFvar = false ∧
  J.annot env 0 value value' ∧
  value'.allLevelParamsDefined cv.levelParams = true ∧
  value'.constsResolve env = true ∧
  (∃ vtype, J.infer env 0 value' vtype ∧ J.defeq env 0 vtype type')

/-- `NatEqsRun` over a package: each structural-`Nat` recurrence is a
definitional equality at depth 2. -/
def NatEqsRunJ (J : Judgements md) (env : Env md) (eqs : List (Expr md × Expr md)) : Prop :=
  ∀ eq ∈ eqs, J.defeq env 2 eq.1 eq.2

/-- **`checkDivModCerts` as a relation**: one row per certificate, in the
order the checker walks them. -/
inductive DivModCertsJ (J : Judgements md) (env : Env md) (c : Key md) (annVal : Expr md) :
    List (List (Expr md) × Expr md) → List (Expr md) → Prop where
  | nil : DivModCertsJ J env c annVal [] []
  | cons {hyps : List (Expr md)} {eqE proof appliedA tp : Expr md}
      {srest : List (List (Expr md) × Expr md)} {prest : List (Expr md)} :
      divModCertGuard env c annVal hyps eqE proof = true →
      J.annot env 4 (divModCertApplied (Expr.substConstAll c annVal proof)
        (hyps.map (Expr.substConst0 c annVal))) appliedA →
      J.infer env 4 appliedA tp →
      J.defeq env 4 tp (Expr.substConst0 c annVal eqE) →
      DivModCertsJ J env c annVal srest prest →
      DivModCertsJ J env c annVal ((hyps, eqE) :: srest) (proof :: prest)

/-- One row of `DivModCertsJ`, as a predicate on a statement and its proof: the
shape of `CertRunFacts` (`Verify/DivModInv.lean`) over a package. -/
def CertRowJ (J : Judgements md) (env : Env md) (c : Key md) (annVal : Expr md)
    (st : List (Expr md) × Expr md) (proof : Expr md) : Prop :=
  divModCertGuard env c annVal st.1 st.2 proof = true ∧
  ∃ appliedA tp,
    J.annot env 4 (divModCertApplied
      (Expr.substConstAll c annVal proof)
      (st.1.map (Expr.substConst0 c annVal))) appliedA ∧
    J.infer env 4 appliedA tp ∧
    J.defeq env 4 tp (Expr.substConst0 c annVal st.2)

/-- The relation's rows, pairwise (the form the model tier destructures). -/
theorem certRuns_of_divModCertsJ {J : Judgements md} {env : Env md} {c : Key md}
    {annVal : Expr md} :
    ∀ {stmts : List (List (Expr md) × Expr md)} {proofs : List (Expr md)},
      DivModCertsJ J env c annVal stmts proofs →
      CertRuns (CertRowJ J env c annVal) stmts proofs
  | _, _, .nil => .nil
  | _, _, .cons hg hann hinf hde rest =>
    .cons ⟨hg, _, _, hann, hinf, hde⟩ (certRuns_of_divModCertsJ rest)

/-- `DivModCertRun` over a package. -/
def DivModCertRunJ (J : Judgements md) (env env₂ : Env md) (c : Key md) (value' : Expr md) :
    Prop :=
  divModEnvGuard env₂ c = true ∧
  ∃ proofs : List (Expr md),
    divModCertsGuard proofs env c value' = true ∧
    DivModCertsJ J env c value' (divModCertStmts c) proofs

/-- `DeclDefnRun` over a package. -/
def DeclDefnRunJ (J : Judgements md) (env : Env md)
    (cv : ConstantVal md) (value : Expr md) (hint : ReducibilityHint)
    (env₂ : Env md) : Prop :=
  ∃ type' value',
    ConstantValRunJ J env cv type' ∧
    ValueFrontRunJ J env cv value type' value' ∧
    env₂ = ⟨.defnInfo ⟨cv.name, cv.levelParams, type'⟩ value' hint ::
      env.consts⟩ ∧
    (natOpNames.contains cv.name = true →
      natOpGuard env₂ cv.name = true ∧
      (natOpDeps cv.name).all (natOpStoredOk env₂) = true ∧
      NatEqsRunJ J env
        ((natOpEquations 0 cv.name).map fun eq =>
          (Expr.substConst0 cv.name value' eq.1,
           Expr.substConst0 cv.name value' eq.2))) ∧
    (natDivModNames.contains cv.name = true →
      DivModCertRunJ J env env₂ cv.name value')

/-- `DeclThmRun` over a package; the theorem is stored with
`J.thmValue value value'`. -/
def DeclThmRunJ (J : Judgements md) (env : Env md)
    (cv : ConstantVal md) (value : Expr md) (env₂ : Env md) : Prop :=
  ∃ type' value',
    ConstantValRunJ J env cv type' ∧
    (∃ stype u, J.infer env 0 type' stype ∧ J.sort env 0 stype u ∧ J.isZero u) ∧
    ValueFrontRunJ J env cv value type' value' ∧
    env₂ = ⟨.thmInfo ⟨cv.name, cv.levelParams, type'⟩ (J.thmValue value value') ::
      env.consts⟩

/-- `DeclOpaqueRun` over a package. -/
def DeclOpaqueRunJ (J : Judgements md) (env : Env md)
    (cv : ConstantVal md) (value : Expr md) (env₂ : Env md) : Prop :=
  ∃ type' value',
    ConstantValRunJ J env cv type' ∧
    ValueFrontRunJ J env cv value type' value' ∧
    env₂ = ⟨.axiomInfo ⟨cv.name, cv.levelParams, type'⟩ :: env.consts⟩

/-- `DeclAxiomRun` over a package. -/
def DeclAxiomRunJ (J : Judgements md) (env : Env md)
    (cv : ConstantVal md) (env₂ : Env md) : Prop :=
  (cv.name = quotSoundName ∧ env₂ = env) ∨
  ∃ type',
    ConstantValRunJ J env cv type' ∧
    (let cvA : ConstantVal md := ⟨cv.name, cv.levelParams, type'⟩
     (stdAxiomOk env cvA = true ∧
        env₂ = ⟨.axiomInfo cvA :: env.consts⟩) ∨
     (stdAxiomOk env cvA = false ∧
        cvA.name ≠ propextName ∧ cvA.name ≠ choiceName ∧
        cvA.name = sorryAxName ∧
        env₂ = env))

/-- **`DeclRun` over a package**: the same kind dispatch, the inductive
kind's payload a parameter as there. -/
def DeclRunJ (J : Judgements md)
    (Ind : List (ConstantInfo md) → Nat → Env md → Prop) (env : Env md) :
    (Declaration md) → Env md → Prop
  | .defnDecl cv value hint, env₂ => DeclDefnRunJ J env cv value hint env₂
  | .thmDecl cv value, env₂ => DeclThmRunJ J env cv value env₂
  | .opaqueDecl cv value, env₂ => DeclOpaqueRunJ J env cv value env₂
  | .axiomDecl cv, env₂ => DeclAxiomRunJ J env cv env₂
  | .basisDecl kind, env₂ => DeclBasisRun env kind env₂
  | .indDecl block nP, env₂ =>
    match basisPinHit block with
    | some kind => DeclBasisRun env kind env₂
    | none => Ind block nP env₂
  | .quotDecl k _, env₂ =>
    match k with
    | .type => DeclBasisRun env .quotK env₂
    | _ => env₂ = env

/-! ## The kernel's records are the run instance -/

theorem constantValRun_eq_runJ {μ : CheckMode} {F : Nat} {env : Env md}
    {cv : ConstantVal md} {type' : Expr md} :
    ConstantValRun μ F env cv type' = ConstantValRunJ (runJ μ F) env cv type' := rfl

theorem valueFrontRun_eq_runJ {μ : CheckMode} {F : Nat} {env : Env md}
    {cv : ConstantVal md} {value type' value' : Expr md} :
    ValueFrontRun μ F env cv value type' value' =
      ValueFrontRunJ (runJ μ F) env cv value type' value' := rfl

theorem natEqsRun_eq_runJ {μ : CheckMode} {F : Nat} {env : Env md}
    {eqs : List (Expr md × Expr md)} :
    NatEqsRun μ F env eqs = NatEqsRunJ (runJ μ F) env eqs := rfl

/-- The per-certificate facts of a successful certificate run
(`checkDivModCerts_inv`) are the relation's rows at the run package. -/
theorem divModCertsJ_of_certRuns {μ : CheckMode} {F : Nat} {env : Env md} {c : Key md}
    {annVal : Expr md} :
    ∀ {stmts : List (List (Expr md) × Expr md)} {proofs : List (Expr md)},
      CertRuns (CertRunFacts μ env F c annVal) stmts proofs →
      DivModCertsJ (runJ μ F) env c annVal stmts proofs
  | _, _, .nil => .nil
  | _, _, .cons ⟨hg, _, _, hann, hinf, hde⟩ rest =>
    .cons hg hann hinf hde (divModCertsJ_of_certRuns rest)

/-- The kernel's certificate run gives the relation at its runs (the
direction the restated records need: the fold holds the run). -/
theorem divModCertsJ_of_run {μ : CheckMode} {F : Nat} {env : Env md} {c : Key md}
    {annVal : Expr md} {stmts : List (List (Expr md) × Expr md)} {proofs : List (Expr md)}
    (h : checkDivModCerts (m := CheckM md) (fueledOps μ F) env c annVal stmts proofs = .ok true) :
    DivModCertsJ (runJ μ F) env c annVal stmts proofs :=
  divModCertsJ_of_certRuns (checkDivModCerts_inv h)

theorem divModCertRun_runJ {μ : CheckMode} {F : Nat} {env env₂ : Env md} {c : Key md}
    {value' : Expr md} (h : DivModCertRun μ F env env₂ c value') :
    DivModCertRunJ (runJ μ F) env env₂ c value' := by
  obtain ⟨hg, proofs, hpg, hrun⟩ := h
  exact ⟨hg, proofs, hpg, divModCertsJ_of_run hrun⟩

theorem declDefnRun_runJ {μ : CheckMode} {F : Nat} {env env₂ : Env md}
    {cv : ConstantVal md} {value : Expr md} {hint : ReducibilityHint}
    (h : DeclDefnRun μ F env cv value hint env₂) :
    DeclDefnRunJ (runJ μ F) env cv value hint env₂ := by
  obtain ⟨type', value', hcv, hvf, henv, hnat, hdm⟩ := h
  exact ⟨type', value', hcv, hvf, henv, hnat, fun hc => divModCertRun_runJ (hdm hc)⟩

theorem declThmRun_eq_runJ {μ : CheckMode} {F : Nat} {env env₂ : Env md}
    {cv : ConstantVal md} {value : Expr md} :
    DeclThmRun μ F env cv value env₂ = DeclThmRunJ (runJ μ F) env cv value env₂ := rfl

theorem declOpaqueRun_eq_runJ {μ : CheckMode} {F : Nat} {env env₂ : Env md}
    {cv : ConstantVal md} {value : Expr md} :
    DeclOpaqueRun μ F env cv value env₂ = DeclOpaqueRunJ (runJ μ F) env cv value env₂ := rfl

theorem declAxiomRun_eq_runJ {μ : CheckMode} {F : Nat} {env env₂ : Env md}
    {cv : ConstantVal md} :
    DeclAxiomRun μ F env cv env₂ = DeclAxiomRunJ (runJ μ F) env cv env₂ := rfl

/-- **The kernel's record gives the restated one at its runs**: the fold's
`DeclRun` is `DeclRunJ` at `runJ μ F` (the certificate run read as its
relation). -/
theorem declRun_runJ {μ : CheckMode} {F : Nat}
    {Ind : List (ConstantInfo md) → Nat → Env md → Prop} {env env₂ : Env md}
    {d : Declaration md} (h : DeclRun μ F Ind env d env₂) :
    DeclRunJ (runJ μ F) Ind env d env₂ := by
  cases d with
  | defnDecl cv value hint => exact declDefnRun_runJ h
  | thmDecl cv value => exact h
  | opaqueDecl cv value => exact h
  | axiomDecl cv => exact h
  | basisDecl kind => exact h
  | indDecl block nP => exact h
  | quotDecl k cv => exact h


/-! ## The η half over a package

`declEtaStepRun` reads only the records' freshness guards and cons shapes, which
`DeclRunJ` keeps; the same proof at any package. -/

/-- **The fold's η-closure half, over a package.** -/
theorem declEtaStepRunJ {J : Judgements md}
    {Ind : List (ConstantInfo md) → Nat → Env md → Prop}
    {env : Env md} {d : Declaration md} {env₂ : Env md}
    (hind : ∀ {block : List (ConstantInfo md)} {nP : Nat} {envI : Env md},
      Ind block nP envI → EtaFamiliesClosed envI)
    (hE : EtaFamiliesClosed env)
    (h : DeclRunJ J Ind env d env₂) : EtaFamiliesClosed env₂ := by
  cases d with
  | defnDecl cv value hint =>
    obtain ⟨type', value', hcv, -, rfl, -, -⟩ := h
    exact EtaFamiliesClosed.cons_nonind hE
      (Option.isNone_iff_eq_none.mp hcv.1) (fun _ _ heq => nomatch heq)
  | thmDecl cv value =>
    obtain ⟨type', value', hcv, -, -, rfl⟩ := h
    exact EtaFamiliesClosed.cons_nonind hE
      (Option.isNone_iff_eq_none.mp hcv.1) (fun _ _ heq => nomatch heq)
  | opaqueDecl cv value =>
    obtain ⟨type', value', hcv, -, rfl⟩ := h
    exact EtaFamiliesClosed.cons_nonind hE
      (Option.isNone_iff_eq_none.mp hcv.1) (fun _ _ heq => nomatch heq)
  | axiomDecl cv =>
    -- the `Quot.sound` arm (task #293) installs nothing
    rcases h with ⟨-, rfl⟩ | h
    · exact hE
    obtain ⟨type', hcv, harm⟩ := h
    have hfresh : env.find? cv.name = none :=
      Option.isNone_iff_eq_none.mp hcv.1
    rcases harm with ⟨-, rfl⟩ | ⟨-, -, -, -, rfl⟩
    · exact EtaFamiliesClosed.cons_nonind hE hfresh
        (fun _ _ heq => nomatch heq)
    · exact hE
  | basisDecl kind =>
    exact basisInstallRun_etaClosed kind.declsA h.2
      (basisIndOk_declsA kind) hE
  | quotDecl k cv =>
    -- the quotient package's `type` record installs the pinned block;
    -- its other records install nothing (task #293)
    cases k with
    | type => exact basisInstallRun_etaClosed _ h.2 (basisIndOk_declsA .quotK) hE
    | _ => exact (show env₂ = env from h) ▸ hE
  | indDecl block nP =>
    -- a block the fold recognises as a pinned one installs the pin
    -- (task #293)
    simp only [DeclRunJ] at h
    split at h
    · exact basisInstallRun_etaClosed _ h.2 (basisIndOk_declsA _) hE
    · exact hind h


/-! ## A declaration stream over a package -/

/-- **A stream of declaration records over a package**: each declaration's
record at the environment the previous ones built. The inductive kind's payload
is a parameter, read at the step's own environment. -/
inductive DeclsRunJ (J : Judgements md)
    (Ind : Env md → List (ConstantInfo md) → Nat → Env md → Prop) :
    Env md → List (Declaration md) → Env md → Prop where
  | nil {env : Env md} : DeclsRunJ J Ind env [] env
  | cons {env env₁ env₂ : Env md} {d : Declaration md} {ds : List (Declaration md)} :
      DeclRunJ J (Ind env) env d env₁ → DeclsRunJ J Ind env₁ ds env₂ →
      DeclsRunJ J Ind env (d :: ds) env₂

end Ix.Kernel.Semantics
