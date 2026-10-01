module

public import ConLeche.Verify.Cached.BridgeCSDecl
import ConLeche.Cached.ParsedC

public section

/-!
# The cached parsed-declaration driver, bridged (task #163)

Port of the SP layer of `ConLeche/Verify/BridgeP.lean` (and, at the end,
of `ConLeche/Verify/BridgePDecl.lean`) for the cached tier: each lemma
relates a `ParsedC` driver function (`ConLeche/Cached/ParsedC.lean`,
`checkConstantValC` …) to the generic declaration checker at the fueled
families, as a `SimC` from any invariant state.

The subjects are the `Expr`-native twins of the parsed-index drivers.
Against `BridgeP` the systematic deletions of the tier carry through —
no arena, hence no `Ext`, no `denoteT`/`denote` distinction and no
tier flag (`hoff`) anywhere — plus the representation differences the
`Expr` currency forces, all of which are *shrinkages*:

* the DAG-memoized syntactic guards are pure `Expr` walks —
  `Expr.looseBVarsBounded`/`Expr.hasFvar`/
  `Expr.allLevelParamsDefined`/`constsResolveFC` — and their agreement
  with the `Expr`-side guards is `ConLeche/Verify/Cached/GuardsC.lean`'s
  `*_spec` family, so every store-read peel disappears;
* the readback `readbackEM j` is the pure `Expr.toExpr j`
  (`toExpr_eq`: the memoized readback *is* the erasure), so every
  `readbackEM_eff` step disappears;
* `opSIxC` has no level-readback wrapper (levels are already trees),
  so `opSIxC_sim` is `ensureSortC_sim` plus the `ensureSort_atF`
  rewrite;
* `recordCConst`'s effect (`recordCConst_eff`,
  `ConLeche/Verify/Cached/SimCEff.lean`) takes `RelC` facts where
  `recordIConst_eff` took `denoteT` facts at a flag-off state.

`Declaration` is now one type for both tiers (task #285), so the
interned premise `denoteDeclP s₀.store pd = some d` has no counterpart
at all: the two drivers are given the same record.  Everything else —
the guard order, the branch structure, the pure comparand of every
statement — is byte-identical to the interned original's.
-/

namespace ConLeche.Cached

open ConLeche
open ConLeche.Expr

variable {mode : CheckMode}
variable {pins : List NatOpPinSet}

/-! ## The declaration

The parsed-index layer's premise was `denoteDeclP s₀.store pd = some d`
and the cached tier's a per-constructor erasure relation `DeclCRel`.
With one declaration type (task #285) there is nothing to relate: the
cached driver and the pure checker are given the SAME record, and the
per-branch `RelC` premises the relation carried are `rfl`. -/
section WalksP

variable {env : Env} {s₀ : CState}

private theorem fueledM_bind_pure' {α : Type} (x : FueledM α) :
    x >>= pure = x := by
  refine Subtype.ext (funext fun F => ?_)
  show x.val F >>= pure = x.val F
  cases x.val F <;> rfl

/-! ## The `Expr` guards agree with the `Expr` guards -/

/-- `Expr.hasFvar` is `Expr.hasFvar` of the erasure (the store-shaped
`hasFvar_spec'` at the unit store). -/
theorem hasFvar_spec {e : Expr} {ex : Expr}
    (h : e = ex) : e.hasFvar = ex.hasFvar :=
  hasFvar_spec' h

/-! ## Parsed-index entry operations -/

/-- Parsed `ensureSort` simulates the fueled family.  No level
readback: the cached currency's levels are already trees. -/
theorem opSIxC_sim (hμ : mode.verifiedChecks = true) (henv : EnvWF env) {d : Nat} {i : Expr} {e : Expr}
    (hs : CSOK mode env s₀) (hden : RelC i e) (hw : Expr.WScoped d e) :
    SimC mode env s₀ RelVC (opSIxC mode (mkFEnv env) d i)
      ((fueledOpsM mode).ensureSort env d e) := by
  have h1 : SimC mode env s₀ RelVC (opSIxC mode (mkFEnv env) d i)
      (ensureSort (fueledFns mode env) env d e) :=
    ensureSortC_sim (ssimC hμ env henv checkFuel) hs hden hw
  refine SimC.wr h1 (fun u F h => ⟨F, ?_⟩)
  rw [ensureSort_atF, ensureSort_def] at h
  exact h

/-! ## The parsed-declaration checker functions -/

/-- `checkConstantValC` simulates the generic `checkConstantVal` at the
fueled families on the erased header: the returned constant is the
fueled result, its type well-scoped, and the returned `Expr` is
related to it. -/
theorem checkConstantValC_sim (hμ : mode.verifiedChecks = true) (henv : EnvWF env) {cvp : ConstantVal}
    {tyE : Expr} (hs : CSOK mode env s₀) (hden : RelC cvp.type tyE) :
    SimC mode env s₀ (fun v w => v.1 = w ∧ v.1.name = cvp.name ∧
        Expr.WScoped 0 v.1.type ∧ RelC v.2 v.1.type)
      (checkConstantValC mode (mkFEnv env) cvp)
      (checkConstantVal (fueledOpsM mode) env
        ⟨cvp.name, cvp.levelParams, tyE⟩) := by
  obtain rfl := hden
  unfold checkConstantValC checkConstantVal
  simp only [mkFEnv_find?]
  by_cases h1 : (env.find? cvp.name).isSome = true
  · simp only [if_pos h1]
    exact SimC.throw_bind
  simp only [if_neg h1]
  by_cases h2 : reservedBasisNames.contains cvp.name = true
  · simp only [if_pos h2]
    exact SimC.throw_bind
  simp only [if_neg h2]
  by_cases h3 : cvp.name.isProjFnShape = true
  · simp only [if_pos h3]
    exact SimC.throw_bind
  simp only [if_neg h3]
  by_cases h4 : Name.nodup cvp.levelParams = true
  case neg =>
    simp only [if_neg h4]
    exact SimC.throw_bind
  simp only [if_pos h4]
  by_cases h5 : Expr.looseBVarsBounded 0 cvp.type = true
  case neg =>
    simp only [if_neg h5]
    exact SimC.throw_bind
  simp only [if_pos h5]
  rw [hasFvar_spec rfl]
  by_cases h6 : Expr.hasFvar cvp.type = true
  · simp only [if_pos h6]
    exact SimC.throw_bind
  simp only [if_neg h6]
  refine SimC.bind ((ssimC hμ env henv checkFuel).annotate hs
      rfl
      (Expr.WScoped.of_not_hasFvar (Bool.not_eq_true _ ▸ h6)))
    (fun s₁ jA w hs₁ hP => ?_)
  obtain ⟨hjA, hwty⟩ := hP
  obtain rfl := hjA
  rw [Expr.allLevelParamsDefinedC_spec]
  by_cases h7 : Expr.allLevelParamsDefined cvp.levelParams jA = true
  case neg =>
    simp only [if_neg h7]
    exact SimC.throw_bind
  simp only [if_pos h7]
  rw [constsResolveFC_spec, constsResolveF_eq]
  by_cases h8 : Expr.constsResolve env jA = true
  case neg =>
    simp only [if_neg h8]
    exact SimC.throw_bind
  simp only [if_pos h8]
  refine SimC.bind ((ssimC hμ env henv checkFuel).infer hs₁ rfl hwty)
    (fun s₂ jsty wsty hs₂ hP₂ => ?_)
  obtain ⟨hjsty, hwsty⟩ := hP₂
  refine SimC.bind (opSIxC_sim hμ henv hs₂ hjsty hwsty)
    (fun s₃ u u' hs₃ hP₃ => ?_)
  exact SimC.pure hs₃ ⟨rfl, rfl, hwty, rfl⟩

/-- `checkDefnValC` simulates the generic `checkDefnVal`: the pushed
index is `mkFEnv` of the fueled environment, whose head stores the
annotated (fvar-free) value. -/
theorem checkDefnValC_sim (hμ : mode.verifiedChecks = true) (henv : EnvWF env) {cvA : ConstantVal}
    {jty : Expr} {value : Expr} {ve : Expr} {hint : ReducibilityHint}
    (htf : Expr.WScoped 0 cvA.type) (hjty : RelC jty cvA.type)
    (hdenv : RelC value ve) (hs : CSOK mode env s₀) :
    SimC mode env s₀ (fun v w => v.env = w ∧ v = mkFEnv v.env ∧
        ∀ cv' v' h', v.env.find? cvA.name = some (.defnInfo cv' v' h') →
          v'.hasFvar = false)
      (checkDefnValC mode (mkFEnv env) cvA jty value hint)
      (checkDefnVal (fueledOpsM mode) env cvA ve hint) := by
  obtain rfl := hdenv
  unfold checkDefnValC checkDefnVal
  by_cases h1 : Expr.looseBVarsBounded 0 value = true
  case neg =>
    simp only [if_neg h1]
    exact SimC.throw_bind
  simp only [if_pos h1]
  rw [hasFvar_spec rfl]
  by_cases h2 : Expr.hasFvar value = true
  · simp only [if_pos h2]
    exact SimC.throw_bind
  simp only [if_neg h2]
  refine SimC.bind ((ssimC hμ env henv checkFuel).annotate hs rfl
      (Expr.WScoped.of_not_hasFvar (Bool.not_eq_true _ ▸ h2)))
    (fun s₁ jv w hs₁ hP => ?_)
  obtain ⟨hjv, hwv⟩ := hP
  obtain rfl := hjv
  rw [Expr.allLevelParamsDefinedC_spec]
  by_cases h3 : Expr.allLevelParamsDefined cvA.levelParams jv = true
  case neg =>
    simp only [if_neg h3]
    exact SimC.throw_bind
  simp only [if_pos h3]
  rw [constsResolveFC_spec, constsResolveF_eq]
  by_cases h4 : Expr.constsResolve env jv = true
  case neg =>
    simp only [if_neg h4]
    exact SimC.throw_bind
  simp only [if_pos h4]
  refine SimC.bind_left (recordCConst_eff hs₁ hjty
      (fun vE' vi h => by
        cases h
        exact rfl))
    (fun s₂' u hs₂' hQ' => ?_)
  refine SimC.bind ((ssimC hμ env henv checkFuel).infer hs₂' rfl hwv)
    (fun s₂ jvt wvt hs₂ hP₂ => ?_)
  obtain ⟨hjvt, hwvt⟩ := hP₂
  refine SimC.bind ((ssimC hμ env henv checkFuel).defeq hs₂ hjvt hjty hwvt htf)
    (fun s₃ b b' hs₃ hP₃ => ?_)
  obtain rfl : b = b' := hP₃
  cases b with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    exact SimC.throw_bind
  | true =>
    simp only [↓reduceIte]
    refine SimC.pure hs₃ ⟨rfl, push_mkFEnv env _, ?_⟩
    intro cv' v' h' hf
    rw [show ((mkFEnv env).push (.defnInfo cvA jv hint)).env =
      ⟨.defnInfo cvA jv hint :: env.consts⟩ from rfl] at hf
    rw [Env.find?_cons, if_pos (show (ConstantInfo.defnInfo cvA jv
      hint).name = cvA.name from rfl)] at hf
    simp only [Option.some.injEq, ConstantInfo.defnInfo.injEq] at hf
    obtain ⟨-, rfl, -⟩ := hf
    exact Expr.not_hasFvar_of_fvarsBelow_zero hwv.fvarsBelow

/-- `checkThmValC` simulates the generic `checkThmVal`. -/
theorem checkThmValC_sim (hμ : mode.verifiedChecks = true) (henv : EnvWF env) {cvA : ConstantVal}
    {jty : Expr} {value : Expr} {ve : Expr}
    (htf : Expr.WScoped 0 cvA.type) (hjty : RelC jty cvA.type)
    (hdenv : RelC value ve) (hs : CSOK mode env s₀) :
    SimC mode env s₀ (fun v w => v.env = w ∧ v = mkFEnv v.env)
      (checkThmValC mode (mkFEnv env) cvA jty value)
      (checkThmVal (fueledOpsM mode) env cvA ve) := by
  unfold checkThmValC checkThmVal
  refine SimC.bind ((ssimC hμ env henv checkFuel).infer hs hjty htf)
    (fun s₁ jsty wsty hs₁ hP => ?_)
  obtain ⟨hjsty, hwsty⟩ := hP
  refine SimC.bind (opSIxC_sim hμ henv hs₁ hjsty hwsty)
    (fun s₂ u u' hs₂ hP₂ => ?_)
  obtain rfl : u = u' := hP₂
  refine SimC.bind (SimC.liftFueled _ _ hs₂)
    (fun s₃ b b' hs₃ hP₃ => ?_)
  obtain rfl : b = b' := hP₃
  cases b with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    exact SimC.throw_bind
  | true =>
  simp only [↓reduceIte]
  obtain rfl := hdenv
  by_cases h1 : Expr.looseBVarsBounded 0 value = true
  case neg =>
    simp only [if_neg h1]
    exact SimC.throw_bind
  simp only [if_pos h1]
  rw [hasFvar_spec rfl]
  by_cases h2 : Expr.hasFvar value = true
  · simp only [if_pos h2]
    exact SimC.throw_bind
  simp only [if_neg h2]
  refine SimC.bind ((ssimC hμ env henv checkFuel).annotate hs₃ rfl
      (Expr.WScoped.of_not_hasFvar (Bool.not_eq_true _ ▸ h2)))
    (fun s₄ jv w hs₄ hP₄ => ?_)
  obtain ⟨hjv, hwv⟩ := hP₄
  obtain rfl := hjv
  rw [Expr.allLevelParamsDefinedC_spec]
  by_cases h3 : Expr.allLevelParamsDefined cvA.levelParams jv = true
  case neg =>
    simp only [if_neg h3]
    exact SimC.throw_bind
  simp only [if_pos h3]
  rw [constsResolveFC_spec, constsResolveF_eq]
  by_cases h4 : Expr.constsResolve env jv = true
  case neg =>
    simp only [if_neg h4]
    exact SimC.throw_bind
  simp only [if_pos h4]
  refine SimC.bind_left (recordCConst_eff hs₄ hjty
      (fun vE' vi h => nomatch h))
    (fun s₅' u₀ hs₅' hQ' => ?_)
  refine SimC.bind ((ssimC hμ env henv checkFuel).infer hs₅' rfl hwv)
    (fun s₅ jvt wvt hs₅ hP₅ => ?_)
  obtain ⟨hjvt, hwvt⟩ := hP₅
  refine SimC.bind ((ssimC hμ env henv checkFuel).defeq hs₅ hjvt hjty hwvt htf)
    (fun s₆ b b' hs₆ hP₆ => ?_)
  obtain rfl : b = b' := hP₆
  cases b with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    exact SimC.throw_bind
  | true =>
    simp only [↓reduceIte]
    exact SimC.pure hs₆ ⟨rfl, push_mkFEnv env _⟩

/-- `checkOpaqueValC` simulates the generic `checkOpaqueVal`. -/
theorem checkOpaqueValC_sim (hμ : mode.verifiedChecks = true) (henv : EnvWF env) {cvA : ConstantVal}
    {jty : Expr} {value : Expr} {ve : Expr}
    (htf : Expr.WScoped 0 cvA.type) (hjty : RelC jty cvA.type)
    (hdenv : RelC value ve) (hs : CSOK mode env s₀) :
    SimC mode env s₀ (fun v w => (v.env = w ∧ v = mkFEnv v.env) ∧
        ve.hasFvar = false)
      (checkOpaqueValC mode (mkFEnv env) cvA jty value)
      (checkOpaqueVal (fueledOpsM mode) env cvA ve) := by
  obtain rfl := hdenv
  unfold checkOpaqueValC checkOpaqueVal
  by_cases h1 : Expr.looseBVarsBounded 0 value = true
  case neg =>
    simp only [if_neg h1]
    exact SimC.throw_bind
  simp only [if_pos h1]
  rw [hasFvar_spec rfl]
  by_cases h2 : Expr.hasFvar value = true
  · simp only [if_pos h2]
    exact SimC.throw_bind
  simp only [if_neg h2]
  refine SimC.bind ((ssimC hμ env henv checkFuel).annotate hs rfl
      (Expr.WScoped.of_not_hasFvar (Bool.not_eq_true _ ▸ h2)))
    (fun s₁ jv w hs₁ hP => ?_)
  obtain ⟨hjv, hwv⟩ := hP
  obtain rfl := hjv
  rw [Expr.allLevelParamsDefinedC_spec]
  by_cases h3 : Expr.allLevelParamsDefined cvA.levelParams jv = true
  case neg =>
    simp only [if_neg h3]
    exact SimC.throw_bind
  simp only [if_pos h3]
  rw [constsResolveFC_spec, constsResolveF_eq]
  by_cases h4 : Expr.constsResolve env jv = true
  case neg =>
    simp only [if_neg h4]
    exact SimC.throw_bind
  simp only [if_pos h4]
  refine SimC.bind_left (recordCConst_eff hs₁ hjty
      (fun vE' vi h => nomatch h))
    (fun s₁' u hs₁' hQ' => ?_)
  refine SimC.bind ((ssimC hμ env henv checkFuel).infer hs₁' rfl hwv)
    (fun s₂ jvt wvt hs₂ hP₂ => ?_)
  obtain ⟨hjvt, hwvt⟩ := hP₂
  refine SimC.bind ((ssimC hμ env henv checkFuel).defeq hs₂ hjvt hjty hwvt htf)
    (fun s₃ b b' hs₃ hP₃ => ?_)
  obtain rfl : b = b' := hP₃
  cases b with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    exact SimC.throw_bind
  | true =>
    simp only [↓reduceIte]
    exact SimC.pure hs₃ ⟨⟨rfl, push_mkFEnv env _⟩,
      Bool.not_eq_true _ ▸ h2⟩

/-! ## The converted declaration -/

/-- The pinned-block install simulates its generic twin (task #293:
three of `checkDeclC`'s arms share this body). -/
theorem checkBasisDeclC_sim (hs : CSOK mode env s₀) (kind : BasisKind) :
    SimC mode env s₀ (fun v w => v.env = w ∧ v = mkFEnv v.env)
      (checkBasisDeclC (mkFEnv env) kind)
      (checkBasisDecl (m := FueledM) env kind) := by
  show SimC mode env s₀ _ (do
      if kind = .quotK then
        unless (mkFEnv env).find? eqName = some eqA do
          throw (.notImplemented
            "quotient basis requires the pinned Eq basis")
      kind.declsA.foldlM installBasisDeclF (mkFEnv env) :
      CheckCM FEnv) _
  unfold checkBasisDecl
  dsimp only
  rw [installBasisFoldF_pushC]
  simp only [mkFEnv_find?]
  by_cases hq : kind = .quotK
  · simp only [if_pos hq]
    by_cases he : env.find? eqName = some eqA
    · simp only [if_pos he]
      rw [← fueledM_bind_pure'
        (kind.declsA.foldlM installBasisDecl env : FueledM Env)]
      refine SimC.bind (installBasisFoldS_sim _ env hs)
        (fun s₁ e e' hs₁ hP => ?_)
      obtain rfl : e = e' := hP
      exact SimC.pure hs₁ ⟨rfl, rfl⟩
    · simp only [if_neg he]
      exact SimC.throw_bind
  · simp only [if_neg hq]
    rw [← fueledM_bind_pure'
      (kind.declsA.foldlM installBasisDecl env : FueledM Env)]
    refine SimC.bind (installBasisFoldS_sim _ env hs)
      (fun s₁ e e' hs₁ hP => ?_)
    obtain rfl : e = e' := hP
    exact SimC.pure hs₁ ⟨rfl, rfl⟩

/-- The non-inductive branches of the converted-declaration driver
`checkDeclC` simulate the generic `checkDecl` at the fueled families
on the related declaration.  (There is no bracket in the cached driver
— `checkDeclC` *is* the plain path — so this is the mirror of
`checkDeclSPPlain_sim`.) -/
theorem checkDeclC_sim (hμ : mode.verifiedChecks = true) (henv : EnvWF env) (hs : CSOK mode env s₀)
    {pd : Declaration}
    (hnotind : ∀ block nP, pd ≠ .indDecl block nP) :
    SimC mode env s₀ (fun v w => v.env = w ∧ v = mkFEnv v.env)
      (checkDeclC mode pins (mkFEnv env) pd)
      (checkDecl mode (fueledOpsM mode) pins env pd) := by
  cases pd with
  | indDecl block nP => exact absurd rfl (hnotind _ _)
  | basisDecl kind => exact checkBasisDeclC_sim hs kind
  | quotDecl k cv =>
    -- task #293: the `type` record installs the pinned block, the other
    -- members install nothing, and a mismatch throws on both sides
    unfold checkDeclC checkDecl
    dsimp only
    by_cases hp : quotPinHit k cv = true
    · simp only [if_pos hp]
      cases k
      · exact checkBasisDeclC_sim hs .quotK
      all_goals exact SimC.pure hs ⟨rfl, rfl⟩
    · simp only [if_neg hp]
      exact SimC.throw
  | axiomDecl cv =>
    unfold checkDeclC checkDecl
    dsimp only
    -- task #293: `Quot.sound` is compared with the pin on both sides
    by_cases hqs : cv.name = quotSoundName
    · simp only [if_pos hqs]
      split
      · exact SimC.pure hs ⟨rfl, rfl⟩
      · exact SimC.throw
    simp only [if_neg hqs]
    refine SimC.bind (checkConstantValC_sim hμ henv hs rfl)
      (fun s₁ pr cvA hs₁ hP => ?_)
    obtain ⟨cvR, jty⟩ := pr
    obtain ⟨rfl, hname, hwty, hjty⟩ := hP
    dsimp only at hjty ⊢
    simp only [stdAxiomOkF_eq, trustCompilerOkF_eq, ofReduceAxOkF_eq]
    by_cases h1 : stdAxiomOk env cvR = true
    · simp only [if_pos h1]
      refine SimC.bind_left (recordCConst_eff hs₁ hjty
          (fun vE vi h => nomatch h))
        (fun s₂ u hs₂ hQ => ?_)
      exact SimC.pure hs₂ ⟨rfl, push_mkFEnv env _⟩
    · simp only [if_neg h1]
      by_cases htc : cvR.name = trustCompilerName
      · simp only [if_pos htc]
        by_cases htok : trustCompilerOk env cvR = true
        · simp only [if_pos htok]
          refine SimC.bind_left (recordCConst_eff hs₁ hjty
              (fun vE vi h => nomatch h))
            (fun s₂ u hs₂ hQ => ?_)
          exact SimC.pure hs₂ ⟨rfl, push_mkFEnv env _⟩
        · simp only [if_neg htok]
          exact SimC.throw
      · simp only [if_neg htc]
        by_cases hor : cvR.name = ofReduceNatName ∨
            cvR.name = ofReduceBoolName
        · simp only [if_pos hor]
          by_cases hoo : ofReduceAxOk env cvR = true
          · simp only [if_pos hoo]
            refine SimC.bind_left (recordCConst_eff hs₁ hjty
                (fun vE vi h => nomatch h))
              (fun s₂ u hs₂ hQ => ?_)
            exact SimC.pure hs₂ ⟨rfl, push_mkFEnv env _⟩
          · simp only [if_neg hoo]
            exact SimC.throw
        · simp only [if_neg hor]
          by_cases h2 : cvR.name = propextName ∨ cvR.name = choiceName
          · simp only [if_pos h2]
            exact SimC.throw
          · simp only [if_neg h2]
            by_cases h3 : cvR.name = sorryAxName
            · simp only [if_pos h3]
              exact SimC.pure hs₁ ⟨rfl, rfl⟩
            · simp only [if_neg h3]
              exact SimC.throw
  | thmDecl cv value =>
    unfold checkDeclC checkDecl
    dsimp only
    refine SimC.bind (checkConstantValC_sim hμ henv hs rfl)
      (fun s₁ pr cvA hs₁ hP => ?_)
    obtain ⟨cvR, jty⟩ := pr
    obtain ⟨rfl, hname, hwty, hjty⟩ := hP
    dsimp only at hjty ⊢
    exact SimC.mono (fun v w h => h)
      (checkThmValC_sim hμ henv hwty hjty rfl hs₁)
  | opaqueDecl cv value =>
    unfold checkDeclC checkDecl
    dsimp only
    refine SimC.bind (checkConstantValC_sim hμ henv hs rfl)
      (fun s₁ pr cvA hs₁ hP => ?_)
    obtain ⟨cvR, jty⟩ := pr
    obtain ⟨rfl, hname, hwty, hjty⟩ := hP
    dsimp only at hjty ⊢
    -- the cached arm branches BEFORE the push (RC linearity), the spec
    -- after it: the case split comes first on both sides
    by_cases hred : reduceOpNames.contains cvR.name = true
    case neg =>
      simp only [if_neg hred]
      rw [← bind_pure (checkOpaqueValC mode (mkFEnv env) _ jty _)]
      refine SimC.bind (checkOpaqueValC_sim hμ henv hwty hjty rfl hs₁)
        (fun s₂ fe2 env2 hs₂ hP₂ => ?_)
      obtain ⟨⟨henvEq, hmk⟩, hvf⟩ := hP₂
      subst henvEq
      rw [hmk]
      simp only [mkFEnv_env]
      exact SimC.pure hs₂ ⟨rfl, hmk ▸ hmk⟩
    simp only [if_pos hred]
    refine SimC.bind (checkOpaqueValC_sim hμ henv hwty hjty rfl hs₁)
      (fun s₂ fe2 env2 hs₂ hP₂ => ?_)
    obtain ⟨⟨henvEq, hmk⟩, hvf⟩ := hP₂
    subst henvEq
    rw [hmk]
    simp only [mkFEnv_env]
    rw [checkReducePinF_eq]
    refine SimC.bind (checkReducePinS_sim hμ henv hvf hs₂)
      (fun s₄ u u' hs₄ hP₄ => ?_)
    exact SimC.pure hs₄ ⟨rfl, hmk ▸ hmk⟩
  | defnDecl cv value hint =>
    unfold checkDeclC checkDecl
    dsimp only
    refine SimC.bind (checkConstantValC_sim hμ henv hs rfl)
      (fun s₁ pr cvA hs₁ hP => ?_)
    obtain ⟨cvR, jty⟩ := pr
    obtain ⟨rfl, hname, hwty, hjty⟩ := hP
    dsimp only at hjty ⊢
    by_cases hb : (natOpNames.contains cvR.name ||
        natDivModNames.contains cvR.name) = true
    case neg =>
      obtain ⟨h1, h4⟩ : ¬(natOpNames.contains cvR.name = true) ∧
          ¬(natDivModNames.contains cvR.name = true) := by
        simpa [not_or] using hb
      simp only [if_neg hb, if_neg h1, if_neg h4]
      rw [← bind_pure (checkDefnValC mode (mkFEnv env) _ jty _ _)]
      refine SimC.bind (checkDefnValC_sim hμ henv hwty hjty rfl hs₁)
        (fun s₂ fe2 env2 hs₂ hP₂ => ?_)
      obtain ⟨henvEq, hmk, -⟩ := hP₂
      subst henvEq
      exact SimC.pure hs₂ ⟨rfl, hmk⟩
    simp only [if_pos hb]
    refine SimC.bind (checkDefnValC_sim hμ henv hwty hjty rfl hs₁)
      (fun s₂ fe2 env2 hs₂ hP₂ => ?_)
    obtain ⟨henvEq, hmk, hv'fD⟩ := hP₂
    subst henvEq
    rw [hmk]
    simp only [natOpGuardF_eq, natOpStoredOkF_eq_fun, mkFEnv_find?,
      checkDivModPinF_eq, mkFEnv_env]
    by_cases h1 : natOpNames.contains cvR.name = true
    case neg =>
      simp only [if_neg h1]
      by_cases h4 : natDivModNames.contains cvR.name = true
      case neg =>
        simp only [if_neg h4]
        exact SimC.pure hs₂ ⟨rfl, hmk ▸ hmk⟩
      simp only [if_pos h4]
      refine SimC.bind (checkDivModPinS_sim hμ henv
          (List.contains_iff_mem.mp h4) hv'fD hs₂)
        (fun s₃ u u' hs₃ hP₃ => ?_)
      exact SimC.pure hs₃ ⟨rfl, hmk ▸ hmk⟩
    simp only [if_pos h1]
    by_cases h2 : (natOpGuard fe2.env cvR.name &&
        (natOpDeps cvR.name).all (natOpStoredOk fe2.env)) = true
    case neg => simp only [if_neg h2]; exact SimC.throw_bind
    simp only [h2, ↓reduceIte]
    cases hfind : fe2.env.find? cvR.name with
    | none => exact SimC.throw_bind
    | some ci =>
      cases ci with
      | defnInfo cvS value' hintS =>
        dsimp only
        have hvf : value'.hasFvar = false := hv'fD _ _ _ hfind
        have hsc : ∀ eq ∈ (natOpEquations 0 cvR.name).map
            (fun eq => (Expr.substConst0 cvR.name value' eq.1,
              Expr.substConst0 cvR.name value' eq.2)),
            (eq.1.wscopedB 2 = true) ∧ (eq.2.wscopedB 2 = true) := by
          intro eq heq
          obtain ⟨eq₀, heq₀, rfl⟩ := List.mem_map.mp heq
          obtain ⟨hs1, hs2⟩ := natOpEquations_wscopedB
            (by simpa using h1) eq₀ heq₀
          exact ⟨wscopedB_substConst0 hvf _ hs1,
            wscopedB_substConst0 hvf _ hs2⟩
        refine SimC.bind (certifyNatEqsS_sim hμ henv hsc hs₂)
          (fun s₃ ok ok' hs₃ hP₃ => ?_)
        obtain rfl : ok = ok' := hP₃
        cases ok with
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte]
          exact SimC.throw_bind
        | true =>
          simp only [↓reduceIte]
          by_cases h4 : natDivModNames.contains cvR.name = true
          case neg =>
            simp only [if_neg h4]
            exact SimC.pure hs₃ ⟨rfl, hmk ▸ hmk⟩
          simp only [if_pos h4]
          refine SimC.bind (checkDivModPinS_sim hμ henv
              (List.contains_iff_mem.mp h4) hv'fD hs₃)
            (fun s₄ u u' hs₄ hP₄ => ?_)
          exact SimC.pure hs₄ ⟨rfl, hmk ▸ hmk⟩
      | axiomInfo cv' => exact SimC.throw_bind
      | thmInfo cv' v' => exact SimC.throw_bind
      | indInfo cv' caps => exact SimC.throw_bind
      | ctorInfo cv' nP nF => exact SimC.throw_bind
      | recInfo cv' mI rP rules => exact SimC.throw_bind
      | projInfo _ => exact SimC.throw_bind

/-- One step of the converted-declaration fold: a successful run from a
residue state is reproduced by the pure fueled checker on the same
declaration, and the residue threads to the next step.  The cached
driver has no bracket and no index-range check, so the step is `flushC`
followed by `checkDeclC`. -/
theorem checkDeclStepC_run (hμ : mode.verifiedChecks = true) {env : Env} (henv : EnvWF env) {pd : Declaration}
    {s₀ : CState} (hres : CSOKF s₀) {fe' : FEnv} {s' : CState}
    (h : checkDeclStepC mode pins (mkFEnv env) pd s₀ = .ok (fe', s')) :
    CSOKF s' ∧ fe' = mkFEnv fe'.env ∧
    ∃ F, checkDecl mode (fueledOps mode F) pins env pd = .ok fe'.env := by
  unfold checkDeclStepC at h
  obtain ⟨u, s₁, hflush, h⟩ := bindC_ok h
  rw [flushC_run] at hflush
  injection hflush with hflush
  obtain rfl : s₀.flushed = s₁ := congrArg Prod.snd hflush
  have hcsok : CSOK mode env s₀.flushed := flushC_csok hres
  have main : (∀ block nP, pd ≠ .indDecl block nP) →
      CSOKF s' ∧ fe' = mkFEnv fe'.env ∧
      ∃ F, checkDecl mode (fueledOps mode F) pins env pd = .ok fe'.env := by
    intro hind
    obtain ⟨hs', v, ⟨henvEq, hmk⟩, F, hF⟩ :=
      (checkDeclC_sim hμ henv hcsok hind) fe' s' h
    refine ⟨hs'.residue, hmk, F, ?_⟩
    rw [← checkDecl_datF, henvEq]
    exact hF
  cases pd with
  | indDecl block nP =>
    -- task #293: a block the fold recognises as one of the five pinned
    -- ones installs the pin, on both sides; the declared parameter
    -- count (task #228) below it is a guard whose `false` throws on
    -- both sides, so only the passing branch reaches the bridge
    have hd : (match basisPinHit block with
        | some kind => checkBasisDeclC (mkFEnv env) kind
        | none =>
          if indParamsOk nP block = true then
            (match nativeParts? nP block with
              | some p => checkNativeS mode (mkFEnv env) p
              | none => checkIndDeclSF mode (mkFEnv env) block)
          else throw (CheckError.invalid "number of parameters mismatch"))
        s₀.flushed = .ok (fe', s') := h
    cases hpin : basisPinHit block with
    | some kind =>
      rw [hpin] at hd
      obtain ⟨hs', v, ⟨henvEq, hmk⟩, F, hF⟩ :=
        (checkBasisDeclC_sim hcsok kind) fe' s' hd
      refine ⟨hs'.residue, hmk, F, ?_⟩
      show checkDecl mode (fueledOps mode F) pins env (.indDecl block nP) = _
      simp only [checkDecl, hpin]
      rw [← checkBasisDecl_datF, henvEq]
      exact hF
    | none =>
      rw [hpin] at hd
      by_cases hok : indParamsOk nP block = true
      · rw [if_pos hok] at hd
        obtain ⟨hres', hfe, F, hF⟩ :=
          checkModeledOrNativeSF_run hμ henv hpin hok hres.flushed hd
        exact ⟨hres', hfe, F, hF⟩
      · rw [if_neg hok] at hd
        exact nomatch hd
  | defnDecl cv value hint => exact main (fun _ _ h => Declaration.noConfusion h)
  | thmDecl cv value => exact main (fun _ _ h => Declaration.noConfusion h)
  | opaqueDecl cv value => exact main (fun _ _ h => Declaration.noConfusion h)
  | axiomDecl cv => exact main (fun _ _ h => Declaration.noConfusion h)
  | basisDecl kind => exact main (fun _ _ h => Declaration.noConfusion h)
  | quotDecl k cv => exact main (fun _ _ h => Declaration.noConfusion h)

end WalksP

end ConLeche.Cached
