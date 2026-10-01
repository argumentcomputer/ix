module

public import ConLeche.Semantics.DeclIndRun
import ConLeche.Verify.Inductives.SumWF
public import ConLeche.Verify.Inductives.FixWF

@[expose] public section

/-!
# `DeclNativeRun`: the direct recursive declaration relation
(task #188)

The direct recursive arm of `checkDecl`'s `.indDecl` clause
(`checkNative`, `ConLeche/Kernel/Inductives/NativeInstall.lean`), recorded as
a run relation exactly as `DeclSumRun`: the three front guards
(positivity — no negative field kind; the elimination restriction —
a large eliminator needs a provably nonzero sort, the one-constructor
`Prop` case being declined; the constructors' distinct names), the
former's run (the sum's stage), the constructors' runs at the
former's environment with the resolution guard pointed at that same
environment, the field kinds re-checked on the annotated types, the
recursor's run at the environment holding all constructors, and the
install spine.  The `.indDecl` run dispatch, with the recursive arm
below the two non-recursive ones, closes the module.
-/

namespace ConLeche.Semantics

open ConLeche (Env Expr Name Level CheckMode ConstantVal ConstantInfo
  InductiveShape NativeParts RecRule fueledOps checkSumInd checkSumCtors
  checkNativeRec checkNative checkNativeTable consSumCtors sumRules
  nativeFieldsOk nativeCaps)

/-- **The direct recursive declaration, as checked**: the stage runs
of `checkNative`.  `env` is the pre-block environment.  The pass the
install settled on (task #268) is the one recorded: the former at the
record at some `is_rec` verdict, the constructors at its environment,
the kinds classified on THOSE constructors, and the classified record
equal to the one the former carries. -/
def DeclNativeRun (μ : CheckMode) (F : Nat) (env : Env)
    (p₀ : NativeParts) (env₂ : Env) : Prop :=
  (p₀.ctors.map (·.1.name)).Nodup ∧
  ∃ (isRec : Bool) (env₁ : Env) (cvTa : ConstantVal) (p₁ : InductiveShape) (p : NativeParts)
    (ctorsA : List (ConstantVal × Nat)) (sortss : List (List Level))
    (kinds : List (List RecFieldKind))
    (cvRa : ConstantVal) (rhss : List Expr) (tfvs : List Expr) (trest : Expr)
    (isorts : List Level),
    -- the former's run completes the record with the sort it read
    -- (task #195; task #210 Part B: this route too); every later stage
    -- runs on the completed record `p` — the sort and the kinds
    checkSumInd (m := ConLeche.CheckM) (fueledOps μ F) env p₀.toInductiveShape
      (fun p₁ => nativeCapsAt p₁ isRec) = .ok (env₁, cvTa, p₁) ∧
    p = (p₀.complete p₁).withKinds kinds ∧
    checkSumCtors (m := ConLeche.CheckM) (fueledOps μ F) env₁ env₁ p.cvT.name
      p.cvT.levelParams p.nP p.nIdx p.resSort p.isProp p.large cvTa p.ctors
      = .ok (ctorsA, sortss) ∧
    classifyFixKinds (m := ConLeche.CheckM) p.cvT.name p.cvT.levelParams p.nP p.nIdx ctorsA
      = .ok kinds ∧
    -- the record the block owes is the one the former carries
    nativeCaps p = nativeCapsAt p₁ isRec ∧
    -- the elimination restriction: a large eliminator needs a provably
    -- nonzero sort unless the block has one constructor (the subsingleton
    -- case, task #202 Stage A2)
    (p.large = true → p.resSort.isNeverZero = true ∨ p.ctors.length < 2) ∧
    openPisAtFvars (p.nP + p.nIdx) cvTa.type 0 = some (tfvs, trest) ∧
    ConLeche.checkStructFieldSortsI (m := ConLeche.CheckM) (fueledOps μ F) env₁ true false p.resSort
      p.nP (tfvs.drop p.nP) [] p.nIdx = .ok isorts ∧
    nativeFieldsOk env p.cvT.name p.cvT.levelParams p.nP p.nIdx ctorsA p.kinds = true ∧
    nativeRulesOk p.cvR.name (p.cvR.levelParams.map .param) .never p.nP p.ctors.length
      ctorsA p.kinds p.rhss p.cvR.type = true ∧
    checkNativeRec (m := ConLeche.CheckM) (fueledOps μ F) (consSumCtors p.nP ctorsA env₁)
      p cvTa ctorsA = .ok (cvRa, rhss) ∧
    -- the projection table at a structure-like block (task #210 Part A)
    checkNativeTable (m := ConLeche.CheckM) p ctorsA sortss
      ⟨.recInfo cvRa p.majorIdx p.rulePrefix
        (sumRules (consSumCtors p.nP ctorsA env₁).find? cvRa.name p.nP p.majorIdx p.rulePrefix cvRa.type ctorsA rhss)
        :: (consSumCtors p.nP ctorsA env₁).consts⟩ = .ok env₂

/-- The install after the pass, inverted: the monad-shape argument,
one `cases` per bind, the guards by cases. -/
theorem checkNativeTail_inv {μ : CheckMode} {F : Nat} {env env₂ : Env}
    {q : NativePass Env}
    (h : checkNativeTail (m := ConLeche.CheckM) (fueledOps μ F) env q = .ok env₂) :
    ∃ (cvRa : ConstantVal) (rhss : List Expr) (tfvs : List Expr) (trest : Expr)
      (isorts : List Level),
      (q.p.large = true → q.p.resSort.isNeverZero = true ∨ q.p.ctors.length < 2) ∧
      openPisAtFvars (q.p.nP + q.p.nIdx) q.cvTa.type 0 = some (tfvs, trest) ∧
      ConLeche.checkStructFieldSortsI (m := ConLeche.CheckM) (fueledOps μ F) q.env₁ true false
        q.p.resSort q.p.nP (tfvs.drop q.p.nP) [] q.p.nIdx = .ok isorts ∧
      nativeFieldsOk env q.p.cvT.name q.p.cvT.levelParams q.p.nP q.p.nIdx q.ctorsA q.p.kinds
        = true ∧
      nativeRulesOk q.p.cvR.name (q.p.cvR.levelParams.map .param) .never q.p.nP
        q.p.ctors.length q.ctorsA q.p.kinds q.p.rhss q.p.cvR.type = true ∧
      checkNativeRec (m := ConLeche.CheckM) (fueledOps μ F) (consSumCtors q.p.nP q.ctorsA q.env₁)
        q.p q.cvTa q.ctorsA = .ok (cvRa, rhss) ∧
      checkNativeTable (m := ConLeche.CheckM) q.p q.ctorsA q.sortss
        ⟨.recInfo cvRa q.p.majorIdx q.p.rulePrefix
          (sumRules (consSumCtors q.p.nP q.ctorsA q.env₁).find? cvRa.name q.p.nP q.p.majorIdx
            q.p.rulePrefix cvRa.type q.ctorsA rhss)
          :: (consSumCtors q.p.nP q.ctorsA q.env₁).consts⟩ = .ok env₂ := by
  rw [checkNativeTail] at h
  simp only [bind, Except.bind] at h
  -- the elimination guard
  by_cases hg : (q.p.large && !q.p.resSort.isNeverZero && decide (2 ≤ q.p.ctors.length)) = true
  · rw [if_pos hg] at h
    exact absurd h (by simp [throw, throwThe, MonadExceptOf.throw])
  rw [if_neg hg] at h
  have helim : q.p.large = true → q.p.resSort.isNeverZero = true ∨ q.p.ctors.length < 2 := by
    intro hl
    cases hz : q.p.resSort.isNeverZero with
    | true => exact Or.inl rfl
    | false =>
      right
      exact Classical.byContradiction fun hge => hg (by simp [hl, hz]; omega)
  try simp only [bind, Except.bind] at h
  cases htq : openPisAtFvars (q.p.nP + q.p.nIdx) q.cvTa.type 0 with
  | none =>
    rw [htq] at h
    exact absurd h (by simp [unwrapOr, throw, throwThe, MonadExceptOf.throw])
  | some tq =>
  obtain ⟨tfvs, trest⟩ := tq
  rw [htq] at h
  simp only [unwrapOr, pure, Except.pure] at h
  cases hsorts : ConLeche.checkStructFieldSortsI (m := ConLeche.CheckM) (fueledOps μ F) q.env₁
      true false q.p.resSort q.p.nP (tfvs.drop q.p.nP) [] q.p.nIdx with
  | error e => rw [hsorts] at h; exact nomatch h
  | ok isorts =>
  rw [hsorts] at h
  dsimp only at h
  by_cases hk : nativeFieldsOk env q.p.cvT.name q.p.cvT.levelParams q.p.nP q.p.nIdx q.ctorsA
      q.p.kinds = true
  case neg =>
    rw [if_neg hk] at h
    exact absurd h (by simp [throw, throwThe, MonadExceptOf.throw])
  rw [if_pos hk] at h
  try simp only [bind, Except.bind] at h
  by_cases hr : nativeRulesOk q.p.cvR.name (q.p.cvR.levelParams.map .param) .never q.p.nP
      q.p.ctors.length q.ctorsA q.p.kinds q.p.rhss q.p.cvR.type = true
  case neg =>
    rw [if_neg hr] at h
    exact absurd h (by simp [throw, throwThe, MonadExceptOf.throw])
  rw [if_pos hr] at h
  try simp only [bind, Except.bind] at h
  cases hRec : checkNativeRec (m := ConLeche.CheckM) (fueledOps μ F)
      (consSumCtors q.p.nP q.ctorsA q.env₁) q.p q.cvTa q.ctorsA with
  | error e => rw [hRec] at h; exact nomatch h
  | ok r₃ =>
  obtain ⟨cvRa, rhss⟩ := r₃
  rw [hRec] at h
  dsimp only at h
  -- `cases … :` rewrote the opening and the recursor's run in the goal
  exact ⟨cvRa, rhss, tfvs, trest, isorts, helim, rfl, hsorts, hk, hr, rfl, h⟩

/-- A settled pass with the install after it is a run. -/
theorem declNativeRun_of_pass {μ : CheckMode} {F : Nat} {env env₂ : Env}
    {p₀ : NativeParts} {isRec : Bool} {q : NativePass Env}
    (hnd : (p₀.ctors.map (·.1.name)).Nodup)
    (hP : checkNativePass (m := ConLeche.CheckM) (fueledOps μ F) env p₀ isRec = .ok (q, true))
    (h : checkNativeTail (m := ConLeche.CheckM) (fueledOps μ F) env q = .ok env₂) :
    DeclNativeRun μ F env p₀ env₂ := by
  obtain ⟨p₁, kinds, hInd, hCtors, hK, hp, hb⟩ := ConLeche.checkNativePass_inv hP
  obtain ⟨cvRa, rhss, tfvs, trest, isorts, helim, htq, hsorts, hk, hr, hRec, hTbl⟩ :=
    checkNativeTail_inv h
  have hcaps : nativeCaps q.p = nativeCapsAt p₁ isRec := beq_iff_eq.mp hb.symm
  refine ⟨hnd, isRec, q.env₁, q.cvTa, p₁, q.p, q.ctorsA, q.sortss, kinds, cvRa, rhss, tfvs, trest,
    isorts, hInd, hp, ?_, ?_, hcaps, helim, htq, hsorts, hk, hr, hRec, hTbl⟩
  · rw [hp]; exact hCtors
  · rw [hp]; exact hK

/-- The bridge inversion: the settled pass — the first, or the second
where the reading overshot — and the install after it. -/
theorem declNativeRun_of {μ : CheckMode} {F : Nat} {env env₂ : Env}
    {p₀ : NativeParts}
    (h : checkNative (m := ConLeche.CheckM) (fueledOps μ F) env p₀ = .ok env₂) :
    DeclNativeRun μ F env p₀ env₂ := by
  rw [checkNative] at h
  simp only [bind, Except.bind] at h
  -- the distinct-names guard
  by_cases hnd : (p₀.ctors.map (·.1.name)).Nodup
  case neg =>
    rw [if_neg hnd] at h
    exact absurd h (by simp [throw, throwThe, MonadExceptOf.throw])
  rw [if_pos hnd] at h
  try simp only [bind, Except.bind] at h
  cases hP : checkNativePass (m := ConLeche.CheckM) (fueledOps μ F) env p₀ (nativeRawRec p₀) with
  | error e => rw [hP] at h; exact nomatch h
  | ok r =>
  obtain ⟨q, settled⟩ := r
  rw [hP] at h
  dsimp only at h
  cases settled with
  | true => exact declNativeRun_of_pass hnd hP (by simpa using h)
  | false =>
  simp only [Bool.false_eq_true, ↓reduceIte] at h
  cases hP₂ : checkNativePass (m := ConLeche.CheckM) (fueledOps μ F) env p₀
      (nativeIsRec q.p.kinds) with
  | error e => rw [hP₂] at h; exact nomatch h
  | ok r₂ =>
  obtain ⟨q', settled'⟩ := r₂
  rw [hP₂] at h
  dsimp only at h
  cases settled' with
  | false =>
    exact absurd h (by simp [throw, throwThe, MonadExceptOf.throw])
  | true => exact declNativeRun_of_pass hnd hP₂ (by simpa using h)

/-! ## The run-level dispatch

`checkDeclRun_ofEnvFactsE`'s `Ind` slot: the direct (fixpoint) arm and
the modeled arm — the kernel's own case split (`nativeParts?`; ONE
ROUTE, task #210 Part B). -/

/-- The `.indDecl` dispatch at the run level (the recogniser alone
since task #219). -/
def DeclIndRunDispatch (μ : CheckMode) (F : Nat) (env : Env)
    (block : List ConstantInfo) (nP : Nat) (env₂ : Env) : Prop :=
  match ConLeche.nativeParts? nP block with
  | some p => DeclNativeRun μ F env p env₂
  | none => DeclIndRun μ F env block env₂

end ConLeche.Semantics
