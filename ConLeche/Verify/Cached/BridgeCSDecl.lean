module

public import ConLeche.Verify.Cached.BridgeCS4
import ConLeche.Verify.Inductives.StructWF
import ConLeche.Verify.Inductives.SumWF
import ConLeche.Verify.Inductives.FixWF
import ConLeche.Verify.Cached.WalkersC

public section

/-!
# Cached shared-state checker: the inductive block and the per-declaration bridge

Port of `ConLeche/Verify/BridgeSDecl.lean` for the cached tier.  The tail
of the per-declaration composition whose bulk is
`ConLeche/Verify/Cached/BridgeCS4.lean`: the inductive-block driver
(`checkIndDeclSF_run`), its dispatch (`checkModeledOrNativeSF_run`), and the
per-declaration bridge (`checkDeclSharedF_bridge`).

As in the interned original the *direct simple-structure* run has no
bridge here: `structsEnabled = false` makes the arm that would
call it unreachable and `structParts?_none` collapses it at one `rw`.

Against `BridgeSDecl` the systematic deletions of the tier carry
through: no arena, hence no `Ext` conjunct anywhere and no
`tierOffE`/tier-flag side condition; `ISOKF` becomes `CSOKF`, whose
`residue` needs no flag witness; the fresh state is `CSOK.empty` rather
than `ISOK.fresh`.  Every pure comparand is byte-identical to the
interned original's.

One piece the interned tier keeps in a *shared* file has to be
replicated here: `checkDeclSF_nonind` (`ConLeche/Verify/CheckerF.lean`)
is stated for `CheckIM`, because the `throw`/`ite` peels it uses are
monad-specific (`rfl` at a concrete `StateT`).  Its `CheckCM` twin —
`checkDeclSFC_nonind`, with the `_push` lemmas it consumes — is proved
below; the pure comparand (`checkDecl` at `sharedOpsC`) is the same
program.  These are the only additions: everything else in the file is
the transposition.
-/

set_option linter.unusedSimpArgs false

namespace ConLeche.Cached

theorem throwC_bind_eq {α β : Type} (e : CheckError)
    (f : α → CheckCM β) : ((throw e : CheckCM α) >>= f) = throw e := rfl


open ConLeche

variable {mode : CheckMode}
variable {pins : List NatOpPinSet}

/-! ## `CheckCM` peels (the `CheckIM` helpers of
`ConLeche/Verify/CheckerF.lean` at the cached monad) -/

theorem bindC_congr {α β : Type} {x : CheckCM α} {f g : α → CheckCM β}
    (h : ∀ a, f a = g a) : x >>= f = x >>= g := by
  rw [funext h]

theorem ite_bindC {α β : Type} (c : Prop) [Decidable c]
    (a b : CheckCM α) (f : α → CheckCM β) :
    ((if c then a else b) >>= f)
      = if c then a >>= f else b >>= f := by
  split <;> rfl

theorem installBasisDeclF_pushC (env : Env) (ci : ConstantInfo) :
    (installBasisDeclF (mkFEnv env) ci : CheckCM FEnv)
      = installBasisDecl env ci >>= fun e => pure (mkFEnv e) := by
  unfold installBasisDeclF installBasisDecl
  simp only [mkFEnv_find?, push_mkFEnv, pure_bind, ite_bindC,
    throwC_bind_eq] <;> rfl

theorem installBasisFoldF_pushC :
    ∀ (l : List ConstantInfo) (env : Env),
      (l.foldlM installBasisDeclF (mkFEnv env) : CheckCM FEnv)
        = l.foldlM installBasisDecl env >>= fun e => pure (mkFEnv e)
  | [], env => by
    simp only [List.foldlM_nil, pure_bind]
  | ci :: l, env => by
    rw [List.foldlM_cons, List.foldlM_cons, installBasisDeclF_pushC,
      bind_assoc, bind_assoc]
    refine bindC_congr fun e => ?_
    rw [pure_bind, installBasisFoldF_pushC l e]

/-! ### The direct simple-structure path's extending stages (task #175
W4c: the cached run bridge restored) -/

/-- The former's telescope stage through the index (task #195): the
whnf loop reads the index's environment, the re-check is the indexed
`checkConstantValF`. -/
theorem checkSumTeleF_pushC (ops : CheckerOps CheckCM) (env : Env)
    (cv : ConstantVal) (n : Nat) (cvTa₀ : ConstantVal) :
    checkSumTeleF ops (mkFEnv env) cv n cvTa₀
      = checkSumTele ops env cv n cvTa₀ := by
  unfold checkSumTeleF checkSumTele
  cases hst : cvTa₀.type.stripPis n with
  | none => simp only [checkConstantValF_eq, mkFEnv_env]
  | some q =>
    obtain ⟨bs, body⟩ := q
    cases body <;> simp only [checkConstantValF_eq, mkFEnv_env]

/-- The direct sum's type-former stage through the index (task #175
sum-types). -/
theorem checkSumIndF_pushC (ops : CheckerOps CheckCM) (env : Env)
    (p : InductiveShape) (capsOf : InductiveShape → IndCaps) :
    checkSumIndF ops (mkFEnv env) p capsOf
      = checkSumInd ops env p capsOf
          >>= fun q => pure (mkFEnv q.1, q.2) := by
  unfold checkSumIndF checkSumInd
  simp only [checkConstantValF_eq, checkSumTeleF_pushC, push_mkFEnv, bind_assoc,
    pure_bind, ite_bindC, throwC_bind_eq] <;> rfl

/-- The projection table through the index (task #175 S1). -/
theorem checkStructProjTableF_pushC (T C : Name) (lps : List Name)
    (nP nF : Nat) (rs : Level) (guards : List Level) (off : Nat) (cvCa : ConstantVal)
    (env : Env) :
    checkStructProjTableF (m := CheckCM) .plain T C lps nP nF rs guards off cvCa (mkFEnv env)
      = checkStructProjTable (m := CheckCM) T C lps nP nF rs guards off cvCa env
          >>= fun e => pure (mkFEnv e) := by
  unfold checkStructProjTableF checkStructProjTable
  simp only [StructWalkers.plain, constsResolveF_eq, mkFEnv_find?, push_mkFEnv, bind_assoc,
    pure_bind, ite_bindC, throwC_bind_eq] <;> rfl

/-! ## `checkModeled` and the final bridge -/

/-! ## The direct simple-structure install (task #82; the cached run
bridge restored at task #175 W4c, the direct install being the only
projection route) -/

/-- The projection-table stage of the cached driver, run-level (task
#175 S1): operation-free, the state is unchanged, the environment is
the pure stage's. -/
theorem checkStructProjTableS_run {T C : Name} {lps : List Name} {nP nF : Nat}
    {rs : Level} {guards : List Level} {off : Nat} {cvCa : ConstantVal}
    (env : Env) {s₀ : CState} {fe' : FEnv} {s' : CState}
    (henv : EnvWF env) (hwf : CSOKF s₀)
    (h : checkStructProjTableF (m := CheckCM) .plain T C lps nP nF rs guards off cvCa
      (mkFEnv env) s₀ = .ok (fe', s')) :
    CSOKF s' ∧ fe' = mkFEnv fe'.env ∧ EnvWF fe'.env ∧
    ∃ F, (checkStructProjTable T C lps nP nF rs guards off cvCa env : FueledM Env).val F
      = .ok fe'.env := by
  rw [checkStructProjTableF_pushC] at h
  obtain ⟨e₁, s₁, hstep, h⟩ := bindC_ok h
  obtain ⟨hfe, rfl⟩ := pureC_ok h
  subst hfe
  -- the pure stage in the cached monad: state unchanged, the value the
  -- `CheckM` instantiation's
  have hrun : s₀ = s₁ ∧ checkStructProjTable (m := CheckM) T C lps nP nF rs guards off cvCa env
      = .ok e₁ := by
    unfold checkStructProjTable at hstep ⊢
    cases hb : structProjBodies T nP nF cvCa.type with
    | none =>
      try rw [hb] at hstep
      exact absurd hstep throwC_bind_ok
    | some bodies =>
      try rw [hb] at hstep
      simp only [unwrapOr, pure_bind] at hstep ⊢
      split at hstep
      · next hg =>
        rw [if_pos hg]
        split at hstep
        · next hfam =>
          rw [if_pos hfam]
          split at hstep
          · next hn =>
            rw [if_pos hn]
            obtain ⟨hfe, rfl⟩ := pureC_ok hstep
            subst hfe
            exact ⟨rfl, rfl⟩
          · exact absurd hstep throwC_bind_ok
        · exact absurd hstep throwC_bind_ok
      · exact absurd hstep throwC_bind_ok
  obtain ⟨rfl, hpure⟩ := hrun
  refine ⟨hwf, rfl, direct_table_wf henv hpure, 0, ?_⟩
  rw [checkStructProjTable_datF]
  exact hpure

/-- The projection-table stage of the fixpoint route at the cached
driver, run-level (task #210 Part A): at a structure-like block the
direct structure's table stage (`checkStructProjTableS_run`), else the
environment unchanged. -/
theorem checkNativeTableS_run {p : NativeParts} {ctorsA : List (ConstantVal × Nat)}
    {sortss : List (List Level)} (env : Env) {s₀ : CState} {fe' : FEnv} {s' : CState}
    (henv : EnvWF env) (hwf : CSOKF s₀)
    (h : checkNativeTableF (m := CheckCM) .plain p ctorsA sortss (mkFEnv env) s₀
      = .ok (fe', s')) :
    CSOKF s' ∧ fe' = mkFEnv fe'.env ∧ EnvWF fe'.env ∧
    ∃ F, (checkNativeTable (m := FueledM) p ctorsA sortss env).val F = .ok fe'.env := by
  match ctorsA, sortss with
  | [cA], [sorts] =>
    simp only [checkNativeTableF] at h
    simp only [checkNativeTable]
    by_cases hi : (p.nIdx == 0) = true
    · rw [if_pos hi] at h
      rw [if_pos hi]
      exact checkStructProjTableS_run env henv hwf h
    · rw [if_neg hi] at h
      rw [if_neg hi]
      obtain ⟨rfl, rfl⟩ := pureC_ok h
      exact ⟨hwf, rfl, henv, 0, rfl⟩
  | [], _ =>
    simp only [checkNativeTableF] at h
    obtain ⟨rfl, rfl⟩ := pureC_ok h
    exact ⟨hwf, rfl, henv, 0, rfl⟩
  | _ :: _ :: _, _ =>
    simp only [checkNativeTableF] at h
    obtain ⟨rfl, rfl⟩ := pureC_ok h
    exact ⟨hwf, rfl, henv, 0, rfl⟩
  | [_], [] =>
    simp only [checkNativeTableF] at h
    obtain ⟨rfl, rfl⟩ := pureC_ok h
    exact ⟨hwf, rfl, henv, 0, rfl⟩
  | [_], _ :: _ :: _ =>
    simp only [checkNativeTableF] at h
    obtain ⟨rfl, rfl⟩ := pureC_ok h
    exact ⟨hwf, rfl, henv, 0, rfl⟩

set_option maxHeartbeats 1600000 in
/-- The kinds' classification is operation-free: in the cached monad it
leaves the state alone and computes what the pure one does (task #210
Part D). -/
theorem classifyFixKindsC_ok {T : Name} {lps : List Name} {nP nIdx : Nat}
    {ctorsA : List (ConstantVal × Nat)} {s₀ s' : CState}
    {kinds : List (List RecFieldKind)}
    (h : classifyFixKinds (m := CheckCM) T lps nP nIdx ctorsA s₀ = .ok (kinds, s')) :
    s' = s₀ ∧ classifyFixKinds (m := CheckM) T lps nP nIdx ctorsA = .ok kinds := by
  unfold classifyFixKinds at h ⊢
  obtain ⟨ks, s₁, hu, h⟩ := bindC_ok h
  cases hk : ctorsA.mapM (recCtorKinds T lps nP nIdx) with
  | none => rw [hk] at hu; exact nomatch hu
  | some ks' =>
  rw [hk] at hu
  simp only [unwrapOr] at hu
  obtain ⟨rfl, rfl⟩ := pureC_ok hu
  simp only [unwrapOr, hk]
  try dsimp only at h
  split at h
  · exact absurd h throwC_bind_ok
  · try dsimp only at h
    split at h
    · exact absurd h throwC_bind_ok
    · obtain ⟨rfl, rfl⟩ := pureC_ok h
      simp only [*, bind, Except.bind, ↓reduceIte, pure, Except.pure]
      exact ⟨trivial, rfl⟩

/-- One pass at the cached driver (task #268) is reproduced by the
pure fueled `checkNativePass`: the former's environment is the index
over the pure one, the memo state is sound at it, and the
constructors' conses onto it are well-formed. -/
theorem checkNativePassS_run (hμ : mode.verifiedChecks = true) {env : Env} (henv : EnvWF env)
    {p₀ : NativeParts} {isRec : Bool} {s₀ : CState} (hs : CSOK mode env s₀)
    {q : NativePass FEnv} {b : Bool} {s' : CState}
    (h : checkNativePassS mode (mkFEnv env) p₀ isRec s₀ = .ok ((q, b), s')) :
    ∃ env₁ : Env, q.env₁ = mkFEnv env₁ ∧ CSOK mode env₁ s' ∧ EnvWF env₁ ∧
      q.cvTa.type.hasFvar = false ∧ EnvWF (consSumCtors q.p.nP q.ctorsA env₁) ∧
      ∃ F, (checkNativePass (fueledOpsM mode) env p₀ isRec).val F
        = .ok (⟨env₁, q.cvTa, q.p, q.ctorsA, q.sortss⟩, b) := by
  unfold checkNativePassS at h
  -- the type former, at the record at the verdict
  rw [checkSumIndF_pushC] at h
  simp only [bind_assoc, pure_bind] at h
  obtain ⟨q1, s₁, hind, h⟩ := bindC_ok h
  obtain ⟨hs₁, q1', hP1, F₁, hF₁⟩ := (checkSumIndS_sim hμ henv hs) q1 s₁ hind
  obtain ⟨rfl, -⟩ := hP1
  obtain ⟨env₁, cvTa, p₁⟩ := q1
  have hF₁p : checkSumInd (fueledOps mode F₁) env p₀.toInductiveShape
      (fun p₁ => nativeCapsAt p₁ isRec) = .ok (env₁, cvTa, p₁) := by
    rw [← checkSumInd_datF]; exact hF₁
  obtain ⟨henv₁, hTf⟩ := direct_sum_ind_wf henv hF₁p (fun q => nativeCapsAt_arity q isRec)
  -- every constructor, at the former's environment, the resolution
  -- guard pointed at that same environment
  try simp only at h
  obtain ⟨uB, sB, hflB, h⟩ := bindC_ok h
  rw [flushC_run] at hflB
  injection hflB with hflB
  obtain rfl : s₁.flushed = sB := congrArg Prod.snd hflB
  rw [checkSumCtorsF_eq] at h
  obtain ⟨q2, s₂, hct, h⟩ := bindC_ok h
  obtain ⟨hs₂, q2', hP2, F₂, hF₂⟩ :=
    (checkSumCtorsS_sim hμ henv₁ hTf (flushC_csok hs₁.residue)) q2 s₂ hct
  obtain rfl : q2 = q2' := hP2
  obtain ⟨ctorsA, sortss⟩ := q2
  have hF₂p : checkSumCtors (fueledOps mode F₂) env₁ env₁ (p₀.complete p₁).cvT.name
      (p₀.complete p₁).cvT.levelParams (p₀.complete p₁).nP (p₀.complete p₁).nIdx
      (p₀.complete p₁).resSort (p₀.complete p₁).isProp (p₀.complete p₁).large cvTa
      (p₀.complete p₁).ctors = .ok (ctorsA, sortss) := by
    rw [← checkSumCtors_datF]; exact hF₂
  -- the kinds, classified on the stored constructors
  try simp only at h
  obtain ⟨kinds, sK, hK, h⟩ := bindC_ok h
  obtain ⟨hsK, hKp⟩ := classifyFixKindsC_ok hK
  obtain ⟨hq, rfl⟩ := pureC_ok h
  simp only [Prod.mk.injEq] at hq
  obtain ⟨rfl, rfl⟩ := hq
  subst hsK
  -- the constructors' conses
  have henv₂ : EnvWF (consSumCtors (p₀.complete p₁).nP ctorsA env₁) := by
    refine envWF_consSumCtors henv₁ ?_
    intro c hc
    obtain ⟨hlen, -, hall⟩ := checkSumCtors_inv hF₂p
    obtain ⟨j, hj⟩ := List.getElem?_of_mem hc
    have hj' : j < (p₀.complete p₁).ctors.length := by
      have := (List.getElem?_eq_some_iff.mp hj).1
      omega
    obtain ⟨-, sorts, -, hrun⟩ := hall j ((p₀.complete p₁).ctors[j]) c
      (List.getElem?_eq_getElem hj') hj
    exact direct_sum_ctor_typeWF hrun
  refine ⟨env₁, rfl, hs₂, henv₁, hTf, henv₂, max F₁ F₂, ?_⟩
  have g₁ : checkSumInd (fueledOps mode (max F₁ F₂)) env p₀.toInductiveShape
      (fun p₁ => nativeCapsAt p₁ isRec) = .ok (env₁, cvTa, p₁) := by
    rw [← checkSumInd_datF]; exact FueledM.up (Nat.le_max_left _ _) hF₁
  have g₂ : checkSumCtors (fueledOps mode (max F₁ F₂)) env₁ env₁ (p₀.complete p₁).cvT.name
      (p₀.complete p₁).cvT.levelParams (p₀.complete p₁).nP (p₀.complete p₁).nIdx
      (p₀.complete p₁).resSort (p₀.complete p₁).isProp (p₀.complete p₁).large cvTa
      (p₀.complete p₁).ctors = .ok (ctorsA, sortss) := by
    rw [← checkSumCtors_datF]; exact FueledM.up (Nat.le_max_right _ _) hF₂
  rw [checkNativePass_datF]
  unfold checkNativePass
  simp only [Bind.bind, Except.bind, pure, Except.pure]
  rw [g₁]
  simp only [Except.bind]
  rw [g₂]
  simp only [Except.bind]
  rw [hKp]

/-- The install after the pass at the cached driver is reproduced by
the pure fueled `checkNativeTail`. -/
theorem checkNativeTailS_run (hμ : mode.verifiedChecks = true) {env env₁ : Env}
    (henv₁ : EnvWF env₁) {cvTa : ConstantVal} {p : NativeParts}
    {ctorsA : List (ConstantVal × Nat)} {sortss : List (List Level)}
    (hTf : cvTa.type.hasFvar = false) (henv₂ : EnvWF (consSumCtors p.nP ctorsA env₁))
    {s₀ : CState} (hs : CSOK mode env₁ s₀) {feOut : FEnv} {s' : CState}
    (h : checkNativeTailS mode (mkFEnv env) ⟨mkFEnv env₁, cvTa, p, ctorsA, sortss⟩ s₀
      = .ok (feOut, s')) :
    CSOKF s' ∧ feOut = mkFEnv feOut.env ∧
    ∃ F, (checkNativeTail (fueledOpsM mode) env ⟨env₁, cvTa, p, ctorsA, sortss⟩).val F
      = .ok feOut.env := by
  unfold checkNativeTailS at h
  rw [structWalkersC_eq_plain] at h
  try simp only at h
  -- the elimination guard on the completed record
  by_cases hg : (p.large && !p.resSort.isNeverZero && decide (2 ≤ p.ctors.length)) = true
  · rw [if_pos hg] at h; exact absurd h throwC_bind_ok
  rw [if_neg hg] at h
  -- the index binders' sorts, read
  cases htq : openPisAtFvars (p.nP + p.nIdx) cvTa.type 0 with
  | none => rw [htq] at h; exact absurd h throwC_bind_ok
  | some tq =>
  rw [htq] at h
  simp only [unwrapOr, pure_bind] at h
  rw [checkStructFieldSortsIF_eq] at h
  obtain ⟨isorts, sS, hsorts, h⟩ := bindC_ok h
  have hTw : Expr.WScoped 0 cvTa.type := Expr.WScoped.of_not_hasFvar hTf
  obtain ⟨htqW, -⟩ := openPisAtFvars_WScoped _ _ _ htq hTw
  have hidxT := openPisAtFvars_index _ _ _ htq
  have hxPos : ∀ (i : Nat) (x : Expr), (tq.1.drop p.nP)[i]? = some x →
      Expr.WScoped (p.nP + i) (Expr.fvarTypeD x) := by
    intro i x hx
    rw [List.getElem?_drop] at hx
    obtain ⟨ty, rfl⟩ := hidxT (p.nP + i) x hx
    have hw := htqW _ (List.mem_of_getElem? hx)
    simp only [Expr.WScoped, Nat.zero_add] at hw
    exact hw.2
  obtain ⟨hsS, isorts', hPs, F₀, hF₀⟩ :=
    (checkStructFieldSortsIS_sim hμ henv₁ hxPos hs) isorts sS hsorts
  obtain rfl : isorts = isorts' := hPs
  -- the field kinds, re-checked
  try simp only at h
  rw [nativeFieldsOkF_eq] at h
  by_cases hk : nativeFieldsOk env p.cvT.name p.cvT.levelParams p.nP p.nIdx ctorsA
      p.kinds = true
  case neg => rw [if_neg hk] at h; exact absurd h throwC_bind_ok
  rw [if_pos hk] at h
  -- the stream's rules against the generated ones
  by_cases hr : nativeRulesOk p.cvR.name (p.cvR.levelParams.map .param) .never p.nP
      p.ctors.length ctorsA p.kinds p.rhss p.cvR.type = true
  case neg => rw [if_neg hr] at h; exact absurd h throwC_bind_ok
  rw [if_pos hr] at h
  rw [consSumCtorsF_mkFEnv] at h
  -- the recursor with the inductive hypotheses, generated and compared
  obtain ⟨u2, sC, hfl2, h⟩ := bindC_ok h
  rw [flushC_run] at hfl2
  injection hfl2 with hfl2
  obtain rfl : sS.flushed = sC := congrArg Prod.snd hfl2
  rw [checkNativeRecF_eq] at h
  obtain ⟨q3, s₃, hrc, h⟩ := bindC_ok h
  obtain ⟨hs₃, q3', hP3, F₃, hF₃⟩ :=
    (checkNativeRecS_sim hμ henv₂ (flushC_csok hsS.residue)) q3 s₃ hrc
  obtain rfl : q3 = q3' := hP3
  obtain ⟨cvRa, rhss⟩ := q3
  have hF₃p : checkNativeRec (fueledOps mode F₃) (consSumCtors p.nP ctorsA env₁)
      p cvTa ctorsA = .ok (cvRa, rhss) := by
    rw [← checkNativeRec_datF]; exact hF₃
  have henv₃ := direct_fix_rec_wf henv₂ hF₃p
  -- the projection table at a structure-like block (task #210 Part A)
  rw [push_mkFEnv, show FEnv.find? (mkFEnv (consSumCtors p.nP ctorsA env₁))
    = (consSumCtors p.nP ctorsA env₁).find? from
    mkFEnv_find?_fun _] at h
  obtain ⟨hwfO, hfeO, -, F₆, hF₆⟩ := checkNativeTableS_run _ henv₃ hs₃.residue h
  obtain ⟨G, hle₀, hle₃, hle₆⟩ : ∃ G, F₀ ≤ G ∧ F₃ ≤ G ∧ F₆ ≤ G :=
    ⟨max F₀ (max F₃ F₆), by omega, by omega, by omega⟩
  refine ⟨hwfO, hfeO, G, ?_⟩
  have g₀ : checkStructFieldSortsI (fueledOps mode G) env₁ true false p.resSort p.nP
      (tq.1.drop p.nP) [] p.nIdx = .ok isorts := by
    rw [← checkStructFieldSortsI_datF]; exact FueledM.up hle₀ hF₀
  have g₃ : checkNativeRec (fueledOps mode G) (consSumCtors p.nP ctorsA env₁)
      p cvTa ctorsA = .ok (cvRa, rhss) := by
    rw [← checkNativeRec_datF]; exact FueledM.up hle₃ hF₃
  have g₆ : checkNativeTable (m := CheckM) p ctorsA sortss
      ⟨.recInfo cvRa p.majorIdx p.rulePrefix
        (sumRules (consSumCtors p.nP ctorsA env₁).find? cvRa.name p.nP p.majorIdx p.rulePrefix cvRa.type ctorsA rhss)
        :: (consSumCtors p.nP ctorsA env₁).consts⟩ = .ok feOut.env := by
    rw [← checkNativeTable_datF]; exact FueledM.up hle₆ hF₆
  rw [checkNativeTail_datF]
  unfold checkNativeTail
  simp only [Bind.bind, Except.bind, pure, Except.pure]
  rw [if_neg hg]
  try simp only [Bind.bind, Except.bind, pure, Except.pure]
  rw [htq]
  simp only [unwrapOr, pure, Except.pure, Except.bind]
  rw [g₀]
  simp only [Except.bind]
  rw [if_pos hk, if_pos hr]
  rw [g₃]
  simp only [Except.bind]
  exact g₆

/-- The direct recursive install at the cached driver is reproduced by
the pure fueled `checkNative` (task #188): the pass at the syntactic
reading, again at the classified verdict where it overshot (task
#268), and the install after the settled one. -/
theorem checkNativeS_run (hμ : mode.verifiedChecks = true) {env : Env} (henv : EnvWF env)
    {p₀ : NativeParts} {s₀ : CState} (hwf : CSOKF s₀)
    {feOut : FEnv} {s' : CState}
    (h : checkNativeS mode (mkFEnv env) p₀ s₀ = .ok (feOut, s')) :
    CSOKF s' ∧ feOut = mkFEnv feOut.env ∧
    ∃ F, checkNative (fueledOps mode F) env p₀ = .ok feOut.env := by
  unfold checkNativeS at h
  -- the front guard
  by_cases hnd : (p₀.ctors.map (·.1.name)).Nodup
  case neg => rw [if_neg hnd] at h; exact absurd h throwC_bind_ok
  rw [if_pos hnd] at h
  obtain ⟨u0, sA, hfl0, h⟩ := bindC_ok h
  rw [flushC_run] at hfl0
  injection hfl0 with hfl0
  obtain rfl : s₀.flushed = sA := congrArg Prod.snd hfl0
  -- the pass at the syntactic reading
  obtain ⟨r, s₁, hP, h⟩ := bindC_ok h
  obtain ⟨⟨fe₁, cvTa, p, ctorsA, sortss⟩, settled⟩ := r
  obtain ⟨env₁, hq₁, hs₁, henv₁, hTf, henv₂, F₁, hF₁⟩ :=
    checkNativePassS_run hμ henv (flushC_csok hwf) hP
  simp only at hq₁ hs₁ henv₁ hTf henv₂ hF₁
  subst hq₁
  try simp only at h
  cases settled with
  | true =>
    simp only [↓reduceIte] at h
    obtain ⟨hwfO, hfeO, F₂, hF₂⟩ := checkNativeTailS_run hμ henv₁ hTf henv₂ hs₁ h
    refine ⟨hwfO, hfeO, max F₁ F₂, ?_⟩
    have g₁ : checkNativePass (fueledOps mode (max F₁ F₂)) env p₀ (nativeRawRec p₀)
        = .ok (⟨env₁, cvTa, p, ctorsA, sortss⟩, true) := by
      rw [← checkNativePass_datF]; exact FueledM.up (Nat.le_max_left _ _) hF₁
    have g₂ : checkNativeTail (fueledOps mode (max F₁ F₂)) env ⟨env₁, cvTa, p, ctorsA, sortss⟩
        = .ok feOut.env := by
      rw [← checkNativeTail_datF]; exact FueledM.up (Nat.le_max_right _ _) hF₂
    unfold checkNative
    rw [if_pos hnd]
    simp only [Bind.bind, Except.bind, pure, Except.pure]
    rw [g₁]
    simp only [Except.bind, ↓reduceIte]
    exact g₂
  | false =>
  simp only [Bool.false_eq_true, ↓reduceIte] at h
  -- the pass again, at the classified verdict
  obtain ⟨u1, sB, hfl1, h⟩ := bindC_ok h
  rw [flushC_run] at hfl1
  injection hfl1 with hfl1
  obtain rfl : s₁.flushed = sB := congrArg Prod.snd hfl1
  obtain ⟨r', s₂, hP', h⟩ := bindC_ok h
  obtain ⟨⟨fe₁', cvTa', p', ctorsA', sortss'⟩, settled'⟩ := r'
  obtain ⟨env₁', hq₁', hs₁', henv₁', hTf', henv₂', F₂, hF₂⟩ :=
    checkNativePassS_run hμ henv (flushC_csok hs₁.residue) hP'
  simp only at hq₁' hs₁' henv₁' hTf' henv₂' hF₂
  subst hq₁'
  try simp only at h
  cases settled' with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h
    exact absurd h throwC_bind_ok
  | true =>
  simp only [↓reduceIte] at h
  obtain ⟨hwfO, hfeO, F₃, hF₃⟩ := checkNativeTailS_run hμ henv₁' hTf' henv₂' hs₁' h
  obtain ⟨G, hle₁, hle₂, hle₃⟩ : ∃ G, F₁ ≤ G ∧ F₂ ≤ G ∧ F₃ ≤ G :=
    ⟨max F₁ (max F₂ F₃), by omega, by omega, by omega⟩
  refine ⟨hwfO, hfeO, G, ?_⟩
  have g₁ : checkNativePass (fueledOps mode G) env p₀ (nativeRawRec p₀)
      = .ok (⟨env₁, cvTa, p, ctorsA, sortss⟩, false) := by
    rw [← checkNativePass_datF]; exact FueledM.up hle₁ hF₁
  have g₂ : checkNativePass (fueledOps mode G) env p₀ (nativeIsRec p.kinds)
      = .ok (⟨env₁', cvTa', p', ctorsA', sortss'⟩, true) := by
    rw [← checkNativePass_datF]; exact FueledM.up hle₂ hF₂
  have g₃ : checkNativeTail (fueledOps mode G) env ⟨env₁', cvTa', p', ctorsA', sortss'⟩
      = .ok feOut.env := by
    rw [← checkNativeTail_datF]; exact FueledM.up hle₃ hF₃
  unfold checkNative
  rw [if_pos hnd]
  simp only [Bind.bind, Except.bind, pure, Except.pure]
  rw [g₁]
  simp only [Except.bind, Bool.false_eq_true, ↓reduceIte]
  rw [g₂]
  simp only [Except.bind, ↓reduceIte]
  exact g₃

/-- The inductive block at the cached driver is reproduced by the
pure fueled `checkModeled`. -/
theorem checkIndDeclSF_run (hμ : mode.verifiedChecks = true) {env : Env} (henv : EnvWF env)
    {block : List ConstantInfo} {s₀ : CState} (hwf : CSOKF s₀)
    {feOut : FEnv} {s' : CState}
    (h : checkIndDeclSF mode (mkFEnv env) block s₀ = .ok (feOut, s')) :
    CSOKF s' ∧ feOut = mkFEnv feOut.env ∧
    ∃ F, checkModeled mode (fueledOps mode F) env block = .ok feOut.env := by
  unfold checkIndDeclSF at h
  have hbnAll : ∀ ci ∈ block.filter (fun ci => match ci with
      | .recInfo _ _ _ _ => true | _ => false),
      (block.map (·.name)).contains ci.name = true := by
    intro ci hci
    have : ci.name ∈ block.map (·.name) :=
      List.mem_map_of_mem (List.mem_filter.mp hci).1
    simpa using this
  split at h
  case isFalse hsplit =>
    exact absurd h throwC_bind_ok
  case isTrue hsplit =>
  split at h
  case _ cvT c0 cvC nP nF heq1 heq2 =>
    obtain ⟨caps, s₁, hcaps, h⟩ := bindC_ok h
    obtain ⟨hcapsv, rfl⟩ := pureC_ok hcaps
    have hcapsv' : indBlockCaps mode env cvT cvC nP nF = caps := by
      rw [← indBlockCapsF_eq]; exact hcapsv
    obtain ⟨fe₂, s₂, hfold, h⟩ := bindC_ok h
    -- the block's capability pins at its (single) inductive member:
    -- the member IS the former the record was computed for
    obtain ⟨hwf₂, hfe₂, henv₂, F₁, hF₁⟩ :=
      foldIndMemberS_run hμ _ env henv hwf (by
        intro ci hci cv caps₀ hceq
        have hmemI : ci ∈ [ConstantInfo.indInfo cvT c0] := by
          rw [← heq1]
          exact List.mem_filter.mpr ⟨(List.mem_filter.mp hci).1, by subst hceq; rfl⟩
        obtain ⟨rfl, -⟩ := ConstantInfo.indInfo.inj
          (hceq ▸ List.mem_singleton.mp hmemI)
        rw [← hcapsv']
        exact ConLeche.etaPins_of_indBlockCaps) hfold
    obtain ⟨fe₃, s₃, hrecs, h⟩ := bindC_ok h
    rw [hfe₂] at hrecs
    obtain ⟨hwf₃, hfe₃, henv₃, F₂, hF₂⟩ :=
      checkIndRecsS_run hμ henv₂ hbnAll hwf₂ hrecs
    rw [hfe₃] at h
    simp only [mkFEnv_find?] at h
    rw [ctorResidualOkF_eq] at h
    by_cases hctorRes : ctorResidualOk mode fe₃.env cvT.name cvC.name
        cvT.levelParams nP nF caps.eta = true
    case neg =>
      rw [if_neg hctorRes] at h
      exact absurd h throwC_bind_ok
    rw [if_pos hctorRes] at h
    by_cases hguard : (List.range nF).all
        (fun j => (fe₃.env.find? (projFnName cvT.name j)).isNone) = true
    case neg =>
      rw [if_neg hguard] at h
      exact absurd h throwC_bind_ok
    rw [if_pos hguard] at h
    -- the projection phase: structure-like blocks only (task #175
    -- SigmaHom); off the shape the phase is the identity
    by_cases hsl : ctorTargetsFam cvC.type cvT.name cvT.levelParams nP nF
        = true
    case neg =>
      rw [if_neg hsl] at h
      obtain ⟨hfe₄, rfl⟩ := pureC_ok h
      subst hfe₄
      refine ⟨hwf₃, rfl, max F₁ F₂, ?_⟩
      have hF₁p := FueledM.up (Nat.le_max_left F₁ F₂) hF₁
      rw [foldlM_atF] at hF₁p
      simp only [checkIndMember_datF] at hF₁p
      have hF₂p := FueledM.up (Nat.le_max_right F₁ F₂) hF₂
      rw [checkIndRecs_datF] at hF₂p
      have hF₁p' : List.foldlM (checkIndMember (fueledOps mode (max F₁ F₂))
          (block.map (·.name)) caps) env _ = .ok fe₂.env := hF₁p
      simp only [checkModeled]
      split
      case isFalse hgs => exact absurd hsplit hgs
      case isTrue hgs =>
      split
      next cvT' c0' cvC' nP' nF' heq1' heq2' =>
        have h12 : ([(.indInfo cvT c0 : ConstantInfo)]) =
            [(.indInfo cvT' c0' : ConstantInfo)] :=
          heq1.symm.trans heq1'
        have h34 : ([(.ctorInfo cvC nP nF : ConstantInfo)]) =
            [(.ctorInfo cvC' nP' nF' : ConstantInfo)] :=
          heq2.symm.trans heq2'
        simp only [List.cons.injEq, and_true,
          ConstantInfo.indInfo.injEq, ConstantInfo.ctorInfo.injEq]
          at h12 h34
        obtain ⟨rfl, rfl⟩ := h12
        obtain ⟨rfl, rfl, rfl⟩ := h34
        simp only [Bind.bind, Except.bind, pure, Except.pure]
        rw [hcapsv']
        split
        next err herr => exact nomatch (hF₁p'.symm.trans herr)
        next v hok =>
        obtain rfl : fe₂.env = v := by
          have hv : (Except.ok fe₂.env : Except CheckError Env) = .ok v :=
            hF₁p'.symm.trans hok
          injection hv
        split
        next err herr => exact nomatch (hF₂p.symm.trans herr)
        next v hok =>
        obtain rfl : fe₃.env = v := by
          have hv : (Except.ok fe₃.env : Except CheckError Env) = .ok v :=
            hF₂p.symm.trans hok
          injection hv
        rw [if_pos hctorRes, if_pos hguard, if_neg hsl]
        rfl
      next x1 x2 hne' =>
        exact (hne' cvT c0 cvC nP nF heq1 heq2).elim
    rw [if_pos hsl] at h
    obtain ⟨hwf₄, hfe₄, henv₄, F₃, hF₃⟩ :=
      foldProjFnS_run hμ _ fe₃.env henv₃ hwf₃ h
    refine ⟨hwf₄, hfe₄, max F₁ (max F₂ F₃), ?_⟩
    have hF₁p := FueledM.up (Nat.le_max_left F₁ (max F₂ F₃)) hF₁
    rw [foldlM_atF] at hF₁p
    simp only [checkIndMember_datF] at hF₁p
    have hF₂p := FueledM.up (Nat.le_trans (Nat.le_max_left F₂ F₃)
      (Nat.le_max_right F₁ (max F₂ F₃))) hF₂
    rw [checkIndRecs_datF] at hF₂p
    have hF₃p := FueledM.up (Nat.le_trans (Nat.le_max_right F₂ F₃)
      (Nat.le_max_right F₁ (max F₂ F₃))) hF₃
    rw [foldlM_atF] at hF₃p
    simp only [installProjFnStep_datF] at hF₃p
    have hF₁p' : List.foldlM (checkIndMember
        (fueledOps mode (max F₁ (max F₂ F₃)))
        (block.map (·.name)) caps) env _ = .ok fe₂.env := hF₁p
    have hF₃p' : List.foldlM (installProjFnStep mode
        (fueledOps mode (max F₁ (max F₂ F₃)))
        cvT.name cvC.name cvT.levelParams nP nF) fe₃.env _ =
        .ok feOut.env := hF₃p
    simp only [checkModeled]
    split
    case isFalse hgs => exact absurd hsplit hgs
    case isTrue hgs =>
    split
    next cvT' c0' cvC' nP' nF' heq1' heq2' =>
      have h12 : ([(.indInfo cvT c0 : ConstantInfo)]) =
          [(.indInfo cvT' c0' : ConstantInfo)] :=
        heq1.symm.trans heq1'
      have h34 : ([(.ctorInfo cvC nP nF : ConstantInfo)]) =
          [(.ctorInfo cvC' nP' nF' : ConstantInfo)] :=
        heq2.symm.trans heq2'
      simp only [List.cons.injEq, and_true,
        ConstantInfo.indInfo.injEq, ConstantInfo.ctorInfo.injEq]
        at h12 h34
      obtain ⟨rfl, rfl⟩ := h12
      obtain ⟨rfl, rfl, rfl⟩ := h34
      simp only [Bind.bind, Except.bind, pure, Except.pure]
      rw [hcapsv']
      split
      next err herr => exact nomatch (hF₁p'.symm.trans herr)
      next v hok =>
      obtain rfl : fe₂.env = v := by
        have hv : (Except.ok fe₂.env : Except CheckError Env) = .ok v :=
          hF₁p'.symm.trans hok
        injection hv
      split
      next err herr => exact nomatch (hF₂p.symm.trans herr)
      next v hok =>
      obtain rfl : fe₃.env = v := by
        have hv : (Except.ok fe₃.env : Except CheckError Env) = .ok v :=
          hF₂p.symm.trans hok
        injection hv
      rw [if_pos hctorRes, if_pos hguard, if_pos hsl]
      exact hF₃p'
    next x1 x2 hne' =>
      exact (hne' cvT c0 cvC nP nF heq1 heq2).elim
  case _ =>
    rename_i x1 x2 hne
    obtain ⟨fe₂, s₂, hfold, h⟩ := bindC_ok h
    obtain ⟨hwf₂, hfe₂, henv₂, F₁, hF₁⟩ :=
      foldIndMemberS_run hμ _ env henv hwf
        (fun _ _ _ _ _ => ⟨(fun h => absurd h (by decide)), (fun h => absurd h (by decide))⟩) hfold
    rw [hfe₂] at h
    obtain ⟨hwf₃, hfe₃, henv₃, F₂, hF₂⟩ :=
      checkIndRecsS_run hμ henv₂ hbnAll hwf₂ h
    refine ⟨hwf₃, hfe₃, max F₁ F₂, ?_⟩
    have hF₁p := FueledM.up (Nat.le_max_left F₁ F₂) hF₁
    rw [foldlM_atF] at hF₁p
    simp only [checkIndMember_datF] at hF₁p
    have hF₂p := FueledM.up (Nat.le_max_right F₁ F₂) hF₂
    rw [checkIndRecs_datF] at hF₂p
    have hF₁p' : List.foldlM (checkIndMember (fueledOps mode (max F₁ F₂))
        (block.map (·.name)) {}) env _ = .ok fe₂.env := hF₁p
    simp only [checkModeled]
    split
    case isFalse hgs => exact absurd hsplit hgs
    case isTrue hgs =>
    split
    next cvT' c0' cvC' nP' nF' heq1' heq2' =>
      exact (hne cvT' c0' cvC' nP' nF' heq1' heq2').elim
    next y1 y2 hne' =>
      simp only [Bind.bind, Except.bind, pure, Except.pure]
      split
      next err herr => exact nomatch (hF₁p'.symm.trans herr)
      next v hok =>
      obtain rfl : fe₂.env = v := by
        have hv : (Except.ok fe₂.env : Except CheckError Env) = .ok v :=
          hF₁p'.symm.trans hok
        injection hv
      exact hF₂p

/-- The inductive-block dispatch of the cached driver: a RECOGNISED
block goes to `checkNativeS`, everything else to `checkIndDeclSF`,
and either way the pure fueled `checkDecl` reproduces the run. -/
theorem checkModeledOrNativeSF_run (hμ : mode.verifiedChecks = true) {env : Env} (henv : EnvWF env)
    {block : List ConstantInfo} {nP : Nat} (hpin : basisPinHit block = none)
    (hok : indParamsOk nP block = true)
    {s₀ : CState} (hwf : CSOKF s₀)
    {feOut : FEnv} {s' : CState}
    (h : (match nativeParts? nP block with
          | some p => checkNativeS mode (mkFEnv env) p
          | none => checkIndDeclSF mode (mkFEnv env) block) s₀ =
      .ok (feOut, s')) :
    CSOKF s' ∧ feOut = mkFEnv feOut.env ∧
    ∃ F, checkDecl mode (fueledOps mode F) pins env (.indDecl block nP) =
      .ok feOut.env := by
  -- the declared parameter count (task #228) is a pure guard shared by
  -- the two drivers: `hok` is the branch both take
  show CSOKF s' ∧ feOut = mkFEnv feOut.env ∧
    ∃ F, (match basisPinHit block with
      | some kind => checkBasisDecl (m := CheckM) env kind
      | none =>
        if indParamsOk nP block = true then
          (match nativeParts? nP block with
            | some p => checkNative (fueledOps mode F) env p
            | none => checkModeled mode (fueledOps mode F) env block)
        else throw (CheckError.invalid "number of parameters mismatch")) = .ok feOut.env
  -- task #293: this block is not one of the five pinned ones (the
  -- recognition happened before the dispatch, on both sides)
  simp only [hpin, if_pos hok]
  cases hfp : nativeParts? nP block with
  | some p =>
    rw [hfp] at h
    obtain ⟨hres, hfe, F, hF⟩ := checkNativeS_run hμ henv hwf h
    exact ⟨hres, hfe, F, hF⟩
  | none =>
    rw [hfp] at h
    obtain ⟨hres, hfe, F, hF⟩ := checkIndDeclSF_run hμ henv hwf h
    exact ⟨hres, hfe, F, hF⟩

end ConLeche.Cached
