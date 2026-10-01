module

public import ConLeche.Verify.Cached.BridgeCS3
public import ConLeche.Verify.CheckerF
import ConLeche.Verify.Extend.Inversions
import ConLeche.Verify.Extend.Modeled
public import ConLeche.Verify.Extend.Recs
import ConLeche.Verify.Extend.Proj

public section

/-!
# Cached shared-state checker: the per-declaration composition

Port of `ConLeche/Verify/BridgeS4.lean` for the cached tier.  Composes
the single-environment walks (`ConLeche/Verify/Cached/BridgeCS*.lean`)
along the thin phase drivers of `ConLeche/Cached/CheckerC.lean` into the
per-declaration bridge: a successful `checkDeclSF` run over a
well-formed environment is reproduced by the pure fueled checker.

The environment changes between phases; the state fact threaded across
a transition is the environment-free residue `CSOKF` — each phase
starts with `flushC`, which re-establishes `CSOK` for the phase's
environment (`flushC_csok`).  The `EnvWF` facts for the intermediate
environments are derived from the pure runs exactly as the interned
original does (the small `ConstWF` derivations are replicated here; the
heavy machinery — inversions, `ProvFacts`, `RulesChain` — is the same
public kit, and is `Expr`-level).

Against `BridgeS4` the systematic deletions of the tier carry through:
there is no arena, hence no `Ext` conjunct in any run-level statement,
no `tierOffE` transport and no tier-flag side condition; `ISOKF`
becomes `CSOKF`, whose `residue` needs no flag witness.  Every pure
comparand — the `(fueledOpsM mode)` runs, the `_datF` conversions, the
`EnvWF` conclusions — is byte-identical to the interned original's.
-/

namespace ConLeche.Cached

open ConLeche
open Expr

variable {mode : CheckMode}

/-! ## Run-level toolkit -/

/-- Dissect a successful `CheckCM` bind. -/
theorem bindC_ok {α β : Type} {x : CheckCM α} {k : α → CheckCM β}
    {s₀ : CState} {v : β} {s' : CState}
    (h : (x >>= k) s₀ = .ok (v, s')) :
    ∃ a s₁, x s₀ = .ok (a, s₁) ∧ k a s₁ = .ok (v, s') := by
  simp only [Bind.bind, StateT.bind] at h
  cases hx : x s₀ with
  | error e => rw [hx] at h; exact nomatch h
  | ok pr =>
    obtain ⟨a, s₁⟩ := pr
    rw [hx] at h
    exact ⟨a, s₁, rfl, h⟩

theorem pureC_ok {α : Type} {a : α} {s₀ : CState} {v : α} {s' : CState}
    (h : (pure a : CheckCM α) s₀ = .ok (v, s')) : a = v ∧ s₀ = s' := by
  simp only [pure, StateT.pure, Except.pure, Except.ok.injEq,
    Prod.mk.injEq] at h
  exact h

/-- Compose fueled runs at the joined fuel. -/
theorem atF_bind_intro {α β : Type} {x : FueledM α} {g : α → FueledM β}
    {F₁ F₂ : Nat} {a : α} {v : β} (hx : x.val F₁ = .ok a)
    (hg : (g a).val F₂ = .ok v) :
    (x >>= g).val (max F₁ F₂) = .ok v := by
  rw [FueledM.atF_bind, x.property (Nat.le_max_left F₁ F₂) hx]
  simp only [Bind.bind, Except.bind]
  exact (g a).property (Nat.le_max_right F₁ F₂) hg

/-- Upgrade a fueled run (subject inferred from the hypothesis). -/
theorem FueledM.up {α : Type} {x : FueledM α} {F F' : Nat} {v : α}
    (hle : F ≤ F') (h : x.val F = .ok v) : x.val F' = .ok v :=
  x.property hle h

/-! ## `ConstWF` derivations (replicated from `BridgeWF`'s private
helpers, over the public inversions) -/

/-- Introduction for `ConstWF` with the clause types spelled out. -/
private theorem constWF_intro' {env : Env} {c : ConstantInfo}
    (h1 : c.toConstantVal.type.hasFvar = false)
    (h2 : c.toConstantVal.type.allLevelParamsDefined
      c.toConstantVal.levelParams = true)
    (h3 : c.toConstantVal.type.constsResolve env = true)
    (h4 : c.toConstantVal.type.looseBVarsBounded 0 = true)
    (h5 : ∀ cv value hint, c = .defnInfo cv value hint →
      value.hasFvar = false ∧
      value.allLevelParamsDefined cv.levelParams = true ∧
      value.constsResolve env = true ∧
      value.looseBVarsBounded 0 = true)
    (h6 : ∀ cv mI rP rules, c = .recInfo cv mI rP rules →
      ∀ r, r ∈ rules →
        (RecRule.rhs r).hasFvar = false ∧
        (RecRule.rhs r).allLevelParamsDefined cv.levelParams = true ∧
        (RecRule.rhs r).constsResolve env = true ∧
        (RecRule.rhs r).looseBVarsBounded 0 = true ∧
        ∀ lvls pins, RecRule.fire r = .nested lvls pins →
          rP ≤ mI ∧
          (∀ l ∈ lvls, l.allParamsDefined cv.levelParams = true) ∧
          (∀ pin ∈ pins, pin.hasFvar = false ∧
            pin.allLevelParamsDefined cv.levelParams = true ∧
            pin.constsResolve env = true ∧
            pin.looseBVarsBounded rP = true) ∧
          ∃ pre dom body bm D,
            cv.type.stripPis mI = some (pre, .forallE dom body bm) ∧
            dom.getAppFn = .const D lvls ∧
            dom.getAppArgs =
              pins.map (Expr.liftLooseBVars (mI - rP) 0) ++
                (List.range (mI - rP)).map
                  (fun i => Expr.bvar (mI - rP - 1 - i)))
    (h8 : ∀ tbl, c = .projInfo tbl →
      tbl.bodies.size = tbl.numFields ∧
      ∀ (i : Nat) (b : Expr), tbl.bodies[i]? = some b →
        b.hasFvar = false ∧
        b.allLevelParamsDefined tbl.levelParams = true ∧
        b.constsResolve env = true ∧
        b.looseBVarsBounded (tbl.numParams + 1) = true := by
        intro tbl h
        exact ConstantInfo.noConfusion h)
    (h9 : IndCapsWF c := by
        intro cv caps h
        exact ConstantInfo.noConfusion h) :
    ConstWF env c := ⟨h1, h2, h3, h4, h5, h6, h8, h9⟩

/-- The four `ConstWF` type-slot facts of a checked constant. -/
private theorem cvA_type_facts' {env : Env} {cv cvA : ConstantVal}
    {F : Nat}
    (h : checkConstantVal (fueledOps mode F) env cv = .ok cvA) :
    cvA.type.hasFvar = false ∧
    cvA.type.allLevelParamsDefined cvA.levelParams = true ∧
    cvA.type.constsResolve env = true ∧
    cvA.type.looseBVarsBounded 0 = true := by
  obtain ⟨hfind, hres, hshape, hnd, hlbt, hitf, type, stype, u, hann, htp,
    htr, hst, hsort, rfl⟩ := checkConstantVal_inv h
  refine ⟨?_, htp, htr, annotateCore_looseBVars F cv.type hann hlbt⟩
  exact not_hasFvar_of_fvarsBelow_zero
    ((annotateCore_WScoped F cv.type hann
      (WScoped.of_not_hasFvar hitf)).fvarsBelow)

/-- The provisioned (rule-less) recursor cons is well-formed. -/
private theorem envWF_cons_provRec {env : Env} (henv : EnvWF env)
    {cvA : ConstantVal} {mI rP F : Nat} {cv : ConstantVal}
    (hccv : checkConstantVal (fueledOps mode F) env cv = .ok cvA) :
    EnvWF ⟨.recInfo cvA mI rP [] :: env.consts⟩ := by
  obtain ⟨htf, htp, htr, htb⟩ := cvA_type_facts' hccv
  exact EnvWF.cons henv (constWF_intro' htf htp
    (Expr.constsResolve_mono htr) htb
    (fun _ _ _ heq => nomatch heq)
    (fun cvR mI' rP' rules' heq r hr => by
      injection heq with h1 h2 h3 h4
      subst h4
      exact nomatch hr))

/-! ## The member fold -/

/-- One member step of the shared driver, run-level: the state's arena
stays canonical, the index invariant is maintained, the output
environment is well-formed, and the step is reproduced by the fueled
generic step. -/
theorem checkIndMemberS_run (hμ : mode.verifiedChecks = true) {blockNames : List Name} {caps : IndCaps}
    {env : Env} (henv : EnvWF env) {ci : ConstantInfo} {fe' : FEnv}
    {s₀ s' : CState} (hwf : CSOKF s₀)
    -- the block's capability pins at an inductive member (its stored
    -- type is the model's under the block renaming: `indCapsWF_of_pins`)
    (hpins : ∀ cv caps₀, ci = .indInfo cv caps₀ →
      EtaPins mode env cv.name cv.levelParams caps)
    (h : checkIndMemberS mode blockNames caps (mkFEnv env) ci s₀ =
      .ok (fe', s')) :
    CSOKF s' ∧ fe' = mkFEnv fe'.env ∧
    EnvWF fe'.env ∧
    ∃ F, (checkIndMember (fueledOpsM mode) blockNames caps env ci).val F =
      .ok fe'.env := by
  unfold checkIndMemberS at h
  simp only [checkMemberValF_eq] at h
  obtain ⟨u, s₁, hflush, h⟩ := bindC_ok h
  rw [flushC_run] at hflush
  injection hflush with hflush
  obtain ⟨rfl, rfl⟩ : u = () ∧ s₀.flushed = s₁ :=
    ⟨rfl, congrArg Prod.snd hflush⟩
  obtain ⟨cvA, s₂, hcm, h⟩ := bindC_ok h
  obtain ⟨hs₂, cvA', ⟨rfl, hwty⟩, F₁, hFm⟩ :=
    (checkMemberValS_sim hμ henv (flushC_csok hwf)) cvA s₂ hcm
  have hFmp : checkMemberVal (fueledOps mode F₁) blockNames env
      ci.toConstantVal = .ok cvA := by
    rw [← checkMemberVal_datF]; exact hFm
  obtain ⟨hccv, -, cvm, mval, hint, hfm, -, hty⟩ := checkMemberVal_inv hFmp
  obtain ⟨htf, htp, htr, htb⟩ := cvA_type_facts' hccv
  cases ci with
  | indInfo cv caps0 =>
    obtain ⟨hfe, rfl⟩ := pureC_ok h
    subst hfe
    -- the capability arities at the stored type
    have hicwA : IndCapsWF (.indInfo cvA caps) := by
      obtain ⟨-, -, -, -, -, -, type, -, -, -, -, -, -, -, hcvA⟩ :=
        checkConstantVal_inv hccv
      refine indCapsWF_of_pins (μ := mode) ?_ hfm hty
      rw [hcvA]; exact hpins cv caps0 rfl
    refine ⟨hs₂.residue, rfl, ?_, F₁, ?_⟩
    · exact EnvWF.cons henv (constWF_intro' htf htp
        (Expr.constsResolve_mono htr) htb
        (fun _ _ _ heq => nomatch heq)
        (fun _ _ _ _ heq => nomatch heq)
        (by intro tbl h; exact ConstantInfo.noConfusion h)
        hicwA)
    · unfold checkIndMember
      rw [FueledM.atF_bind, hFm]
      simp only [Bind.bind, Except.bind]
      rfl
  | ctorInfo cv nP nF =>
    obtain ⟨hfe, rfl⟩ := pureC_ok h
    subst hfe
    refine ⟨hs₂.residue, rfl, ?_, F₁, ?_⟩
    · exact EnvWF.cons henv (constWF_intro' htf htp
        (Expr.constsResolve_mono htr) htb
        (fun _ _ _ heq => nomatch heq)
        (fun _ _ _ _ heq => nomatch heq))
    · unfold checkIndMember
      rw [FueledM.atF_bind, hFm]
      simp only [Bind.bind, Except.bind]
      rfl
  | axiomInfo cv => exact nomatch h
  | projInfo e => exact nomatch h
  | defnInfo cv v hint => exact nomatch h
  | thmInfo cv v => exact nomatch h
  | recInfo cv mI rP rules => exact nomatch h

/-- The member fold of the shared driver. -/
theorem foldIndMemberS_run (hμ : mode.verifiedChecks = true) {blockNames : List Name} {caps : IndCaps} :
    ∀ (cis : List ConstantInfo) (env : Env) {s₀ : CState}
      {fe' : FEnv} {s' : CState},
      EnvWF env → CSOKF s₀ →
      -- the block's capability pins at every inductive member
      (∀ ci ∈ cis, ∀ cv caps₀, ci = .indInfo cv caps₀ →
        EtaPins mode env cv.name cv.levelParams caps) →
      (cis.foldlM (checkIndMemberS mode blockNames caps) (mkFEnv env)) s₀ =
        .ok (fe', s') →
      CSOKF s' ∧ fe' = mkFEnv fe'.env ∧
      EnvWF fe'.env ∧
      ∃ F, (cis.foldlM (checkIndMember (fueledOpsM mode) blockNames caps)
        env).val F = .ok fe'.env
  | [], env, s₀, fe', s', henv, hwf, _, h => by
    obtain ⟨hfe, rfl⟩ := pureC_ok h
    subst hfe
    exact ⟨hwf, rfl, henv, 0, rfl⟩
  | ci :: cis, env, s₀, fe', s', henv, hwf, hpins, h => by
    rw [List.foldlM_cons] at h
    obtain ⟨fe₁, s₁, hstep, h⟩ := bindC_ok h
    obtain ⟨hwf₁, hfe₁, henv₁, F₁, hF₁⟩ :=
      checkIndMemberS_run hμ henv hwf (hpins ci List.mem_cons_self) hstep
    -- the step conses one fresh constant, so the pins persist
    have hpins₁ : ∀ ci' ∈ cis, ∀ cv caps₀, ci' = .indInfo cv caps₀ →
        EtaPins mode fe₁.env cv.name cv.levelParams caps := by
      have hF₁' : checkIndMember (fueledOps mode F₁) blockNames caps env ci
          = .ok fe₁.env := by
        rw [← checkIndMember_datF]; exact hF₁
      obtain ⟨cvA, -, -, -, hccv, -, -, -, -, hkind⟩ :=
        checkIndMember_inv hF₁'
      have hfresh : env.find? cvA.name = none := by
        obtain ⟨hf, -, -, -, -, -, type, -, -, -, -, -, -, -, hcvA⟩ :=
          checkConstantVal_inv hccv
        rw [hcvA]; exact hf
      intro ci' hci' cv caps₀ hceq
      have hp := hpins ci' (List.mem_cons_of_mem _ hci') cv caps₀ hceq
      rcases hkind with ⟨-, henv₁eq⟩ | ⟨_, _, _, -, henv₁eq⟩
      · rw [henv₁eq]; exact EtaPins.step hp hfresh
      · rw [henv₁eq]; exact EtaPins.step hp hfresh
    rw [hfe₁] at h
    obtain ⟨hwf', hfe', henv', F₂, hF₂⟩ :=
      foldIndMemberS_run hμ cis fe₁.env henv₁ hwf₁ hpins₁ h
    refine ⟨hwf', hfe', henv', max F₁ F₂, ?_⟩
    rw [List.foldlM_cons]
    exact atF_bind_intro hF₁ hF₂

/-! ## The recursor group -/

/-- The provisioning fold of the shared driver. -/
theorem provisionRecsS_run (hμ : mode.verifiedChecks = true) {blockNames : List Name} :
    ∀ (recs : List ConstantInfo) (env : Env) {s₀ : CState}
      {p : FEnv × List (ConstantVal × Nat × Nat × List RecRule)}
      {s' : CState},
      EnvWF env → CSOKF s₀ →
      provisionRecsS mode blockNames (mkFEnv env) recs s₀ = .ok (p, s') →
      CSOKF s' ∧ p.1 = mkFEnv p.1.env ∧
      EnvWF p.1.env ∧
      ∃ F, (provisionRecs (fueledOpsM mode) blockNames env recs).val F =
        .ok (p.1.env, p.2)
  | [], env, s₀, p, s', henv, hwf, h => by
    obtain ⟨hfe, rfl⟩ := pureC_ok h
    subst hfe
    exact ⟨hwf, rfl, henv, 0, rfl⟩
  | ci :: rest, env, s₀, p, s', henv, hwf, h => by
    unfold provisionRecsS at h
    simp only [checkMemberValF_eq] at h
    cases ci with
    | axiomInfo cv => exact nomatch h
    | projInfo e => exact nomatch h
    | defnInfo cv v hint => exact nomatch h
    | thmInfo cv v => exact nomatch h
    | indInfo cv caps0 => exact nomatch h
    | ctorInfo cv nP nF => exact nomatch h
    | recInfo cv mI rP rules =>
    obtain ⟨u, s₁, hflush, h⟩ := bindC_ok h
    rw [flushC_run] at hflush
    injection hflush with hflush
    obtain rfl : s₀.flushed = s₁ :=
      congrArg Prod.snd hflush
    obtain ⟨cvA, s₂, hcm, h⟩ := bindC_ok h
    obtain ⟨hs₂, cvA', ⟨rfl, hwty⟩, F₁, hFm⟩ :=
      (checkMemberValS_sim hμ henv (flushC_csok hwf)) cvA s₂ hcm
    have hFmp : checkMemberVal (fueledOps mode F₁) blockNames env
        (ConstantInfo.recInfo cv mI rP rules).toConstantVal = .ok cvA := by
      rw [← checkMemberVal_datF]; exact hFm
    obtain ⟨hccv, -⟩ := checkMemberVal_inv hFmp
    have henv₁ : EnvWF ⟨.recInfo cvA mI rP [] :: env.consts⟩ :=
      envWF_cons_provRec henv hccv
    obtain ⟨p', s₃, hrec, h⟩ := bindC_ok h
    rw [show (mkFEnv env).push (.recInfo cvA mI rP []) =
      mkFEnv ⟨.recInfo cvA mI rP [] :: env.consts⟩ from rfl] at hrec
    obtain ⟨hwf₃, hfeS, henvS, F₂, hF₂⟩ :=
      provisionRecsS_run hμ rest _ henv₁ hs₂.residue hrec
    obtain ⟨feSelf, others⟩ := p'
    obtain ⟨hfe, rfl⟩ := pureC_ok h
    subst hfe
    refine ⟨hwf₃, hfeS, henvS, max F₁ F₂, ?_⟩
    show (provisionRecs (fueledOpsM mode) blockNames env
      (ConstantInfo.recInfo cv mI rP rules :: rest)).val (max F₁ F₂) = _
    unfold provisionRecs
    rw [FueledM.atF_bind,
      (checkMemberVal (fueledOpsM mode) blockNames env _).property
        (Nat.le_max_left F₁ F₂) hFm]
    simp only [Bind.bind, Except.bind]
    rw [(provisionRecs (fueledOpsM mode) blockNames
        ⟨.recInfo cvA mI rP [] :: env.consts⟩ rest).property
        (Nat.le_max_right F₁ F₂) hF₂]
    rfl

/-- Transport `ConstWF` along lookup-presence monotonicity. -/
private theorem constWF_le' {envA envB : Env}
    (hle : ∀ n, (envA.find? n).isSome = true →
      (envB.find? n).isSome = true)
    {c : ConstantInfo} (h : ConstWF envA c) : ConstWF envB c := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h8, h9⟩ := h
  refine ⟨h1, h2, Expr.constsResolve_le hle h3, h4, ?_, ?_,
    fun tbl heq =>
      let ⟨hs, hb⟩ := h8 tbl heq
      ⟨hs, fun i b hbi =>
        let ⟨g1, g2, g3, g4⟩ := hb i b hbi
        ⟨g1, g2, Expr.constsResolve_le hle g3, g4⟩⟩, h9⟩
  · intro cv v hint heq
    obtain ⟨g1, g2, g3, g4⟩ := h5 cv v hint heq
    exact ⟨g1, g2, Expr.constsResolve_le hle g3, g4⟩
  · intro cv a b e heq r hr
    obtain ⟨g1, g2, g3, g4, g5⟩ := h6 cv a b e heq r hr
    refine ⟨g1, g2, Expr.constsResolve_le hle g3, g4, ?_⟩
    intro lvls pins hf
    obtain ⟨n1, n2, n3, n4⟩ := g5 lvls pins hf
    refine ⟨n1, n2, ?_, n4⟩
    intro pin hp
    obtain ⟨p1, p2, p3, p4⟩ := n3 pin hp
    exact ⟨p1, p2, Expr.constsResolve_le hle p3, p4⟩

/-- A `CheckCM` throw composed with anything never succeeds. -/
theorem throwC_bind_ok {α β : Type} {e : CheckError} {k : α → CheckCM β}
    {s₀ : CState} {v : β} {s' : CState}
    (h : ((throw e : CheckCM α) >>= k) s₀ = .ok (v, s')) : False := by
  exact nomatch h

/-- The iota fold of the shared driver: all operations run at
`envSelf`, one shared state across the whole fold. -/
private theorem iotaFoldS_run (hμ : mode.verifiedChecks = true) {env₂ envSelf : Env}
    (henv₂ : EnvWF env₂) (henvS : EnvWF envSelf) {f : Name → Name} :
    ∀ (checked : List (ConstantVal × Nat × Nat × List RecRule))
      (acc : FEnv) {s₀ : CState} {fe₃ : FEnv} {s' : CState},
      (∀ c ∈ checked, c.1.type.hasFvar = false) →
      CSOK mode envSelf s₀ →
      (checked.foldlM (fun (acc : FEnv) (c : ConstantVal × Nat × Nat × List RecRule) => do
          let rules' ← checkIotaRules mode (sharedOpsC mode (mkFEnv envSelf)) env₂
            envSelf f c.1.name c.1.levelParams c.1.type c.2.1 c.2.2.1
            0 c.2.2.2
          pure (acc.push (.recInfo c.1 c.2.1 c.2.2.1 rules'))) acc) s₀ =
        .ok (fe₃, s') →
      CSOKF s' ∧
      (acc = mkFEnv acc.env → fe₃ = mkFEnv fe₃.env) ∧
      ∃ F, (checked.foldlM (fun (acc : Env) (c : ConstantVal × Nat × Nat × List RecRule) => do
          let rules' ← checkIotaRules mode (fueledOpsM mode) env₂ envSelf f c.1.name
            c.1.levelParams c.1.type c.2.1 c.2.2.1 0 c.2.2.2
          pure (⟨.recInfo c.1 c.2.1 c.2.2.1 rules' :: acc.consts⟩ : Env))
          acc.env).val F = .ok fe₃.env
  | [], acc, s₀, fe₃, s', _, hs, h => by
    obtain ⟨hfe, rfl⟩ := pureC_ok h
    subst hfe
    exact ⟨hs.residue, fun hacc => hacc, 0, rfl⟩
  | c :: rest, acc, s₀, fe₃, s', htys, hs, h => by
    rw [List.foldlM_cons] at h
    obtain ⟨acc₁, s₁, hstep, h⟩ := bindC_ok h
    obtain ⟨rules', s₂, hir, hstep⟩ := bindC_ok hstep
    obtain ⟨hs₂, rules'', hPr, F₁, hF₁⟩ :=
      (checkIotaRulesS_sim hμ henv₂ henvS
        (htys c List.mem_cons_self) hs) rules' s₂ hir
    obtain rfl : rules' = rules'' := hPr
    obtain ⟨hacc₁, rfl⟩ := pureC_ok hstep
    subst hacc₁
    obtain ⟨hwf', hfe', F₂, hF₂⟩ := iotaFoldS_run hμ henv₂ henvS rest
      (acc.push (.recInfo c.1 c.2.1 c.2.2.1 rules'))
      (fun c' hc' => htys c' (List.mem_cons_of_mem _ hc')) hs₂ h
    refine ⟨hwf', fun hacc => hfe' (by rw [hacc]; rfl), max F₁ F₂, ?_⟩
    rw [List.foldlM_cons]
    have hF₂' : (rest.foldlM (fun (acc : Env) (c : ConstantVal × Nat × Nat × List RecRule) => do
        let rules' ← checkIotaRules mode (fueledOpsM mode) env₂ envSelf f c.1.name
          c.1.levelParams c.1.type c.2.1 c.2.2.1 0 c.2.2.2
        pure (⟨.recInfo c.1 c.2.1 c.2.2.1 rules' :: acc.consts⟩ : Env))
        (⟨.recInfo c.1 c.2.1 c.2.2.1 rules' :: acc.env.consts⟩ :
          Env)).val F₂ = .ok fe₃.env := hF₂
    refine atF_bind_intro (F₁ := F₁) (F₂ := F₂) ?_ hF₂'
    rw [FueledM.atF_bind, hF₁]
    rfl

/-- Convert the constructed fueled iota fold to a pure fold at the
same fuel. -/
private theorem iotaFold_datF {env₂ envSelf : Env} {f : Name → Name}
    {F : Nat} :
    ∀ (checked : List (ConstantVal × Nat × Nat × List RecRule))
      (acc : Env) {env₃ : Env},
      (checked.foldlM (fun (acc : Env) (c : ConstantVal × Nat × Nat × List RecRule) => do
          let rules' ← checkIotaRules mode (fueledOpsM mode) env₂ envSelf f c.1.name
            c.1.levelParams c.1.type c.2.1 c.2.2.1 0 c.2.2.2
          pure (⟨.recInfo c.1 c.2.1 c.2.2.1 rules' :: acc.consts⟩ : Env))
          acc).val F = .ok env₃ →
      checked.foldlM (fun (acc : Env) (c : ConstantVal × Nat × Nat × List RecRule) => do
          let rules' ← checkIotaRules mode (fueledOps mode F) env₂ envSelf f
            c.1.name c.1.levelParams c.1.type c.2.1 c.2.2.1 0 c.2.2.2
          pure (⟨.recInfo c.1 c.2.1 c.2.2.1 rules' :: acc.consts⟩ : Env))
          acc = .ok env₃
  | [], acc, env₃, h => h
  | c :: rest, acc, env₃, h => by
    rw [List.foldlM_cons] at h ⊢
    obtain ⟨e₁, hstep, h⟩ := atF_bind_ok h
    obtain ⟨rules', hir, hstep⟩ := atF_bind_ok hstep
    rw [checkIotaRules_datF] at hir
    show ((checkIotaRules mode (fueledOps mode F) env₂ envSelf f c.1.name
      c.1.levelParams c.1.type c.2.1 c.2.2.1 0 c.2.2.2 >>= _ :
        CheckM Env) >>= _) = _
    rw [hir]
    simp only [Bind.bind, Except.bind]
    have hstep' : (⟨.recInfo c.1 c.2.1 c.2.2.1 rules' ::
        acc.consts⟩ : Env) = e₁ := by
      have hst : (Except.ok (⟨.recInfo c.1 c.2.1 c.2.2.1 rules' ::
          acc.consts⟩ : Env) : Except CheckError Env) = .ok e₁ := hstep
      exact Except.ok.inj hst
    simp only [pure, Except.pure]
    rw [hstep']
    exact iotaFold_datF rest e₁ h

/-- The recursor group of the shared driver. -/
theorem checkIndRecsS_run (hμ : mode.verifiedChecks = true) {blockNames : List Name} {env₂ : Env}
    {recs : List ConstantInfo} (henv₂ : EnvWF env₂)
    (hbn : ∀ ci ∈ recs, blockNames.contains ci.name = true)
    {s₀ : CState} (hwf : CSOKF s₀) {fe₃ : FEnv} {s' : CState}
    (h : checkIndRecsS mode blockNames (mkFEnv env₂) recs s₀ =
      .ok (fe₃, s')) :
    CSOKF s' ∧ fe₃ = mkFEnv fe₃.env ∧
    EnvWF fe₃.env ∧
    ∃ F, (checkIndRecs mode (fueledOpsM mode) blockNames env₂ recs).val F =
      .ok fe₃.env := by
  unfold checkIndRecsS at h
  by_cases hemp : recs.isEmpty = true
  · rw [if_pos hemp] at h
    obtain ⟨hfe, rfl⟩ := pureC_ok h
    subst hfe
    refine ⟨hwf, rfl, henv₂, 0, ?_⟩
    show (checkIndRecs mode (fueledOpsM mode) blockNames env₂ recs).val 0 = _
    unfold checkIndRecs
    rw [FueledM.atF_ite, if_pos hemp]
    rfl
  rw [if_neg hemp] at h
  dsimp only at h
  by_cases heqf : env₂.find? eqName = some eqA
  case neg =>
    rw [if_neg (show ¬((mkFEnv env₂).find? eqName = some eqA) by
      rw [mkFEnv_find?]; exact heqf)] at h
    exact absurd h throwC_bind_ok
  rw [if_pos (show (mkFEnv env₂).find? eqName = some eqA by
    rw [mkFEnv_find?]; exact heqf)] at h
  obtain ⟨p, s₁, hprovR, h⟩ := bindC_ok h
  obtain ⟨feSelf, checked⟩ := p
  obtain ⟨hwf₁, hfeS, henvS, F₁, hF₁⟩ :=
    provisionRecsS_run hμ recs env₂ henv₂ hwf hprovR
  obtain ⟨u, s₂, hflush, h⟩ := bindC_ok h
  rw [flushC_run] at hflush
  injection hflush with hflush
  obtain rfl : s₁.flushed = s₂ :=
    congrArg Prod.snd hflush
  -- the pure provisioning run and its facts
  have hprovP : provisionRecs (fueledOps mode F₁) blockNames env₂ recs =
      .ok (feSelf.env, checked) := by
    rw [← provisionRecs_datF]; exact hF₁
  have hProvF₁ := provisionRecs_facts (F := F₁) recs env₂
    (feSelf.env, checked) hprovP hbn
  have htys : ∀ c ∈ checked, c.1.type.hasFvar = false := by
    intro c hc
    obtain ⟨-, -, -, -, htyf, -, -, -, -, -⟩ :=
      ProvFacts.mem_facts hProvF₁ c hc
    exact htyf
  -- the iota fold in the shared state at `envSelf`
  rw [hfeS] at h
  simp only [checkIotaRulesF_eq] at h
  obtain ⟨hwf', hfe₃, F₂, hF₂⟩ := iotaFoldS_run hμ henv₂ henvS checked
    (mkFEnv env₂) htys (flushC_csok hwf₁) h
  have hfe₃' : fe₃ = mkFEnv fe₃.env := hfe₃ rfl
  -- both phases at the joined fuel, for the `RulesChain` machinery
  have hF₁M : (provisionRecs (fueledOpsM mode) blockNames env₂ recs).val
      (max F₁ F₂) = .ok (feSelf.env, checked) :=
    (provisionRecs (fueledOpsM mode) blockNames env₂ recs).property
      (Nat.le_max_left F₁ F₂) hF₁
  have hF₂M := (checked.foldlM (fun (acc : Env)
      (c : ConstantVal × Nat × Nat × List RecRule) => do
      let rules' ← checkIotaRules mode (fueledOpsM mode) env₂ feSelf.env
        (fun n => if blockNames.contains n then n.str "_model" else n)
        c.1.name c.1.levelParams c.1.type c.2.1 c.2.2.1 0 c.2.2.2
      pure (⟨.recInfo c.1 c.2.1 c.2.2.1 rules' :: acc.consts⟩ : Env))
      env₂ : FueledM Env).property (Nat.le_max_right F₁ F₂) hF₂
  have hprovPM : provisionRecs (fueledOps mode (max F₁ F₂)) blockNames env₂
      recs = .ok (feSelf.env, checked) := by
    rw [← provisionRecs_datF]; exact hF₁M
  have hProv := provisionRecs_facts (F := max F₁ F₂) recs env₂
    (feSelf.env, checked) hprovPM hbn
  refine ⟨hwf', hfe₃', ?_, ?_⟩
  · -- the final environment is well-formed (as in `checkIndRecs_wfimp`)
    have hpure := iotaFold_datF checked env₂ hF₂M
    obtain ⟨zipped, hmap, hchain⟩ := rulesFold_inv checked env₂ fe₃.env
      hpure
    rw [show checked = zipped.map Prod.fst from hmap.symm] at hProv htys
    have hswSh := chains_swapSh hProv hchain
      (SwapShList.of_eq env₂.consts)
    have hcorr := swapSh_find?_corr hswSh
    have hisoSome : ∀ n, (feSelf.env.find? n).isSome =
        (fe₃.env.find? n).isSome := by
      intro n
      rcases hcorr n with heq | ⟨cv, a, b, e0, h₀, h₃, -⟩
      · rw [heq]
      · rw [h₀, h₃]
        rfl
    intro c₃ hc₃
    rcases rulesChain_mem hchain c₃ hc₃ with hc₂ | ⟨z, hz, rfl⟩
    · refine constWF_le' (fun n hn => ?_) (henv₂ c₃ hc₂)
      rw [← hisoSome n]
      cases hf2 : env₂.find? n with
      | none =>
        rw [hf2] at hn
        exact nomatch hn
      | some ci₂ =>
        rw [ProvFacts.find?_preserved hProv n ci₂ hf2]
        rfl
    · have hz1 : z.1 ∈ zipped.map Prod.fst := List.mem_map_of_mem hz
      obtain ⟨-, -, -, -, htyf, htyb, htlp, htres, -, -⟩ :=
        ProvFacts.mem_facts hProv z.1 hz1
      have hkits0 := checkIotaRules_inv 0 _ _
        (RulesChain.mem_facts hchain z hz)
      refine constWF_intro' htyf htlp ?_ htyb
        (fun _ _ _ heq => nomatch heq) ?_
      · rw [← Expr.constsResolve_congr hisoSome]
        exact htres
      · intro cvR mI' rP' rules'' heq r hr
        injection heq with e1 e2 e3 e4
        subst e1; subst e2; subst e3; subst e4
        obtain ⟨k, hk⟩ := List.getElem?_of_mem hr
        obtain ⟨cvj, cnP, cnF, raw, rhsTy, rbinders, rbody, -, -, -, -,
          hnest, -, -, -, hrf, hrb, hrlp, hrres, -, -, -⟩ := hkits0 k r hk
        refine ⟨hrf, hrlp, ?_, hrb, ?_⟩
        · rw [← Expr.constsResolve_congr hisoSome]
          exact hrres
        · intro lvls pins hfe
          obtain ⟨hmi, hlvls, hpins, hshape, -⟩ := hnest lvls pins hfe
          refine ⟨hmi, hlvls, ?_, hshape⟩
          intro pin hp
          obtain ⟨p1, p2, p3, p4⟩ := hpins pin hp
          exact ⟨p1, p2,
            by rw [← Expr.constsResolve_congr hisoSome]; exact p3, p4⟩
  · refine ⟨max F₁ F₂, ?_⟩
    unfold checkIndRecs
    rw [FueledM.atF_ite, if_neg hemp]
    dsimp only
    rw [if_pos heqf]
    rw [FueledM.atF_bind, hF₁M]
    simp only [Bind.bind, Except.bind]
    exact hF₂M

/-! ## The projection phases -/

/-- The projection-function install (mirrors `checkProjFn`). -/
theorem checkProjFnS_run (hμ : mode.verifiedChecks = true) {env : Env} (henv : EnvWF env)
    {T ctorName : Name} {lps : List Name} {nP nF i : Nat}
    {s₀ : CState} (hs : CSOK mode env s₀) {fe' : FEnv} {s' : CState}
    (h : checkProjFnS mode (mkFEnv env) T ctorName lps nP nF i s₀ =
      .ok (fe', s')) :
    CSOKF s' ∧ fe' = mkFEnv fe'.env ∧
    EnvWF fe'.env ∧
    ∃ F, (checkProjFn mode (fueledOpsM mode) env T ctorName lps nP nF i).val F =
      .ok fe'.env := by
  unfold checkProjFnS at h
  simp only [checkProjLookupsF_eq, checkProjTyF_eq, checkProjRuleF_eq,
    checkProjIotaF_eq] at h
  obtain ⟨pr, s₁, hlk, h⟩ := bindC_ok h
  obtain ⟨hs₁, pr', hPlk, F₀, hFlk⟩ :=
    (checkProjLookupsS_sim hs) pr s₁ hlk
  obtain rfl : pr = pr' := hPlk
  obtain ⟨cvj, mcv⟩ := pr
  obtain ⟨pty, s₂, hty, h⟩ := bindC_ok h
  obtain ⟨hs₂, pty', hPty, F₀', hFty⟩ :=
    (checkProjTyS_sim hs₁) pty s₂ hty
  obtain rfl : pty = pty' := hPty
  obtain ⟨u0, s₂', hshape, h⟩ := bindC_ok h
  obtain ⟨hs₂', u0', hPu0, F₀'', hFshape⟩ :=
    (checkProjShapeS_sim hs₂) u0 s₂' hshape
  by_cases hi : i < nF
  case neg =>
    rw [if_neg hi] at h
    exact absurd h throwC_bind_ok
  rw [if_pos hi] at h
  obtain ⟨rhsA, s₃, hrule, h⟩ := bindC_ok h
  have hTYc0 : (checkProjTy env T ctorName lps mcv.type nP nF :
      CheckM _) = .ok pty := by
    rw [← checkProjTy_datF (F := F₀')]
    exact hFty
  obtain ⟨hptyf, hptyb⟩ := checkProjTy_wf hTYc0
  have hLKc0 : (checkProjLookups env T ctorName lps nP nF i :
      CheckM _) = .ok (cvj, mcv) := by
    rw [← checkProjLookups_datF (F := F₀)]
    exact hFlk
  obtain ⟨cnP0, cnF0, hctorE⟩ := checkProjLookups_ctor hLKc0
  obtain ⟨hs₃, rhsA', hPr, F₁, hFr⟩ :=
    (checkProjRuleS_sim hμ henv hptyf
      (show cvj.type.hasFvar = false from
        (henv _ (find?_mem hctorE)).1) hs₂') rhsA s₃ hrule
  obtain rfl : rhsA = rhsA' := hPr
  obtain ⟨u, s₄, hio, h⟩ := bindC_ok h
  obtain ⟨hs₄, u', hPu, F₂, hFio⟩ :=
    (checkProjIotaS_sim hμ henv hs₃) u s₄ hio
  obtain ⟨hfe, rfl⟩ := pureC_ok h
  subst hfe
  -- the ops-free stages, `CheckM`-level
  have hLKc : (checkProjLookups env T ctorName lps nP nF i :
      CheckM _) = .ok (cvj, mcv) := by
    rw [← checkProjLookups_datF (F := F₀)]
    exact hFlk
  have hTYc : (checkProjTy env T ctorName lps mcv.type nP nF :
      CheckM _) = .ok pty := by
    rw [← checkProjTy_datF (F := F₀')]
    exact hFty
  have hSHc : (checkProjShape pty cvj.type nP nF : CheckM Unit)
      = .ok u0 := by
    rw [← checkProjShape_datF (F := F₀'')]
    exact hFshape
  -- both fueled stages at a common fuel
  obtain ⟨F₃, hF₁₃, hF₂₃⟩ : ∃ F₃, F₁ ≤ F₃ ∧ F₂ ≤ F₃ :=
    ⟨max F₁ F₂, Nat.le_max_left _ _, Nat.le_max_right _ _⟩
  have hIOc : checkProjIota mode (fueledOps mode F₃) env env T ctorName lps cvj
      nP nF i = .ok u' := by
    rw [← checkProjIota_datF (F := F₃)]
    exact (checkProjIota mode (fueledOpsM mode) env env T ctorName lps cvj nP nF
      i).property hF₂₃ hFio
  have hFrp : checkProjRule (fueledOps mode F₃) env pty cvj lps nP nF i =
      .ok rhsA := by
    rw [← checkProjRule_datF]
    exact (checkProjRule (fueledOpsM mode) env pty cvj lps nP nF
      i).property hF₁₃ hFr
  have hFnp : checkProjFn mode (fueledOps mode F₃) env T ctorName lps nP nF i =
      .ok (⟨.recInfo ⟨projFnName T i, lps, pty⟩ nP nP
        [projFnRule env.find? T ctorName pty nP nF i rhsA] :: env.consts⟩ : Env) := by
    unfold checkProjFn
    show ((checkProjLookups env T ctorName lps nP nF i :
      CheckM _) >>= _) = _
    rw [hLKc]
    simp only [Bind.bind, Except.bind]
    show ((checkProjTy env T ctorName lps mcv.type nP nF :
      CheckM _) >>= _) = _
    rw [hTYc]
    simp only [Bind.bind, Except.bind]
    show ((checkProjShape pty cvj.type nP nF : CheckM Unit) >>= _) = _
    rw [hSHc]
    simp only [Bind.bind, Except.bind]
    try dsimp only
    rw [if_pos hi]
    show (checkProjRule (fueledOps mode F₃) env pty cvj lps nP nF i >>= _)
      = _
    rw [hFrp]
    simp only [Bind.bind, Except.bind]
    show (checkProjIota mode (fueledOps mode F₃) env env T ctorName lps cvj nP
      nF i >>= _) = _
    rw [hIOc]
    simp only [Bind.bind, Except.bind]
    rfl
  have hFn : (checkProjFn mode (fueledOpsM mode) env T ctorName lps nP nF
      i).val F₃ = .ok (⟨.recInfo ⟨projFnName T i, lps, pty⟩ nP nP
        [projFnRule env.find? T ctorName pty nP nF i rhsA] :: env.consts⟩ : Env) := by
    rw [checkProjFn_datF]
    exact hFnp
  rw [show FEnv.find? (mkFEnv env) = env.find? from mkFEnv_find?_fun env]
  refine ⟨hs₄.residue, rfl, ?_, F₃, hFn⟩
  -- the installed projection recursor is well-formed
  obtain ⟨cvj', mcv', hlk', pty', hty', ⟨_, hshape'⟩, hi', rhsA',
    hrule', ⟨_, hio'⟩, heq⟩ := checkProjFn_inv hFnp
  have heq' := heq
  simp only [Env.mk.injEq, List.cons.injEq] at heq'
  obtain ⟨hrecEq, -⟩ := heq'
  obtain ⟨-, -, hres, hbv, hfv, hlp, -⟩ := checkProjTy_inv hty'
  obtain ⟨raw, rb, cb, cbody, hraw, hrf, hrb, hann, halp, hrres, hrbv,
    hrfv, hsl, hsp, hdm, -⟩ := checkProjRule_inv hrule'
  show EnvWF (⟨.recInfo ⟨projFnName T i, lps, pty⟩ nP nP
      [projFnRule env.find? T ctorName pty nP nF i rhsA] :: env.consts⟩ : Env)
  rw [show (⟨.recInfo ⟨projFnName T i, lps, pty⟩ nP nP
      [projFnRule env.find? T ctorName pty nP nF i rhsA] :: env.consts⟩ : Env) =
    ⟨.recInfo ⟨projFnName T i, lps, pty'⟩ nP nP
      [projFnRule env.find? T ctorName pty' nP nF i rhsA'] :: env.consts⟩
    from by rw [hrecEq]]
  refine EnvWF.cons henv (constWF_intro' hfv hlp
    (Expr.constsResolve_mono hres) hbv
    (fun _ _ _ heq2 => nomatch heq2) ?_)
  intro cvR mI' rP' rules'' heq2 r hr
  injection heq2 with e1 e2 e3 e4
  subst e1
  subst e4
  rcases List.mem_singleton.mp hr with rfl
  refine ⟨hrfv, halp, Expr.constsResolve_mono hrres, hrbv, ?_⟩
  intro lvls pins hf
  cases hcond : Expr.recRulePlain pty' nP nP nP <;>
    simp [projFnRule, recRuleBits, hcond] at hf

/-- One projection-function install step. -/
theorem installProjFnStepS_run (hμ : mode.verifiedChecks = true) {env : Env} (henv : EnvWF env)
    {T ctorName : Name} {lps : List Name} {nP nF i : Nat}
    {s₀ : CState} (hwf : CSOKF s₀) {fe' : FEnv} {s' : CState}
    (h : installProjFnStepS mode T ctorName lps nP nF (mkFEnv env) i s₀ =
      .ok (fe', s')) :
    CSOKF s' ∧ fe' = mkFEnv fe'.env ∧
    EnvWF fe'.env ∧
    ∃ F, (installProjFnStep mode (fueledOpsM mode) T ctorName lps nP nF env
      i).val F = .ok fe'.env := by
  unfold installProjFnStepS at h
  rw [mkFEnv_find?] at h
  by_cases hart : (env.find? (projModelName T i)).isSome = true
  · rw [if_pos hart] at h
    obtain ⟨u, s₁, hflush, h⟩ := bindC_ok h
    rw [flushC_run] at hflush
    injection hflush with hflush
    obtain rfl : s₀.flushed = s₁ :=
      congrArg Prod.snd hflush
    obtain ⟨hwf', hfe', henv', F, hF⟩ :=
      checkProjFnS_run hμ henv (flushC_csok hwf) h
    refine ⟨hwf', hfe', henv', F, ?_⟩
    unfold installProjFnStep
    rw [FueledM.atF_ite, if_pos hart]
    exact hF
  · rw [if_neg hart] at h
    obtain ⟨hfe, rfl⟩ := pureC_ok h
    subst hfe
    refine ⟨hwf, rfl, henv, 0, ?_⟩
    unfold installProjFnStep
    rw [FueledM.atF_ite, if_neg hart]
    rfl

/-- The artifact-phase fold. -/
theorem foldProjFnS_run (hμ : mode.verifiedChecks = true) {T ctorName : Name} {lps : List Name}
    {nP nF : Nat} :
    ∀ (idxs : List Nat) (env : Env) {s₀ : CState} {fe' : FEnv}
      {s' : CState},
      EnvWF env → CSOKF s₀ →
      (idxs.foldlM (installProjFnStepS mode T ctorName lps nP nF)
        (mkFEnv env)) s₀ = .ok (fe', s') →
      CSOKF s' ∧ fe' = mkFEnv fe'.env ∧
      EnvWF fe'.env ∧
      ∃ F, (idxs.foldlM (installProjFnStep mode (fueledOpsM mode) T ctorName lps
        nP nF) env).val F = .ok fe'.env
  | [], env, s₀, fe', s', henv, hwf, h => by
    obtain ⟨hfe, rfl⟩ := pureC_ok h
    subst hfe
    exact ⟨hwf, rfl, henv, 0, rfl⟩
  | i :: idxs, env, s₀, fe', s', henv, hwf, h => by
    rw [List.foldlM_cons] at h
    obtain ⟨fe₁, s₁, hstep, h⟩ := bindC_ok h
    obtain ⟨hwf₁, hfe₁, henv₁, F₁, hF₁⟩ :=
      installProjFnStepS_run hμ henv hwf hstep
    rw [hfe₁] at h
    obtain ⟨hwf', hfe', henv', F₂, hF₂⟩ :=
      foldProjFnS_run hμ idxs fe₁.env henv₁ hwf₁ h
    refine ⟨hwf', hfe', henv', max F₁ F₂, ?_⟩
    rw [List.foldlM_cons]
    exact atF_bind_intro hF₁ hF₂

end ConLeche.Cached
