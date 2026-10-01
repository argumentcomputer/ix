module

public import ConLeche.Verify.Cached.BridgeC
public import ConLeche.Model.Fold
public import ConLeche.Verify.Cached.PushChain
import ConLeche.Verify.Cached.KnotCongr
import ConLeche.Verify.CheckerSplit

public section

/-!
# The model along the install run, and the letters on the fully checked environment

`FullyChecked μ ds` (`ConLeche/Cached/Installed.lean`) is what the
driver's two loops assemble: phase A's accepting run (`InstallRun`)
installs a separable value declaration by the install half and records
its datum, and every record was checked against the prefix view
`fe.restrictTo vis` from a fresh memo state (`GroupChecked`).  This
module walks the run with the graded model beside it:

* `annotConstantValC_run` / `annotValC_run` / `annotValueC_run` — phase
  A's install simulates the pure install halves
  (`installConstantVal`, `installValue`, `ConLeche/Kernel/CheckerSplit.lean`).
* `checkPending_run` — the check at the prefix view simulates the pure
  check half `checkValueGroup` at the truncated environment.  The view
  and `mkFEnv` of the truncated environment have the same `find?`
  (`mkFEnv_find?_visibleBelow`, under the name uniqueness every driver
  step preserves — `PushChain`), so by `coreKnotI_congr` they run the
  SAME core, and the simulation stated at `mkFEnv env` covers the check
  at the view.
* `installRun_model` — the walk: at each position the model supplies
  the well-formedness of the environment every bridge from the
  executable core takes; an ordinary step is a `checkDecl` run by
  `checkDeclStepC_run`, a separable value declaration is the two halves
  re-associated into a `checkDecl` run (`checkDecl_of_split_*`,
  `ConLeche/Verify/CheckerSplit.lean`) with the record's check consumed
  at the position that produced it; `declStep_preserves` carries the
  model across either.
* `fullyChecked_sound` / `no_proof_of_False_checked` /
  `no_proof_of_Empty_checked` — the letters on the fully checked
  environment the driver assembles.  The
  fold's letters (`ConLeche/Verify/Cached/MainC.lean`) are these under
  `checkDecls_fullyChecked`.

The set theory is a hypothesis of every walk although the letters'
conclusions do not mention it: the model is what supplies the
well-formedness the bridges need.
-/

namespace ConLeche.Cached

open ConLeche ConLeche.Semantics ConLeche.Model

universe w
variable {V : Type w} [SetTheory V] {μ : CheckMode}
variable {pins : List NatOpPinSet}

/-! ## The two-phase driver: phase A's install halves -/

/-- Phase A's header install simulates the pure install half: from an
invariant state at `mkFEnv env`, a successful run returns the header
with its annotated type, well scoped, and `installConstantVal` succeeds
on it at some fuel. -/
theorem annotConstantValC_run (hμ : μ.verifiedChecks = true) {env : Env} (henv : EnvWF env)
    {cv cvA : ConstantVal} {jty : Expr} {s₀ s' : CState} (hs : CSOK μ env s₀)
    (h : annotConstantValC μ (mkFEnv env) cv s₀ = .ok ((cvA, jty), s')) :
    CSOK μ env s' ∧ cvA = { cv with type := jty } ∧ Expr.WScoped 0 jty ∧
    ∃ F, installConstantVal (fueledOps μ F) env cv = .ok cvA := by
  unfold annotConstantValC at h
  simp only [mkFEnv_find?] at h
  by_cases h1 : (env.find? cv.name).isSome = true
  · rw [if_pos h1] at h; exact absurd h throwC_bind_ok
  rw [if_neg h1] at h
  by_cases h2 : reservedBasisNames.contains cv.name = true
  · rw [if_pos h2] at h; exact absurd h throwC_bind_ok
  rw [if_neg h2] at h
  by_cases h3 : cv.name.isProjFnShape = true
  · rw [if_pos h3] at h; exact absurd h throwC_bind_ok
  rw [if_neg h3] at h
  by_cases h4 : Name.nodup cv.levelParams = true
  case neg => rw [if_neg h4] at h; exact absurd h throwC_bind_ok
  rw [if_pos h4] at h
  by_cases h5 : Expr.looseBVarsBounded 0 cv.type = true
  case neg => rw [if_neg h5] at h; exact absurd h throwC_bind_ok
  rw [if_pos h5] at h
  rw [hasFvar_spec rfl] at h
  by_cases h6 : Expr.hasFvar cv.type = true
  · rw [if_pos h6] at h; exact absurd h throwC_bind_ok
  rw [if_neg h6] at h
  obtain ⟨jA, s₁, hann, h⟩ := bindC_ok h
  obtain ⟨hs₁, w, ⟨hjA, hwty⟩, F, hF⟩ :=
    (ssimC hμ env henv checkFuel).annotate hs rfl
      (Expr.WScoped.of_not_hasFvar (Bool.not_eq_true _ ▸ h6)) jA s₁ hann
  obtain rfl := hjA
  rw [Expr.allLevelParamsDefinedC_spec] at h
  by_cases h7 : Expr.allLevelParamsDefined cv.levelParams jA = true
  case neg => rw [if_neg h7] at h; exact absurd h throwC_bind_ok
  rw [if_pos h7] at h
  rw [constsResolveFC_spec, constsResolveF_eq] at h
  by_cases h8 : Expr.constsResolve env jA = true
  case neg => rw [if_neg h8] at h; exact absurd h throwC_bind_ok
  rw [if_pos h8] at h
  obtain ⟨hv, rfl⟩ := pureC_ok h
  obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ hv
  refine ⟨hs₁, rfl, hwty, F, ?_⟩
  exact installConstantVal_of_facts (Option.not_isSome_iff_eq_none.mp h1)
    (by simpa using h2) (by simpa using h3) h4 h5 (by simpa using h6) hF h7 h8

/-- Phase A's value install simulates the pure install half. -/
theorem annotValC_run (hμ : μ.verifiedChecks = true) {env : Env} (henv : EnvWF env)
    {cvA : ConstantVal} {jty value jv : Expr} {record : Bool} {s₀ s' : CState}
    (hjty : jty = cvA.type) (hs : CSOK μ env s₀)
    (h : annotValC μ (mkFEnv env) cvA jty value record s₀ = .ok (jv, s')) :
    CSOK μ env s' ∧ Expr.WScoped 0 jv ∧
    ∃ F, installValue (fueledOps μ F) env cvA value = .ok jv := by
  unfold annotValC at h
  by_cases h1 : Expr.looseBVarsBounded 0 value = true
  case neg => rw [if_neg h1] at h; exact absurd h throwC_bind_ok
  rw [if_pos h1] at h
  rw [hasFvar_spec rfl] at h
  by_cases h2 : Expr.hasFvar value = true
  · rw [if_pos h2] at h; exact absurd h throwC_bind_ok
  rw [if_neg h2] at h
  obtain ⟨jA, s₁, hann, h⟩ := bindC_ok h
  obtain ⟨hs₁, w, ⟨hjA, hwv⟩, F, hF⟩ :=
    (ssimC hμ env henv checkFuel).annotate hs rfl
      (Expr.WScoped.of_not_hasFvar (Bool.not_eq_true _ ▸ h2)) jA s₁ hann
  obtain rfl := hjA
  rw [Expr.allLevelParamsDefinedC_spec] at h
  by_cases h3 : Expr.allLevelParamsDefined cvA.levelParams jA = true
  case neg => rw [if_neg h3] at h; exact absurd h throwC_bind_ok
  rw [if_pos h3] at h
  rw [constsResolveFC_spec, constsResolveF_eq] at h
  by_cases h4 : Expr.constsResolve env jA = true
  case neg => rw [if_neg h4] at h; exact absurd h throwC_bind_ok
  rw [if_pos h4] at h
  obtain ⟨u, s₂, hrec, h⟩ := bindC_ok h
  obtain ⟨hs₂, -⟩ := recordCConst_eff hs₁ (hjty ▸ rfl)
    (fun vE vi hv => by
      cases record <;> simp only [Bool.false_eq_true, ↓reduceIte] at hv
      · exact nomatch hv
      · cases hv; rfl) u s₂ hrec
  obtain ⟨rfl, rfl⟩ := pureC_ok h
  exact ⟨hs₂, hwv, F, installValue_of_facts h1 (by simpa using h2) hF h3 h4⟩

/-! ## The two-phase driver: phase B's check at the prefix view -/

/-- `annotValC` reads its index through `find?` alone (the knot and
`constsResolveFC`), so it is congruent in the index: phase B's
annotation of a theorem's value at the prefix view is the annotation
at the environment the view names. -/
theorem annotValC_congr {fe₁ fe₂ : FEnv} (hfe : fe₁.find? = fe₂.find?) :
    annotValC μ fe₁ = annotValC μ fe₂ := by
  funext cvA jty value record
  unfold annotValC
  simp only [coreKnotI_congr hfe, constsResolveFC_congr hfe]

/-- Phase B's check at the prefix view simulates the pure check half at
the environment the view names: the view and `mkFEnv env` have the same
`find?`, so by `coreKnotI_congr` the check runs the core the
simulation is stated about.  A theorem's value arrives RAW and is
annotated here (`annotValC` at the view, `annotValC_congr`), so the
well-scopedness premise on the value is asked only of the other two
kinds. -/
theorem checkPending_run (hμ : μ.verifiedChecks = true) {env : Env} (henv : EnvWF env)
    {feFinal : FEnv} {pc : PendingCheck}
    (hfind : ∀ n, (feFinal.restrictTo pc.vis).find? n = env.find? n)
    (hwty : Expr.WScoped 0 pc.vg.cvA.type)
    (hwv : pc.vg.kind ≠ .thm → Expr.WScoped 0 pc.vg.jv)
    {s₀ s' : CState} (hres : CSOKF s₀)
    (h : checkPending μ feFinal pc s₀ = .ok ((), s')) :
    CSOKF s' ∧ ∃ F, checkValueGroup (fueledOps μ F) env pc.vg = .ok () := by
  have hfe : (feFinal.restrictTo pc.vis).find? = (mkFEnv env).find? :=
    funext fun n => (hfind n).trans (mkFEnv_find? env n).symm
  unfold checkPending at h
  simp only [coreKnotI_congr hfe, opSIxC_congr hfe, annotValC_congr hfe] at h
  obtain ⟨u₀, s₁, hflush, h⟩ := bindC_ok h
  rw [flushC_run] at hflush
  injection hflush with hflush
  obtain rfl : s₀.flushed = s₁ := congrArg Prod.snd hflush
  have hcs : CSOK μ env s₀.flushed := flushC_csok hres
  obtain ⟨jsty, s₂, hst, h⟩ := bindC_ok h
  obtain ⟨hs₂, wsty, ⟨rfl, hwsty⟩, F₁, hF₁⟩ :=
    (ssimC hμ env henv checkFuel).infer hcs rfl hwty jsty s₂ hst
  obtain ⟨u, s₃, hsort, h⟩ := bindC_ok h
  obtain ⟨hs₃, u', rfl, F₂, hF₂⟩ := opSIxC_sim hμ henv hs₂ rfl hwsty u s₃ hsort
  -- the value's typing, after the theorem test (and a theorem's value
  -- install)
  have tail : ∀ {s₄ : CState} (jv : Expr), CSOK μ env s₄ → Expr.WScoped 0 jv →
      ((coreKnotI μ (mkFEnv env) checkFuel).infer 0 jv >>= fun jvt =>
        (coreKnotI μ (mkFEnv env) checkFuel).defeq 0 jvt pc.vg.cvA.type >>= fun b =>
          if b = true then pure () else
            throw (.invalid s!"type mismatch in {pc.vg.kind.word} {pc.vg.cvA.name}")) s₄
        = .ok ((), s') →
      CSOKF s' ∧ ∃ F jvt, inferTypeCore μ env F 0 jv = .ok jvt ∧
        isDefEqCore μ env F 0 jvt pc.vg.cvA.type = .ok true := by
    intro s₄ jv hs₄ hwjv h
    obtain ⟨jvt, s₅, hvt, h⟩ := bindC_ok h
    obtain ⟨hs₅, wvt, ⟨rfl, hwvt⟩, F₃, hF₃⟩ :=
      (ssimC hμ env henv checkFuel).infer hs₄ rfl hwjv jvt s₅ hvt
    obtain ⟨b, s₆, hde, h⟩ := bindC_ok h
    obtain ⟨hs₆, b', rfl, F₄, hF₄⟩ :=
      (ssimC hμ env henv checkFuel).defeq hs₅ rfl rfl hwvt hwty b s₆ hde
    cases b with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte] at h
      exact nomatch h
    | true =>
      simp only [↓reduceIte] at h
      obtain ⟨-, rfl⟩ := pureC_ok h
      exact ⟨hs₆.residue, max F₃ F₄, jvt, inferTypeCore_mono (Nat.le_max_left _ _) hF₃,
        isDefEqCore_mono (Nat.le_max_right _ _) hF₄⟩
  by_cases hk : pc.vg.kind = .thm
  · rw [if_pos hk] at h
    obtain ⟨b, s₄, hlift, h⟩ := bindC_ok h
    obtain ⟨hs₄, b', rfl, F₀, hF₀⟩ := SimC.liftFueled _ _ hs₃ b s₄ hlift
    rw [liftFueled_atF] at hF₀
    cases heqv : Level.isEquiv u .zero with
    | none => rw [heqv] at hF₀; exact nomatch hF₀
    | some b₀ =>
    rw [heqv] at hF₀
    simp only [liftFueled, pure, Except.pure, Except.ok.injEq] at hF₀
    subst hF₀
    cases b₀ with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte] at h
      exact absurd h throwC_bind_ok
    | true =>
    simp only [↓reduceIte] at h
    obtain ⟨jv, s₅, hval, h⟩ := bindC_ok h
    obtain ⟨hs₅, hwjv, F₃, hV⟩ := annotValC_run hμ henv rfl hs₄ hval
    obtain ⟨hres', F₅, jvt, hvt, hde⟩ := tail jv hs₅ hwjv h
    refine ⟨hres', max (max (max F₁ F₂) F₃) F₅, ?_⟩
    exact checkValueGroup_of_facts (jv := jv)
      (inferTypeCore_mono (by omega) hF₁)
      (ensureSortCore_mono (by omega) hF₂)
      (fun _ => heqv) (fun _ => installValue_mono (by omega) hV)
      (fun hk' => absurd hk hk')
      (inferTypeCore_mono (by omega) hvt)
      (isDefEqCore_mono (by omega) hde)
  · rw [if_neg hk] at h
    obtain ⟨hres', F₅, jvt, hvt, hde⟩ := tail _ hs₃ (hwv hk) h
    refine ⟨hres', max (max F₁ F₂) F₅, ?_⟩
    exact checkValueGroup_of_facts (jv := pc.vg.jv)
      (inferTypeCore_mono (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _)) hF₁)
      (ensureSortCore_mono (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _)) hF₂)
      (fun hk' => absurd hk' hk) (fun hk' => absurd hk' hk) (fun _ => rfl)
      (inferTypeCore_mono (Nat.le_max_right _ _) hvt)
      (isDefEqCore_mono (Nat.le_max_right _ _) hde)

/-- Phase A's value install, run: the two halves at a common fuel, the
annotated terms well scoped, the residue kept. -/
theorem annotValueC_run (hμ : μ.verifiedChecks = true) {env : Env} (henv : EnvWF env)
    {cv cvA : ConstantVal} {value jty jv : Expr} {record : Bool} {s₀ s' : CState}
    (hres : CSOKF s₀)
    (h : annotValueC μ (mkFEnv env) cv value record s₀ = .ok ((cvA, jty, jv), s')) :
    CSOKF s' ∧ cvA = { cv with type := jty } ∧ Expr.WScoped 0 jty ∧ Expr.WScoped 0 jv ∧
    ∃ F, installConstantVal (fueledOps μ F) env cv = .ok cvA ∧
      installValue (fueledOps μ F) env cvA value = .ok jv := by
  unfold annotValueC at h
  obtain ⟨u₀, s₁, hflush, h⟩ := bindC_ok h
  rw [flushC_run] at hflush
  injection hflush with hflush
  obtain rfl : s₀.flushed = s₁ := congrArg Prod.snd hflush
  obtain ⟨pr, s₂, hcv, h⟩ := bindC_ok h
  obtain ⟨cvA', jty'⟩ := pr
  obtain ⟨hs₂, hcvA, hwty, F₁, hI⟩ := annotConstantValC_run hμ henv (flushC_csok hres) hcv
  obtain ⟨jv', s₃, hv, h⟩ := bindC_ok h
  obtain ⟨hs₃, hwv, F₂, hV⟩ := annotValC_run hμ henv (by rw [hcvA]) hs₂ hv
  obtain ⟨hv, rfl⟩ := pureC_ok h
  simp only [Prod.mk.injEq] at hv
  obtain ⟨rfl, rfl, rfl⟩ := hv
  exact ⟨hs₃.residue, hcvA, hwty, hwv, max F₁ F₂,
    installConstantVal_mono (Nat.le_max_left _ _) hI, installValue_mono (Nat.le_max_right _ _) hV⟩

/-- The lookup at the prefix view of a canonical, name-unique index whose
environment extends `env` by exactly the constants above `env`'s
length is `env`'s lookup. -/
theorem restrictTo_find?_of_extends {feFinal : FEnv} {env : Env}
    (hcanon : feFinal = mkFEnv feFinal.env) (hnd : NodupNames feFinal.env)
    {new : List ConstantInfo} (hext : feFinal.env.consts = new ++ env.consts) (n : Name) :
    (feFinal.restrictTo env.consts.length).find? n = env.find? n := by
  have h1 : (feFinal.restrictTo env.consts.length).find? n
      = ((mkFEnv feFinal.env).restrictTo env.consts.length).find? n := by
    rw [← hcanon]
  rw [h1, mkFEnv_find?_visibleBelow feFinal.env env.consts.length n hnd,
    Env.prefixTo_of_extends hext]

/-! ## The model along the run -/

set_option maxHeartbeats 2000000 in
/-- **One step of the run, with the model**: the cons case of
`installRun_model`, as a lemma of its own — phase A's step at a record,
from a canonical index whose environment carries the model, leaves the
model on the environment it produces, keeps the memo residue, and *is*
a pure `checkDecl` run at some fuel.  The last conjunct is what a walk
that wants to know WHAT was installed reads
(`ConLeche/Verify/Cached/StreamConsts.lean`); `installRun_model` itself
uses only the first two.

The hypotheses about the run's final index (`q`) are the ones a
separable value declaration needs: phase A installs its header and
records the value group, and the group's own check — run at the FINAL
environment, from a fresh memo state — is what the model step consumes. -/
theorem annotStepC_model (hμ : μ.verifiedChecks = true)
    {i : Nat} {fe fe₁ : FEnv} {pend pend₁ : Array PendingCheck} {pd : Declaration}
    {s s₁ : CState} {q : Nat × FEnv × Array PendingCheck} {new₁ : List PendingCheck}
    (hfe : fe = mkFEnv fe.env) (hfe₁ : fe₁ = mkFEnv fe₁.env)
    (hm : EnvModelOk V μ fe.env) (hresA : CSOKF s)
    (hstepC : annotStepC μ pins i fe pend pd s = .ok ((fe₁, pend₁), s₁))
    (hchainF : PushChain fe₁.env q.2.1)
    (hpend₁ : q.2.2.toList = pend₁.toList ++ new₁)
    (hnd : NodupNames q.2.1.env)
    (hB : ∀ pc ∈ q.2.2.toList, ∃ s'', checkPending μ q.2.1 pc {} = .ok ((), s'')) :
    EnvModelOk V μ fe₁.env ∧ CSOKF s₁ ∧
      ∃ F, checkDecl μ (fueledOps μ F) pins fe.env pd = .ok fe₁.env := by
    obtain ⟨⟨mp⟩, hE⟩ := hm
    have henv : EnvWF fe.env := mp.toEnvFacts.wf
    -- the ordinary step: a declaration checked in full at its install
    have ordinary : ∀ (pd' : Declaration),
        (checkDeclStepC μ pins fe pd' >>= fun fe' => pure (fe', pend)) s = .ok ((fe₁, pend₁), s₁) →
        EnvModelOk V μ fe₁.env ∧ CSOKF s₁ ∧
          ∃ F, checkDecl μ (fueledOps μ F) pins fe.env pd' = .ok fe₁.env := by
      intro pd' hst
      obtain ⟨fe₁', s₁', hstepC', hp⟩ := bindC_ok hst
      obtain ⟨hv, rfl⟩ := pureC_ok hp
      simp only [Prod.mk.injEq] at hv
      obtain ⟨rfl, rfl⟩ := hv
      rw [hfe] at hstepC'
      obtain ⟨hres₁, -, F, hF⟩ := checkDeclStepC_run hμ henv hresA hstepC'
      exact ⟨declStep_preserves hμ mp hE
          (ConLeche.Semantics.checkDeclRun_ofEnvFactsE hF), hres₁, F, hF⟩
    -- a separable value declaration: phase A's install (its facts
    -- given), phase B's check at the prefix view
    have value : ∀ (kind : ValueKind) (mk : ConstantVal → Expr → ConstantInfo)
        (d : Declaration) (cvA : ConstantVal) (jv : Expr),
        pd = d →
        CSOKF s₁ →
        fe₁ = fe.push (mk cvA jv) →
        pend₁ = pend.push ⟨⟨kind, cvA, jv⟩, i, fe.visibleBelow⟩ →
        Expr.WScoped 0 cvA.type →
        (kind ≠ .thm → Expr.WScoped 0 jv) →
        (∀ F, checkValueGroup (fueledOps μ F) fe.env ⟨kind, cvA, jv⟩ = .ok () →
          ∃ F', checkDecl μ (fueledOps μ F') pins fe.env d = .ok ⟨mk cvA jv :: fe.env.consts⟩) →
        EnvModelOk V μ fe₁.env ∧ CSOKF s₁ ∧
          ∃ F, checkDecl μ (fueledOps μ F) pins fe.env pd = .ok fe₁.env := by
      intro kind mk d cvA jv hdrel hres₁ hfe₁' hpend₁' hwty hwv hsplit
      subst hfe₁' hpend₁'
      -- the record's check, from a fresh memo state
      have hmem : (⟨⟨kind, cvA, jv⟩, i, fe.visibleBelow⟩ : PendingCheck) ∈ q.2.2.toList := by
        rw [hpend₁, Array.toList_push]
        exact List.mem_append_left _ (List.mem_append_right _ (List.mem_singleton.mpr rfl))
      obtain ⟨sB, hchk⟩ := hB _ hmem
      have hvis : fe.visibleBelow = fe.env.consts.length := by
        rw [hfe]; exact mkFEnv_visibleBelow _
      have hfind : ∀ n, (q.2.1.restrictTo fe.env.consts.length).find? n = fe.env.find? n := by
        obtain ⟨newF, hnewF⟩ := hchainF.2.1
        exact restrictTo_find?_of_extends hchainF.canon hnd
          (new := newF ++ [mk cvA jv]) (by rw [hnewF, List.append_assoc]; rfl)
      obtain ⟨-, F₂, hC⟩ := checkPending_run hμ henv
        (pc := ⟨⟨kind, cvA, jv⟩, i, fe.visibleBelow⟩) (by rw [hvis]; exact hfind)
        hwty hwv CSOKF.empty hchk
      -- the two halves are the declaration's check
      obtain ⟨F', hF⟩ := hsplit F₂ hC
      have hm₁ : EnvModelOk V μ (fe.push (mk cvA jv)).env :=
        declStep_preserves hμ mp hE (ConLeche.Semantics.checkDeclRun_ofEnvFactsE hF)
      exact ⟨hm₁, hres₁, F', hdrel ▸ hF⟩
    cases pd with
    | defnDecl cv val hint =>
      unfold annotStepC at hstepC
      simp only [] at hstepC
      split at hstepC
      · exact ordinary _ hstepC
      · rename_i hnat
        obtain ⟨r, s₁', hval, hp⟩ := bindC_ok hstepC
        obtain ⟨cvA, jty, jv⟩ := r
        obtain ⟨hv, rfl⟩ := pureC_ok hp
        simp only [Prod.mk.injEq] at hv
        obtain ⟨rfl, rfl⟩ := hv
        rw [hfe] at hval
        obtain ⟨hres₁, hcvA, hwty, hwv, F₁, hI, hV⟩ := annotValueC_run hμ henv hresA hval
        refine value .defn (fun cvA jv => .defnInfo cvA jv hint)
          (.defnDecl cv val hint) cvA jv rfl
          hres₁ rfl rfl (by rw [hcvA]; exact hwty)
          (fun _ => hwv) ?_
        intro F hC
        have hnat' : (natOpNames.contains cv.name || natDivModNames.contains cv.name) = false :=
          Bool.not_eq_true _ ▸ hnat
        exact ⟨max F₁ F, checkDecl_of_split_defn hnat' rfl
          (installConstantVal_mono (Nat.le_max_left _ _) hI)
          (installValue_mono (Nat.le_max_left _ _) hV)
          (checkValueGroup_mono (Nat.le_max_right _ _) hC)⟩
    | thmDecl cv val =>
      -- phase A installed the header alone: the flush, the header's
      -- install half, the type record, the push of the RAW value
      unfold annotStepC at hstepC
      simp only [] at hstepC
      obtain ⟨u₀, s₁', hflush, h⟩ := bindC_ok hstepC
      rw [flushC_run] at hflush
      injection hflush with hflush
      obtain rfl : s.flushed = s₁' := congrArg Prod.snd hflush
      obtain ⟨pr, s₂, hcv, h⟩ := bindC_ok h
      obtain ⟨cvA, jty⟩ := pr
      rw [hfe] at hcv
      obtain ⟨hs₂, hcvA, hwty, F₁, hI⟩ :=
        annotConstantValC_run hμ henv (flushC_csok hresA) hcv
      obtain ⟨u₁, s₃, hrec, h⟩ := bindC_ok h
      obtain ⟨hs₃, -⟩ := recordCConst_eff (val := none) hs₂ (by rw [hcvA]; rfl)
        (fun _ _ hv => nomatch hv) u₁ s₃ hrec
      obtain ⟨hv, rfl⟩ := pureC_ok h
      simp only [Prod.mk.injEq] at hv
      obtain ⟨rfl, rfl⟩ := hv
      refine value .thm (fun cvA v => .thmInfo cvA v) (.thmDecl cv val) cvA val
        rfl
        hs₃.residue rfl rfl (by rw [hcvA]; exact hwty) (fun h => absurd rfl h) ?_
      intro F hC
      exact ⟨max F₁ F, checkDecl_of_split_thm rfl
        (installConstantVal_mono (Nat.le_max_left _ _) hI) rfl
        (checkValueGroup_mono (Nat.le_max_right _ _) hC)⟩
    | opaqueDecl cv val =>
      unfold annotStepC at hstepC
      simp only [] at hstepC
      split at hstepC
      · exact ordinary _ hstepC
      · rename_i hred
        obtain ⟨r, s₁', hval, hp⟩ := bindC_ok hstepC
        obtain ⟨cvA, jty, jv⟩ := r
        obtain ⟨hv, rfl⟩ := pureC_ok hp
        simp only [Prod.mk.injEq] at hv
        obtain ⟨rfl, rfl⟩ := hv
        rw [hfe] at hval
        obtain ⟨hres₁, hcvA, hwty, hwv, F₁, hI, hV⟩ := annotValueC_run hμ henv hresA hval
        refine value .opaque (fun cvA _ => .axiomInfo cvA) (.opaqueDecl cv val)
          cvA jv rfl
          hres₁ rfl rfl (by rw [hcvA]; exact hwty) (fun _ => hwv) ?_
        intro F hC
        have hred' : reduceOpNames.contains cv.name = false := Bool.not_eq_true _ ▸ hred
        exact ⟨max F₁ F, checkDecl_of_split_opaque hred' rfl
          (installConstantVal_mono (Nat.le_max_left _ _) hI)
          (installValue_mono (Nat.le_max_left _ _) hV)
          (checkValueGroup_mono (Nat.le_max_right _ _) hC)⟩
    | axiomDecl cv => unfold annotStepC at hstepC; exact ordinary _ hstepC
    | basisDecl kind => unfold annotStepC at hstepC; exact ordinary _ hstepC
    | quotDecl k cv => unfold annotStepC at hstepC; exact ordinary _ hstepC
    | indDecl block nP => unfold annotStepC at hstepC; exact ordinary _ hstepC

/-- **The model along the run**: phase A's accepting run from a
canonical index whose environment carries the model, with every record
of the final index checked from a fresh memo state, carries the model
to the final environment.  (The model at each position supplies the
well-formedness of the environment every bridge from the executable
core takes; the records' checks are consumed at the positions that
produced them.)  A theorem's record holds its RAW value: phase A
installed the header alone, and phase B's check — which annotates the
value — is what the theorem's model step consumes. -/
theorem installRun_model (hμ : μ.verifiedChecks = true) {ds : List Declaration}
    {p : Nat × FEnv × Array PendingCheck} {s : CState}
    {q : Nat × FEnv × Array PendingCheck} {s' : CState}
    (hrun : InstallRun μ pins ds p s q s') :
    p.2.1 = mkFEnv p.2.1.env → EnvModelOk V μ p.2.1.env → CSOKF s →
    NodupNames q.2.1.env →
    (∀ pc ∈ q.2.2.toList, ∃ s'', checkPending μ q.2.1 pc {} = .ok ((), s'')) →
    EnvModelOk V μ q.2.1.env := by
  induction hrun with
  | nil p s => exact fun _ hm _ _ _ => hm
  | @cons pd ds p p₁ q s s₁ s' hstep rest ih =>
    intro hfe hm hresA hnd hB
    obtain ⟨i, fe, pend⟩ := p
    obtain ⟨fe₁, pend₁, rfl, hstepC⟩ := annotDeclStep_ok hstep
    simp only at hfe hstepC
    obtain ⟨hpush₁, -⟩ :=
      annotStepC_push μ i (PushChain.self hfe) pend pd s (fe₁, pend₁) s₁ hstepC
    have hfe₁ : fe₁ = mkFEnv fe₁.env := hpush₁.canon
    obtain ⟨hchainF, new₁, hpend₁⟩ := installRun_trace μ rest (PushChain.self hfe₁)
    obtain ⟨hm₁, hres₁, -⟩ :=
      annotStepC_model hμ hfe hfe₁ hm hresA hstepC hchainF hpend₁ hnd hB
    exact ih hfe₁ hm₁ hres₁ hnd hB

/-! ## The letters on the fully checked environment -/

/-- **A fully checked environment carries the model.**  The set theory
is a hypothesis because the walk threads the model for the
well-formedness it needs; the conclusion is the model itself. -/
theorem fullyChecked_sound (V : Type w) [SetTheory V] (hμ : μ.verifiedChecks = true)
    {ds : List Declaration} (fc : FullyChecked μ pins ds) :
    Nonempty (EnvModelM V μ fc.env) := by
  obtain ⟨n, s, r⟩ := fc.1.run
  have hchain := installRun_trace μ r (PushChain.refl Env.empty)
  exact (installRun_model (V := V) hμ r rfl
    ⟨⟨EnvModelM.empty V μ⟩, EtaFamiliesClosed.empty⟩ CSOKF.empty
    (hchain.1.2.2 List.nodup_nil) fc.records).1

/-- **The letter on the fully checked environment**: such an environment, in
a validating mode, holds no constant of type `False`.  The step the main
corollary rests on (`ConLeche/MainTheorem.lean`, about `checkDecls`) is
this under `checkDecls_fullyChecked`. -/
theorem no_proof_of_False_checked (V : Type w) [SetTheory V]
    {μ : CheckMode} (hμ : μ.verifiedChecks = true) {ds : List Declaration}
    (fc : FullyChecked μ pins ds) :
    ∀ c ∈ fc.env.consts,
      c.toConstantVal.type = .const falseName [] → False := by
  obtain ⟨mp⟩ := fullyChecked_sound V hμ fc
  exact fun c hc hty => no_constant_of_False mp c hc hty

/-- The same letter about the pinned `Empty`. -/
theorem no_proof_of_Empty_checked (V : Type w) [SetTheory V]
    {μ : CheckMode} (hμ : μ.verifiedChecks = true) {ds : List Declaration}
    (fc : FullyChecked μ pins ds) :
    ∀ c ∈ fc.env.consts,
      c.toConstantVal.type = .const emptyName [] → False := by
  obtain ⟨mp⟩ := fullyChecked_sound V hμ fc
  exact fun c hc hty => no_constant_of_Empty mp c hc hty

end ConLeche.Cached
