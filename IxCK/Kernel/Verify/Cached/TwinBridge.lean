module

public import IxCK.Kernel.Cached.TwinC
public import IxCK.Kernel.Verify.Inductives.TwinFuel
public import IxCK.Kernel.Verify.Inductives.TwinWF
public import IxCK.Kernel.Verify.Inductives.TwinFallback
public import IxCK.Kernel.Verify.Cached.BridgeCS4
public import IxCK.Kernel.Verify.Cached.ModeledRun

public section

/-! # Cached simulation of the stored-recursor twin phases -/

namespace Ix.Kernel.Cached

open Ix.Kernel.Semantics

variable {mode : CheckMode}

theorem twinHeaderS_sim {env : Env md} (hmode : mode.verifiedChecks = true)
    (henv : EnvWF env) {state : CState md} (hs : CSOK mode env state)
    (ci : ConstantInfo md) :
    SimC mode env state RelVC
      (NativeTwin.checkHeader (sharedOpsC mode (mkFEnv env)) env ci)
      (NativeTwin.checkHeader (fueledOpsM mode) env ci) := by
  cases ci with
  | recInfo cv mI rP rules =>
    unfold NativeTwin.checkHeader
    refine SimC.bind (checkConstantValS_sim hmode henv hs) (fun next checked checked' hnext hchecked => ?_)
    obtain ⟨rfl, _⟩ := hchecked
    by_cases hfree : letFree checked.type = true
    · simp only [if_pos hfree]
      cases hcanonical : NativeTwin.findCanonical env.find? cv checked mI rP rules env.consts with
      | none => exact SimC.throw
      | some part => exact SimC.pure hnext rfl
    · simp only [if_neg hfree]
      exact SimC.throw_bind
  | _ => exact SimC.throw

theorem twinHeadersS_sim {env : Env md} (hmode : mode.verifiedChecks = true)
    (henv : EnvWF env) : ∀ (block : List (ConstantInfo md)) {state : CState md},
    CSOK mode env state →
    SimC mode env state RelVC
      (NativeTwin.checkHeaders (sharedOpsC mode (mkFEnv env)) env block)
      (NativeTwin.checkHeaders (fueledOpsM mode) env block)
  | [], _, hs => SimC.pure hs rfl
  | ci :: block, _, hs => by
    unfold NativeTwin.checkHeaders
    refine SimC.bind (twinHeaderS_sim hmode henv hs ci) (fun next part part' hnext hpart => ?_)
    obtain rfl : part = part' := hpart
    refine SimC.bind (twinHeadersS_sim hmode henv block hnext)
      (fun final parts parts' hfinal hparts => ?_)
    obtain rfl : parts = parts' := hparts
    exact SimC.pure hfinal rfl

theorem twinPrepareS_sim {env : Env md} (hmode : mode.verifiedChecks = true)
    (henv : EnvWF env) {state : CState md} (hs : CSOK mode env state)
    (block : List (ConstantInfo md)) :
    SimC mode env state RelVC
      (NativeTwin.prepare (sharedOpsC mode (mkFEnv env)) env block)
      (NativeTwin.prepare (fueledOpsM mode) env block) := by
  unfold NativeTwin.prepare
  by_cases hempty : block.isEmpty = true
  · simp only [if_pos hempty]
    exact SimC.throw_bind
  · simp only [if_neg hempty]
    refine SimC.bind (twinHeadersS_sim hmode henv block hs)
      (fun next parts parts' hnext hparts => ?_)
    obtain rfl : parts = parts' := hparts
    by_cases hdistinct : ((NativeTwin.provision parts ++ NativeTwin.models parts).map (·.name)).Nodup
    · simp only [if_pos hdistinct]
      by_cases hfresh : (NativeTwin.provision parts ++ NativeTwin.models parts).all
          (fun ci => (env.find? ci.name).isNone) = true
      · simp only [if_pos hfresh]
        exact SimC.pure hnext rfl
      · simp only [if_neg hfresh]
        exact SimC.throw_bind
    · simp only [if_neg hdistinct]
      exact SimC.throw_bind

theorem twinRuleS_sim {checking : Env md} (hmode : mode.verifiedChecks = true)
    (henv : EnvWF checking) {state : CState md} (hs : CSOK mode checking state)
    (base : Env md) (part : NativeTwin.Part md) (raw canonical : RecRule md) :
    SimC mode checking state RelVC
      (NativeTwin.checkRule (sharedOpsC mode (mkFEnv checking)) base checking part raw canonical)
      (NativeTwin.checkRule (fueledOpsM mode) base checking part raw canonical) := by
  unfold NativeTwin.checkRule
  dsimp only [sharedOpsC]
  by_cases hmeta : (raw.ctor == canonical.ctor && raw.nfields == canonical.nfields) = true
  · simp only [if_pos hmeta]
    by_cases hraw : (raw.rhs.looseBVarsBounded 0 && !raw.rhs.hasFvar) = true
    · simp only [if_pos hraw]
      have hfree : raw.rhs.hasFvar = false := by
        have h := (Bool.and_eq_true_iff.mp hraw).2
        simpa only [Bool.not_eq_true'] using h
      refine SimC.bind (opE_annotate_sim hmode henv hs (Expr.WScoped.of_not_hasFvar hfree))
        (fun next rhs rhs' hnext hrhs => ?_)
      obtain ⟨rfl, _⟩ := hrhs
      by_cases hscope : (rhs.allLevelParamsDefined part.canonical.levelParams &&
          rhs.constsResolve checking && letFree rhs) = true
      · simp only [if_pos hscope]
        by_cases hshape : NativeTwin.ruleShape base part canonical = true
        · simp only [if_pos hshape]
          exact SimC.pure hnext rfl
        · simp only [if_neg hshape]
          exact SimC.throw_bind
      · simp only [if_neg hscope]
        exact SimC.throw_bind
    · simp only [if_neg hraw]
      exact SimC.throw_bind
  · simp only [if_neg hmeta]
    exact SimC.throw_bind

theorem twinRulesS_sim {checking : Env md} (hmode : mode.verifiedChecks = true)
    (henv : EnvWF checking) (base : Env md) (part : NativeTwin.Part md) :
    ∀ (raws canonicals : List (RecRule md)) {state : CState md}, CSOK mode checking state →
      SimC mode checking state RelVC
        (NativeTwin.checkRules (sharedOpsC mode (mkFEnv checking)) base checking part raws canonicals)
        (NativeTwin.checkRules (fueledOpsM mode) base checking part raws canonicals)
  | [], [], _, hs => SimC.pure hs rfl
  | [], _ :: _, _, _ => SimC.throw
  | _ :: _, [], _, _ => SimC.throw
  | raw :: raws, canonical :: canonicals, _, hs => by
    unfold NativeTwin.checkRules
    refine SimC.bind (twinRuleS_sim hmode henv hs base part raw canonical)
      (fun next rule rule' hnext hrule => ?_)
    obtain rfl : rule = rule' := hrule
    refine SimC.bind (twinRulesS_sim hmode henv base part raws canonicals hnext)
      (fun final rules rules' hfinal hrules => ?_)
    obtain rfl : rules = rules' := hrules
    exact SimC.pure hfinal rfl

theorem twinPartsRulesS_sim {checking : Env md} (hmode : mode.verifiedChecks = true)
    (henv : EnvWF checking) (base : Env md) :
    ∀ (parts : List (NativeTwin.Part md)) {state : CState md}, CSOK mode checking state →
      SimC mode checking state RelVC
        (NativeTwin.checkPartsRules (sharedOpsC mode (mkFEnv checking)) base checking parts)
        (NativeTwin.checkPartsRules (fueledOpsM mode) base checking parts)
  | [], _, hs => SimC.pure hs rfl
  | part :: parts, _, hs => by
    unfold NativeTwin.checkPartsRules
    refine SimC.bind (twinRulesS_sim hmode henv base part part.rawRules part.canonicalRules hs)
      (fun next rules rules' hnext hrules => ?_)
    obtain rfl : rules = rules' := hrules
    refine SimC.bind (twinPartsRulesS_sim hmode henv base parts hnext)
      (fun final rest rest' hfinal hrest => ?_)
    obtain rfl : rest = rest' := hrest
    exact SimC.pure hfinal rfl

theorem twinFinishS_sim {checking : Env md} {state : CState md}
    (hs : CSOK mode checking state) (base : Env md) (parts : List (NativeTwin.Part md)) :
    SimC mode checking state RelVC
      (NativeTwin.finish (m := CheckCM md) base parts) (NativeTwin.finish (m := FueledM md) base parts) := by
  unfold NativeTwin.finish
  by_cases hwrap : (NativeTwin.rulesWrap base id parts ||
      NativeTwin.rulesWrap base (NativeTwin.peerRename parts) parts) = true
  · simp only [if_pos hwrap]
    exact SimC.pure hs rfl
  · simp only [if_neg hwrap]
    exact SimC.throw_bind

/-- The complete cached twin driver refines a pure run at one common fuel. Its header
and rule phases use their own actual environment indices, with a flush at each transition. -/
theorem checkTwinS_run {env : Env md} (hmode : mode.verifiedChecks = true)
    (henv : EnvWF env) {state : CState md} (hs : CSOKF state)
    {block : List (ConstantInfo md)} {output : FEnv md} {final : CState md}
    (h : checkTwinS mode (mkFEnv env) block state = .ok (output, final)) :
    CSOKF final ∧ output = mkFEnv output.env ∧
      ∃ fuel, NativeTwin.check (fueledOps mode fuel) env block = .ok output.env := by
  unfold checkTwinS at h
  simp only [mkFEnv_env] at h
  obtain ⟨_, start, hflush, h⟩ := bindC_ok h
  rw [flushC_run] at hflush
  have hstart : state.flushed = start := congrArg Prod.snd (Except.ok.inj hflush)
  subst start
  obtain ⟨parts, headersState, hprepare, h⟩ := bindC_ok h
  obtain ⟨hheaders, parts', hparts, headerFuel, hheaderRun⟩ :=
    twinPrepareS_sim hmode henv (flushC_csok hs) block parts headersState hprepare
  obtain rfl : parts = parts' := hparts
  have hpureHeader : NativeTwin.prepare (fueledOps mode headerFuel) env block = .ok parts := by
    simpa only [NativeTwin.prepare_datF] using hheaderRun
  have hself := NativeTwin.prepare_self_wf henv hpureHeader
  obtain ⟨_, rulesStart, hflush, h⟩ := bindC_ok h
  rw [flushC_run] at hflush
  have hrulesStart : headersState.flushed = rulesStart := congrArg Prod.snd (Except.ok.inj hflush)
  subst rulesStart
  obtain ⟨checked, rulesState, hrules, h⟩ := bindC_ok h
  obtain ⟨hcheckedState, checked', hchecked, ruleFuel, hruleRun⟩ :=
    twinPartsRulesS_sim hmode hself env parts (flushC_csok hheaders.residue)
      checked rulesState hrules
  obtain rfl : checked = checked' := hchecked
  obtain ⟨result, finishState, hfinish, h⟩ := bindC_ok h
  obtain ⟨hfinishState, result', hresult, finishFuel, hfinishRun⟩ :=
    twinFinishS_sim hcheckedState env checked result finishState hfinish
  obtain rfl : result = result' := hresult
  obtain ⟨_, last, hflush, h⟩ := bindC_ok h
  rw [flushC_run] at hflush
  have hlast : finishState.flushed = last := congrArg Prod.snd (Except.ok.inj hflush)
  subst last
  obtain ⟨houtput, hfinal⟩ := pureC_ok h
  subst output
  subst final
  refine ⟨hfinishState.residue.flushed, ?_, max headerFuel (max ruleFuel finishFuel), ?_⟩
  · rw [mkFEnv_env]
  · rw [mkFEnv_env, ← NativeTwin.check_datF]
    unfold NativeTwin.check
    exact atF_bind_intro hheaderRun (atF_bind_intro hruleRun hfinishRun)

/-- The cached choice preserves modeled successes and refines the structural pure
choice. A failed attempt cannot smuggle a provisional environment into the fallback. -/
theorem checkTwinOrModeledS_run {env : Env md} (hmode : mode.verifiedChecks = true)
    (henv : EnvWF env) {state : CState md} (hs : CSOKF state)
    {block : List (ConstantInfo md)} {output : FEnv md} {final : CState md}
    (h : checkTwinOrModeledS mode (mkFEnv env) block state = .ok (output, final)) :
    CSOKF final ∧ output = mkFEnv output.env ∧
      ∃ fuel, (if NativeTwin.usesStoredRecursors env.find? block then
        NativeTwin.check (fueledOps mode fuel) env block
        else checkModeled mode (fueledOps mode fuel) env block) = .ok output.env := by
  unfold checkTwinOrModeledS at h
  have lookup : (mkFEnv env).find? = env.find? := by
    funext name
    simp only [mkFEnv_find?]
  rw [lookup] at h
  by_cases selected : NativeTwin.usesStoredRecursors env.find? block = true
  · rw [if_pos selected] at h
    cases htwin : checkTwinS mode (mkFEnv env) block state with
    | ok result =>
      rw [htwin] at h
      have hresult : result = (output, final) := Except.ok.inj h
      rw [hresult] at htwin
      obtain ⟨hstate, houtput, fuel, hrun⟩ := checkTwinS_run hmode henv hs htwin
      exact ⟨hstate, houtput, fuel, by rw [if_pos selected]; exact hrun⟩
    | error reason =>
      rw [htwin] at h
      obtain ⟨_, restarted, hflush, hmodeled⟩ := bindC_ok h
      rw [flushC_run] at hflush
      have hrestart : state.flushed = restarted := congrArg Prod.snd (Except.ok.inj hflush)
      subst restarted
      obtain ⟨_, _, fuel, hrun⟩ := checkIndDeclSF_run hmode henv hs.flushed hmodeled
      have incompatible := NativeTwin.modeled_not_usesStoredRecursors hrun
      rw [selected] at incompatible
      cases incompatible
  · rw [if_neg selected] at h
    obtain ⟨hstate, houtput, fuel, hrun⟩ := checkIndDeclSF_run hmode henv hs h
    exact ⟨hstate, houtput, fuel, by rw [if_neg selected]; exact hrun⟩

end Ix.Kernel.Cached
