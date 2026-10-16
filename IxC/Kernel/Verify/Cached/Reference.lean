module

public import IxC.Kernel.Verify.Cached.InstalledC
public import IxC.Kernel.Verify.BridgeDecl

public section

/-!
# The reference level: the executed fold refines the pure fold

LOCALITY §6(d4) and §7 (G7). The executed fold `Cached.checkDecls` is
proved sound by walking its install run with the model beside it, and every
step of that walk is a run of the pure declaration checker at some fuel
(`annotStepC_model`). This module keeps those runs:

* `checkDecl_mono`, `checkDeclsFrom_mono`: the pure checker is monotone in
  its fuel, read off the fueled family `checkDecl (fueledOpsM mode)`, whose
  runs are monotone by construction (`checkDecl_datF`);
* `checkDecl_deterministic`, `checkDeclsFrom_deterministic`: two accepting
  runs at any two fuels install the same environment;
* `AcceptsRef`: **reference acceptance**, the pure fold accepting at some
  fuel, where neither caches nor a fixed fuel appear;
* `installRun_ref`, `checkDecls_refines_ref`: **an accept of the executed
  fold is a reference accept of the same environment**. Like the soundness
  walk (`installRun_model`), the walk takes a set theory: the model at each
  position is what supplies the well-formedness every bridge from the
  executable core takes;
* `AcceptsRef.unique`: a reference accept determines its environment.

Later statements about the fold (renaming, locality) are stated at this
level (LOCALITY §8.4, the owner's 2026-10-16 decision on the renaming
lemma).
-/

namespace Ix.Kernel

variable {mode : CheckMode} {ev : Evidences md}

/-! ## Fuel -/

/-- **The pure declaration checker is monotone in its fuel.** -/
theorem checkDecl_mono {F F' : Nat} (hle : F ≤ F') {env env' : Env md} {d : Declaration md}
    (h : checkDecl mode (fueledOps mode F) ev env d = .ok env') :
    checkDecl mode (fueledOps mode F') ev env d = .ok env' := by
  rw [← checkDecl_datF] at h ⊢
  exact (checkDecl mode (fueledOpsM mode) ev env d).property hle h

/-- The pure fold from any environment is monotone in its fuel. -/
theorem checkDeclsFrom_mono {F F' : Nat} (hle : F ≤ F') {ds : List (Declaration md)}
    {env env' : Env md} (h : ds.foldlM (checkDecl mode (fueledOps mode F) ev) env = .ok env') :
    ds.foldlM (checkDecl mode (fueledOps mode F') ev) env = .ok env' := by
  have hF : ∀ G, (ds.foldlM (checkDecl mode (fueledOpsM mode) ev) env).val G =
      ds.foldlM (checkDecl mode (fueledOps mode G) ev) env := by
    intro G
    rw [foldlM_atF]
    simp only [checkDecl_datF]
  rw [← hF] at h ⊢
  exact (ds.foldlM (checkDecl mode (fueledOpsM mode) ev) env).property hle h

/-- **Two accepting runs of the pure checker, at any two fuels, install the
same environment.** -/
theorem checkDecl_deterministic {F₁ F₂ : Nat} {env e₁ e₂ : Env md} {d : Declaration md}
    (h₁ : checkDecl mode (fueledOps mode F₁) ev env d = .ok e₁)
    (h₂ : checkDecl mode (fueledOps mode F₂) ev env d = .ok e₂) : e₁ = e₂ := by
  have h := checkDecl_mono (Nat.le_max_left F₁ F₂) h₁
  rw [checkDecl_mono (Nat.le_max_right F₁ F₂) h₂] at h
  exact (Except.ok.inj h).symm

/-- Two accepting runs of the pure fold from one environment, at any two
fuels, install the same environment. -/
theorem checkDeclsFrom_deterministic {F₁ F₂ : Nat} {ds : List (Declaration md)}
    {env e₁ e₂ : Env md}
    (h₁ : ds.foldlM (checkDecl mode (fueledOps mode F₁) ev) env = .ok e₁)
    (h₂ : ds.foldlM (checkDecl mode (fueledOps mode F₂) ev) env = .ok e₂) : e₁ = e₂ := by
  have h := checkDeclsFrom_mono (Nat.le_max_left F₁ F₂) h₁
  rw [checkDeclsFrom_mono (Nat.le_max_right F₁ F₂) h₂] at h
  exact (Except.ok.inj h).symm

end Ix.Kernel

namespace Ix.Kernel.Cached

open Ix.Kernel Ix.Kernel.Semantics Ix.Kernel.Model

universe w
variable {μ : CheckMode} {ev : Evidences md}

/-! ## Reference acceptance -/

/-- **Reference acceptance**: the pure fold, at some fuel, accepts `ds` and
installs `env` (LOCALITY §7 (d4)). -/
def AcceptsRef (μ : CheckMode) (ev : Evidences md) (ds : List (Declaration md)) (env : Env md) :
    Prop :=
  ∃ F, checkDeclsPure μ (fueledOps μ F) ev ds = .ok env

/-- **A reference accept determines its environment.** -/
theorem AcceptsRef.unique {ds : List (Declaration md)} {env₁ env₂ : Env md}
    (h₁ : AcceptsRef μ ev ds env₁) (h₂ : AcceptsRef μ ev ds env₂) : env₁ = env₂ := by
  obtain ⟨F₁, h₁⟩ := h₁
  obtain ⟨F₂, h₂⟩ := h₂
  unfold checkDeclsPure at h₁ h₂
  exact checkDeclsFrom_deterministic h₁ h₂

/-- **The install run is a run of the pure fold**: along an accepting run
of phase A whose records all check at the final index, the pure fold at
some fuel installs the run's final environment from its first. The model
travels beside the walk, as in `installRun_model`. -/
theorem installRun_ref {V : Type w} [SetTheory V] (hμ : μ.verifiedChecks = true)
    {ds : List (Declaration md)}
    {p : Nat × FEnv md × Array (PendingCheck md)} {s : CState md}
    {q : Nat × FEnv md × Array (PendingCheck md)} {s' : CState md}
    (hrun : InstallRun μ ev ds p s q s') :
    p.2.1 = mkFEnv p.2.1.env → EnvModelOk V μ p.2.1.env →
    NodupNames q.2.1.env →
    (∀ pc ∈ q.2.2.toList, ∃ s'', checkPending μ q.2.1 pc {} = .ok ((), s'')) →
    ∃ F, ds.foldlM (checkDecl μ (fueledOps μ F) ev) p.2.1.env = .ok q.2.1.env := by
  induction hrun with
  | nil p s => exact fun _ _ _ _ => ⟨0, rfl⟩
  | @cons pd ds p p₁ q s s₁ s' hstep rest ih =>
    intro hfe hm hnd hB
    obtain ⟨i, fe, pend⟩ := p
    obtain ⟨fe₁, pend₁, rfl, hstepC⟩ := annotDeclStep_ok hstep
    simp only at hfe hstepC
    obtain ⟨hpush₁, -⟩ :=
      annotStepC_push μ i (PushChain.self hfe) pend pd s (fe₁, pend₁) s₁ hstepC
    have hfe₁ : fe₁ = mkFEnv fe₁.env := hpush₁.canon
    obtain ⟨hchainF, new₁, hpend₁⟩ := installRun_trace μ rest (PushChain.self hfe₁)
    obtain ⟨hm₁, -, F₁, hF₁⟩ :=
      annotStepC_model hμ hfe hfe₁ hm hstepC hchainF hpend₁ hnd hB
    obtain ⟨F₂, hF₂⟩ := ih hfe₁ hm₁ hnd hB
    refine ⟨max F₁ F₂, ?_⟩
    rw [List.foldlM_cons, checkDecl_mono (Nat.le_max_left F₁ F₂) hF₁]
    exact checkDeclsFrom_mono (Nat.le_max_right F₁ F₂) hF₂

/-- **The executed fold refines the reference fold** (LOCALITY §7, G7): an
accept of `Cached.checkDecls` is a reference accept of the same
environment. The set theory is a hypothesis of the walk, not of the
statement's meaning (see `installRun_ref`). -/
theorem checkDecls_refines_ref (V : Type w) [SetTheory V] (hμ : μ.verifiedChecks = true)
    {ds : Array (Declaration md)} {env : Env md} (h : checkDecls μ ev ds = .ok env) :
    AcceptsRef μ ev ds.toList env := by
  obtain ⟨fc, rfl⟩ := checkDecls_fullyChecked μ h
  obtain ⟨n, s, r⟩ := fc.1.run
  have hchain := installRun_trace μ r (PushChain.refl Env.empty)
  exact installRun_ref (V := V) hμ r rfl ⟨⟨EnvModelM.empty V μ⟩, EtaFamiliesClosed.empty⟩
    (hchain.1.2.2 List.nodup_nil) fc.records

end Ix.Kernel.Cached
