module

public import IxC.Kernel.Verify.Cached.Reference
public import IxC.Kernel.Cached.Policy

@[expose] public section

/-!
# Reference acceptance under an axiom policy

The cached fold admits user axioms under the policy `allowUser`
(`Cached.checkDeclsUnder`, `IxC/Kernel/Cached/Policy.lean`): at an
`.axiomDecl` under an eligible key it checks the header and type, declines a
type that restates an axiom role's pinned specification, and installs the
axiom. Reference acceptance (`Cached.AcceptsRef`, the pure fold at some fuel)
had no such policy. This module gives it one:

* `checkUserAxiomDecl`: the user arm of the pure fold
  (`checkConstantVal`, then install as `.axiomInfo`);
* `checkDeclUnder`, `checkDeclsPureUnder`: `checkDecl` and `checkDeclsPure`
  with that arm at a key the policy admits (`Cached.AxiomPolicy.admits`);
* `Cached.AcceptsRefUnder policy`: the pure fold under `policy` at some fuel.

The facts proved here are the cheap ones:

* at `strict` it is `AcceptsRef` (`acceptsRefUnder_strict`);
* at every policy, over declarations with no user axiom
  (`userAxiomsOfDecls ds = []`) it is `AcceptsRef`
  (`acceptsRefUnder_iff_of_nil`), the reference twin of
  `Cached.checkDeclsUnder_eq_checkDecls`.

An accept that installs user axioms is conditional on them. No model is
claimed for it here; that, and the refinement of the cached fold under
`allowUser` by this one, are later work.
-/

namespace Ix.Kernel

variable {m : Type → Type} [Monad m] [MonadExcept (CheckError md) m]

/-- **The pure fold's user axiom arm**: the header and type checked
(`checkConstantVal`) and the axiom installed as `.axiomInfo`. -/
def checkUserAxiomDecl (ops : (CheckerOps md) m) (env : Env md) (cv : ConstantVal md) :
    m (Env md) := do
  let cvA ← checkConstantVal ops env cv
  pure ⟨.axiomInfo cvA :: env.consts⟩

/-- **The pure declaration checker under an axiom policy**: `checkDecl`, with
the user arm at an `.axiomDecl` whose key the policy admits. -/
def checkDeclUnder (mode : CheckMode) (policy : Cached.AxiomPolicy) (ops : (CheckerOps md) m)
    (ev : Evidences md) (env : Env md) (d : Declaration md) : m (Env md) :=
  match d with
  | .axiomDecl cv =>
    if policy.admits cv.name then checkUserAxiomDecl ops env cv else checkDecl mode ops ev env d
  | _ => checkDecl mode ops ev env d

/-- **The pure fold under an axiom policy**, from the empty environment. -/
def checkDeclsPureUnder (mode : CheckMode) (policy : Cached.AxiomPolicy) (ops : (CheckerOps md) m)
    (ev : Evidences md) (ds : List (Declaration md)) : m (Env md) :=
  ds.foldlM (checkDeclUnder mode policy ops ev) Env.empty

theorem checkDeclUnder_strict (mode : CheckMode) (ops : (CheckerOps md) m) (ev : Evidences md)
    (env : Env md) (d : Declaration md) :
    checkDeclUnder mode .strict ops ev env d = checkDecl mode ops ev env d := by
  cases d <;> rfl

/-- A declaration that is no user axiom is checked by `checkDecl`, at every
policy. -/
theorem checkDeclUnder_of_userAxiom?_none (mode : CheckMode) (policy : Cached.AxiomPolicy)
    (ops : (CheckerOps md) m) (ev : Evidences md) (env : Env md) {d : Declaration md}
    (h : d.userAxiom? = none) :
    checkDeclUnder mode policy ops ev env d = checkDecl mode ops ev env d := by
  cases d
  case axiomDecl cv =>
    have he : cv.name.isCustomAxiomEligible = false := by
      cases hk : cv.name.isCustomAxiomEligible with
      | false => rfl
      | true => simp [Declaration.userAxiom?, hk] at h
    have ha : policy.admits cv.name = false := Cached.AxiomPolicy.admits_of_not_eligible policy he
    simp [checkDeclUnder, ha]
  all_goals rfl

theorem checkDeclsPureUnder_strict (mode : CheckMode) (ops : (CheckerOps md) m)
    (ev : Evidences md) (ds : List (Declaration md)) :
    checkDeclsPureUnder mode .strict ops ev ds = checkDeclsPure mode ops ev ds := by
  have h : checkDeclUnder mode .strict ops ev = checkDecl mode ops ev :=
    funext fun env => funext fun d => checkDeclUnder_strict mode ops ev env d
  unfold checkDeclsPureUnder checkDeclsPure
  rw [h]

theorem foldlM_checkDeclUnder_of_nil (mode : CheckMode) (policy : Cached.AxiomPolicy)
    (ops : (CheckerOps md) m) (ev : Evidences md) :
    ∀ (ds : List (Declaration md)) (env : Env md), userAxiomsOfDecls ds = [] →
      ds.foldlM (checkDeclUnder mode policy ops ev) env = ds.foldlM (checkDecl mode ops ev) env
  | [], _, _ => rfl
  | d :: ds, env, hnone => by
    cases hd : d.userAxiom? with
    | some cv => simp [userAxiomsOfDecls, hd] at hnone
    | none =>
      have hds : userAxiomsOfDecls ds = [] := by simpa [userAxiomsOfDecls, hd] using hnone
      rw [List.foldlM_cons, List.foldlM_cons,
        checkDeclUnder_of_userAxiom?_none mode policy ops ev env hd]
      congr 1
      funext e
      exact foldlM_checkDeclUnder_of_nil mode policy ops ev ds e hds

/-- With no user axiom among the declarations, the fold is `checkDeclsPure` at
every policy. -/
theorem checkDeclsPureUnder_of_nil (mode : CheckMode) (policy : Cached.AxiomPolicy)
    (ops : (CheckerOps md) m) (ev : Evidences md) {ds : List (Declaration md)}
    (hnone : userAxiomsOfDecls ds = []) :
    checkDeclsPureUnder mode policy ops ev ds = checkDeclsPure mode ops ev ds :=
  foldlM_checkDeclUnder_of_nil mode policy ops ev ds Env.empty hnone

/-! ## Fuel monotonicity, determinism and composition -/

theorem checkUserAxiomDecl_datF {mode : CheckMode} (env : Env md) (cv : ConstantVal md) (F : Nat) :
    (checkUserAxiomDecl (fueledOpsM mode) env cv).val F =
      checkUserAxiomDecl (fueledOps mode F) env cv := by
  unfold checkUserAxiomDecl
  rw [FueledM.atF_bind, checkConstantVal_datF]
  rfl

theorem checkDeclUnder_datF {mode : CheckMode} {policy : Cached.AxiomPolicy} {ev : Evidences md}
    (env : Env md) (d : Declaration md) (F : Nat) :
    (checkDeclUnder mode policy (fueledOpsM mode) ev env d).val F =
      checkDeclUnder mode policy (fueledOps mode F) ev env d := by
  unfold checkDeclUnder
  cases d with
  | axiomDecl cv =>
    dsimp only
    split
    · exact checkUserAxiomDecl_datF env cv F
    · exact checkDecl_datF env (.axiomDecl cv) F
  | _ => exact checkDecl_datF env _ F

/-- **The pure user-axiom arm is monotone in its fuel.** -/
theorem checkUserAxiomDecl_mono {mode : CheckMode} {F F' : Nat} (hle : F ≤ F')
    {env env' : Env md} {cv : ConstantVal md}
    (h : checkUserAxiomDecl (fueledOps mode F) env cv = .ok env') :
    checkUserAxiomDecl (fueledOps mode F') env cv = .ok env' := by
  rw [← checkUserAxiomDecl_datF] at h ⊢
  exact (checkUserAxiomDecl (fueledOpsM mode) env cv).property hle h

/-- **The pure declaration checker under any axiom policy is monotone in its
fuel.** -/
theorem checkDeclUnder_mono {mode : CheckMode} {policy : Cached.AxiomPolicy} {ev : Evidences md}
    {F F' : Nat} (hle : F ≤ F') {env env' : Env md} {d : Declaration md}
    (h : checkDeclUnder mode policy (fueledOps mode F) ev env d = .ok env') :
    checkDeclUnder mode policy (fueledOps mode F') ev env d = .ok env' := by
  rw [← checkDeclUnder_datF] at h ⊢
  exact (checkDeclUnder mode policy (fueledOpsM mode) ev env d).property hle h

/-- **The pure fold under any axiom policy, from any environment, is monotone
in its fuel.** -/
theorem checkDeclsFromUnder_mono {mode : CheckMode} {policy : Cached.AxiomPolicy} {ev : Evidences md}
    {F F' : Nat} (hle : F ≤ F') {ds : List (Declaration md)} {env env' : Env md}
    (h : ds.foldlM (checkDeclUnder mode policy (fueledOps mode F) ev) env = .ok env') :
    ds.foldlM (checkDeclUnder mode policy (fueledOps mode F') ev) env = .ok env' := by
  have hF : ∀ G, (ds.foldlM (checkDeclUnder mode policy (fueledOpsM mode) ev) env).val G =
      ds.foldlM (checkDeclUnder mode policy (fueledOps mode G) ev) env := by
    intro G
    rw [foldlM_atF]
    simp only [checkDeclUnder_datF]
  rw [← hF] at h ⊢
  exact (ds.foldlM (checkDeclUnder mode policy (fueledOpsM mode) ev) env).property hle h

theorem checkDeclsPureUnder_mono {mode : CheckMode} {policy : Cached.AxiomPolicy} {ev : Evidences md}
    {F F' : Nat} (hle : F ≤ F') {ds : List (Declaration md)} {env : Env md}
    (h : checkDeclsPureUnder mode policy (fueledOps mode F) ev ds = .ok env) :
    checkDeclsPureUnder mode policy (fueledOps mode F') ev ds = .ok env :=
  checkDeclsFromUnder_mono hle h

/-- **Two accepting runs of `checkDeclUnder`, at any two fuels, install the
same environment.** -/
theorem checkDeclUnder_deterministic {mode : CheckMode} {policy : Cached.AxiomPolicy}
    {ev : Evidences md} {F₁ F₂ : Nat} {env e₁ e₂ : Env md} {d : Declaration md}
    (h₁ : checkDeclUnder mode policy (fueledOps mode F₁) ev env d = .ok e₁)
    (h₂ : checkDeclUnder mode policy (fueledOps mode F₂) ev env d = .ok e₂) : e₁ = e₂ := by
  have h := checkDeclUnder_mono (Nat.le_max_left F₁ F₂) h₁
  rw [checkDeclUnder_mono (Nat.le_max_right F₁ F₂) h₂] at h
  exact (Except.ok.inj h).symm

/-- **Two accepting runs of the pure fold under any policy, at any two fuels,
install the same environment.** -/
theorem checkDeclsFromUnder_deterministic {mode : CheckMode} {policy : Cached.AxiomPolicy}
    {ev : Evidences md} {F₁ F₂ : Nat} {ds : List (Declaration md)} {env e₁ e₂ : Env md}
    (h₁ : ds.foldlM (checkDeclUnder mode policy (fueledOps mode F₁) ev) env = .ok e₁)
    (h₂ : ds.foldlM (checkDeclUnder mode policy (fueledOps mode F₂) ev) env = .ok e₂) : e₁ = e₂ := by
  have h := checkDeclsFromUnder_mono (Nat.le_max_left F₁ F₂) h₁
  rw [checkDeclsFromUnder_mono (Nat.le_max_right F₁ F₂) h₂] at h
  exact (Except.ok.inj h).symm

/-- **Stepping the pure fold under an axiom policy** by one declaration at its
own fuel. -/
theorem checkDeclsFromUnder_cons {mode : CheckMode} {policy : Cached.AxiomPolicy}
    {ev : Evidences md} {F₁ F₂ : Nat} {d : Declaration md} {ds : List (Declaration md)}
    {env₀ env₁ env₂ : Env md}
    (h₁ : checkDeclUnder mode policy (fueledOps mode F₁) ev env₀ d = .ok env₁)
    (h₂ : ds.foldlM (checkDeclUnder mode policy (fueledOps mode F₂) ev) env₁ = .ok env₂) :
    (d :: ds).foldlM (checkDeclUnder mode policy (fueledOps mode (max F₁ F₂)) ev) env₀ = .ok env₂ := by
  rw [List.foldlM_cons, checkDeclUnder_mono (Nat.le_max_left F₁ F₂) h₁]
  exact checkDeclsFromUnder_mono (Nat.le_max_right F₁ F₂) h₂

/-- **Composing two fuel-bounded declaration segments** under an axiom policy
at `max F₁ F₂`. -/
theorem checkDeclsFromUnder_append {mode : CheckMode} {policy : Cached.AxiomPolicy}
    {ev : Evidences md} {F₁ F₂ : Nat} {ds₁ ds₂ : List (Declaration md)}
    {env₀ env₁ env₂ : Env md}
    (h₁ : ds₁.foldlM (checkDeclUnder mode policy (fueledOps mode F₁) ev) env₀ = .ok env₁)
    (h₂ : ds₂.foldlM (checkDeclUnder mode policy (fueledOps mode F₂) ev) env₁ = .ok env₂) :
    (ds₁ ++ ds₂).foldlM (checkDeclUnder mode policy (fueledOps mode (max F₁ F₂)) ev) env₀ = .ok env₂ := by
  rw [List.foldlM_append, checkDeclsFromUnder_mono (Nat.le_max_left F₁ F₂) h₁]
  exact checkDeclsFromUnder_mono (Nat.le_max_right F₁ F₂) h₂

namespace Cached

/-- **Reference acceptance under an axiom policy**: the pure fold under
`policy`, at some fuel, accepts `ds` and installs `env`. At `allowUser` an
accept is conditional on the user axioms of `ds` (`userAxiomsOfDecls`). -/
def AcceptsRefUnder (policy : AxiomPolicy) (μ : CheckMode) (ev : Evidences md)
    (ds : List (Declaration md)) (env : Env md) : Prop :=
  ∃ F, checkDeclsPureUnder μ policy (fueledOps μ F) ev ds = .ok env

/-- **A reference accept under any policy determines its environment.** -/
theorem AcceptsRefUnder.unique {policy : AxiomPolicy} {μ : CheckMode} {ev : Evidences md}
    {ds : List (Declaration md)} {env₁ env₂ : Env md}
    (h₁ : AcceptsRefUnder policy μ ev ds env₁)
    (h₂ : AcceptsRefUnder policy μ ev ds env₂) : env₁ = env₂ := by
  obtain ⟨F₁, h₁⟩ := h₁
  obtain ⟨F₂, h₂⟩ := h₂
  unfold checkDeclsPureUnder at h₁ h₂
  exact checkDeclsFromUnder_deterministic h₁ h₂

/-- **At `strict`, reference acceptance under the policy is `AcceptsRef`.** -/
theorem acceptsRefUnder_strict {μ : CheckMode} {ev : Evidences md} {ds : List (Declaration md)}
    {env : Env md} : AcceptsRefUnder .strict μ ev ds env ↔ AcceptsRef μ ev ds env := by
  rw [AcceptsRef.iff]
  unfold AcceptsRefUnder
  simp only [checkDeclsPureUnder_strict]

/-- **With no user axioms, reference acceptance under any policy is
`AcceptsRef`.** -/
theorem acceptsRefUnder_iff_of_nil {policy : AxiomPolicy} {μ : CheckMode} {ev : Evidences md}
    {ds : List (Declaration md)} {env : Env md} (hnone : userAxiomsOfDecls ds = []) :
    AcceptsRefUnder policy μ ev ds env ↔ AcceptsRef μ ev ds env := by
  rw [AcceptsRef.iff]
  unfold AcceptsRefUnder
  simp only [checkDeclsPureUnder_of_nil μ policy _ ev hnone]

end Cached

end Ix.Kernel
