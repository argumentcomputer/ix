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
had no such policy. This module gives it one, by the same rule:

* `checkUserAxiomDecl`: the user arm of the pure fold
  (`Cached.checkUserAxiomDeclC` without the caches);
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
(`checkConstantVal`) and the axiom installed as `.axiomInfo`, unless its type
restates an axiom role's pinned specification (`Cached.axiomRoleSpecHit?`),
which declines. `Cached.checkUserAxiomDeclC` without the caches. -/
def checkUserAxiomDecl (ops : (CheckerOps md) m) (env : Env md) (cv : ConstantVal md) :
    m (Env md) := do
  let cvA ← checkConstantVal ops env cv
  match Cached.axiomRoleSpecHit? cvA with
  | some _ => throw (.notImplemented "user axiom restates the specification of an unbound axiom role")
  | none => pure ⟨.axiomInfo cvA :: env.consts⟩

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
    unfold checkDeclUnder
    rw [ha]
    rfl
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

namespace Cached

/-- **Reference acceptance under an axiom policy**: the pure fold under
`policy`, at some fuel, accepts `ds` and installs `env`. At `allowUser` an
accept is conditional on the user axioms of `ds` (`userAxiomsOfDecls`). -/
def AcceptsRefUnder (policy : AxiomPolicy) (μ : CheckMode) (ev : Evidences md)
    (ds : List (Declaration md)) (env : Env md) : Prop :=
  ∃ F, checkDeclsPureUnder μ policy (fueledOps μ F) ev ds = .ok env

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
