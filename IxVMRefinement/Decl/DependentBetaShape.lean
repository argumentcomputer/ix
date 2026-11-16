import IxVMRefinement.Decl.DependentBetaFrame
import IxVMRefinement.Decl.IdentityRefShape

/-! # Covariant reference shape through an actual identity-beta reduction

The reference is tracked explicitly through substitution and abstraction; it is not assumed
to keep an arbitrary replacement's type. Kernel evaluation of an identity redex at an opened
variable either returns that variable or leaves the same redex. This supplies the operational
part of connecting the local typed-frame lemma through closing and reopening.
-/

namespace IxVM.Refinement.Decl

open Ix.Kernel

private theorem variable_core {md : Mode} {env : Env md} {fuel depth index : Nat} {type out : Expr md}
    (run : whnfCore .verified env fuel depth (.fvar index type) = .ok out) : out = .fvar index type := by
  cases fuel with
  | zero => cases run
  | succ fuel => exact (Except.ok.inj run).symm

private theorem identity_core {md : Mode} {env : Env md} {fuel depth : Nat} {level : Level}
    {metadata : BinderMeta} {out : Expr md}
    (run : whnfCore .verified env fuel depth (.lam (.sort level) (.bvar 0) metadata) = .ok out) :
    out = .lam (.sort level) (.bvar 0) metadata := by
  cases fuel with
  | zero => cases run
  | succ fuel => exact (Except.ok.inj run).symm

/-- The actual core run exposes only the returned variable or the unchanged identity redex. -/
theorem IdentityRef.whnfCore {md : Mode} {env : Env md} {fuel depth index : Nat}
    {domainSort : Level} {type e out : Expr md} (shape : IdentityRef domainSort (.fvar index type) e)
    (run : Ix.Kernel.whnfCore .verified env fuel depth e = .ok out) :
    IdentityRef domainSort (.fvar index type) out := by
  cases shape with
  | reference => rw [variable_core run]; exact .reference
  | @beta metadata =>
    cases fuel with
    | zero => cases run
    | succ fuel =>
      obtain ⟨functionExpr, functionRun, branches⟩ := whnf_app_inv run
      obtain rfl := identity_core functionRun
      rcases branches with ⟨domain, body, lambdaMeta, same, bodyRun, _⟩ | ⟨result, iota, _⟩ | same
      · obtain ⟨rfl, rfl, rfl⟩ := Expr.lam.inj same
        simp only [Expr.instantiate1, ↓reduceIte] at bodyRun
        rw [variable_core bodyRun]
        exact .reference
      · have impossible : iotaRecFueled .verified env fuel depth
            (.app (.lam (.sort domainSort) (.bvar 0) metadata) (.fvar index type)) = .ok none := rfl
        rw [impossible] at iota
        cases iota
      · rw [same]
        exact .beta

private theorem IdentityRef.noNat {md : Mode} {env : Env md} {fuel depth index : Nat}
    {domainSort : Level} {type e : Expr md} (shape : IdentityRef domainSort (.fvar index type) e) :
    reduceNatFueled .verified env fuel depth e = .ok none := by cases shape <;> rfl

private theorem IdentityRef.noDelta {md : Mode} {env : Env md} {index : Nat}
    {domainSort : Level} {type e : Expr md} (shape : IdentityRef domainSort (.fvar index type) e) :
    unfoldDefinition env e = none := by cases shape <;> rfl

/-- Actual weak-head evaluation keeps this same variable reference; no opaque-head rule is assumed. -/
theorem IdentityRef.whnf {md : Mode} {env : Env md} {fuel depth index : Nat}
    {domainSort : Level} {type e out : Expr md} (shape : IdentityRef domainSort (.fvar index type) e)
    (run : Ix.Kernel.whnf .verified env fuel depth e = .ok out) :
    IdentityRef domainSort (.fvar index type) out := by
  cases fuel with
  | zero => cases run
  | succ fuel =>
    rw [whnf_succ] at run
    change whnfLoop (pureFns .verified env fuel) env depth whnfLoopFuel e = .ok out at run
    obtain ⟨budget, positive⟩ := whnfLoopFuel_succ
    rw [positive] at run
    obtain ⟨head, coreRun, branches⟩ := whnfStep_inv run
    have headShape := shape.whnfCore coreRun
    rcases branches with ⟨next, natural, _⟩ | ⟨_, next, unfolded, _⟩ | ⟨_, _, same⟩
    · rw [headShape.noNat] at natural
      cases natural
    · rw [headShape.noDelta] at unfolded
      cases unfolded
    · rw [same]
      exact headShape

/-- The real domain normalizer preserves the selected original reference until reclosing. -/
theorem IdentityRef.normalized {md : Mode} {env : Env md} {fuel steps depth index : Nat}
    {T : Key md} {domainSort : Level} {type e out : Expr md}
    (shape : IdentityRef domainSort (.fvar index type) e)
    (run : normPosDom (fueledOps .verified fuel) env T depth steps e = .ok out) :
    IdentityRef domainSort (.fvar index type) out := by
  cases steps with
  | zero => cases run
  | succ steps =>
    simp only [normPosDom] at run
    split at run
    · obtain rfl := (Except.ok.inj run).symm
      exact shape
    · obtain ⟨head, reduced, rest⟩ := exceptBind_ok run
      change Ix.Kernel.whnf .verified env fuel depth e = .ok head at reduced
      have headShape := shape.whnf reduced
      split at rest
      · obtain rfl := (Except.ok.inj rest).symm
        exact headShape
      · cases head with
        | forallE => cases headShape
        | _ =>
          obtain rfl := (Except.ok.inj rest).symm
          exact headShape

/-- The actual application check also fixes the identity lambda's binder datum. -/
theorem infer_identity_metadata {md : Mode} {env : Env md} {depth : Nat} {domainSort : Level}
    {argument inferred : Expr md} {metadata : BinderMeta}
    (typed : Rules.Infer env .full depth (.app (.lam (.sort domainSort) (.bvar 0) metadata) argument) inferred) :
    metadata.pw = .never := by
  obtain ⟨_, _, _, _, _, functionTyped, _, _, _, _⟩ := Rules.Infer.app_inv typed
  cases functionTyped with
  | lam _ _ bodyTyped _ typeTyped typeSorted metadataEq =>
    simp only [Expr.instantiate1, ↓reduceIte] at bodyTyped
    have bodyType := Rules.Infer.fvar_inv bodyTyped
    have typeCheck := typeTyped rfl
    rw [bodyType] at typeCheck
    have inferredType := Rules.Infer.sort_inv typeCheck
    have reduced := typeSorted rfl
    rw [inferredType] at reduced
    have levelEq := Rules.Red.sort_eq reduced
    have datum := metadataEq rfl
    rw [levelEq] at datum
    exact datum.symm

/-- The local typed-frame result covers both possible outcomes of actual normalization. -/
theorem SortKindPair.identity_result {env : Env .anon} {fuel index depth : Nat}
    {original final result inputType outputType : Expr .anon}
    {kind domainSort inputSort outputSort : Level} {metadata : BinderMeta}
    (pair : SortKindPair env fuel index original final kind)
    (beforeTyped : Rules.Infer env .full depth
      (.app (.lam (.sort domainSort) (.bvar 0) metadata) original) inputType)
    (beforeSorted : Rules.Red env depth inputType (.sort inputSort))
    (afterShape : IdentityRef domainSort final result)
    (afterTyped : Rules.Infer env .full depth result outputType)
    (afterSorted : Rules.Red env depth outputType (.sort outputSort)) :
    Level.zeronessOf inputSort = Level.zeronessOf outputSort := by
  cases afterShape with
  | reference => exact (pair.identity_to_variable beforeTyped beforeSorted afterTyped afterSorted).2.2
  | beta =>
    have beforeType := (infer_identity_application beforeTyped).1
    have afterType := (infer_identity_application afterTyped).1
    rw [beforeType] at beforeSorted
    rw [afterType] at afterSorted
    rw [Rules.Red.sort_eq beforeSorted, Rules.Red.sort_eq afterSorted]

end IxVM.Refinement.Decl
