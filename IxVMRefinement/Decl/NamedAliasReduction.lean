import IxVMRefinement.Decl.ReferenceDefinitionSorts
import IxC.Kernel.Verify.InferLemmas

/-! # Actual kernel reduction of a checked constant alias

This small fragment contains an alias, its named inductive target, and a constant-body beta
redex returning the alias. Its closure is proved from the executable whnf trace. The general
Rules.Red relation also permits equality reflection at constant heads and is not used to claim
opaque-head rigidity here.
-/

namespace IxVM.Refinement.Decl

open Ix.Kernel

/-- A named alias or target, possibly behind one constant-body beta redex. -/
inductive AliasLeaf (aliasName targetName : Key md) (targetLevels : List Level) : Expr md → Prop
  | named : AliasLeaf aliasName targetName targetLevels (.const aliasName [])
  | target : AliasLeaf aliasName targetName targetLevels (.const targetName targetLevels)
  | beta {domain argument : Expr md} {metadata : BinderMeta} :
      AliasLeaf aliasName targetName targetLevels
        (.app (.lam domain (.const aliasName []) metadata) argument)

theorem AliasLeaf.instantiate1 {md : Mode} {aliasName targetName : Key md} {targetLevels : List Level}
    {e : Expr md} (shape : AliasLeaf aliasName targetName targetLevels e) (value : Expr md) :
    ∀ cut, AliasLeaf aliasName targetName targetLevels (e.instantiate1 value cut) := by
  cases shape <;> intro cut
  · exact .named
  · exact .target
  · exact .beta

theorem AliasLeaf.abstract1 {md : Mode} {aliasName targetName : Key md} {targetLevels : List Level}
    {e : Expr md} (shape : AliasLeaf aliasName targetName targetLevels e) (index : Nat) :
    ∀ cut, AliasLeaf aliasName targetName targetLevels (e.abstract1 index cut) := by
  cases shape <;> intro cut
  · exact .named
  · exact .target
  · exact .beta

theorem AliasLeaf.annotated {aliasName targetName : Key .anon} {targetLevels : List Level}
    {e out : Expr .anon} (shape : AliasLeaf aliasName targetName targetLevels e)
    (annotation : IxVM.Consistency.Annotates out e) : AliasLeaf aliasName targetName targetLevels out := by
  cases shape with
  | named => cases annotation; exact .named
  | target => cases annotation; exact .target
  | beta =>
    cases annotation with
    | app functionAnn _ =>
      cases functionAnn with
      | lam _ bodyAnn => cases bodyAnn; exact .beta

private theorem whnfCore_const_eq {md : Mode} {env : Env md} {fuel depth : Nat}
    {name : Key md} {levels : List Level} {out : Expr md}
    (run : whnfCore .verified env fuel depth (.const name levels) = .ok out) : out = .const name levels := by
  cases fuel with
  | zero => cases run
  | succ fuel => exact (Except.ok.inj run).symm

private theorem whnfCore_lam_eq {md : Mode} {env : Env md} {fuel depth : Nat}
    {domain body out : Expr md} {metadata : BinderMeta}
    (run : whnfCore .verified env fuel depth (.lam domain body metadata) = .ok out) :
    out = .lam domain body metadata := by
  cases fuel with
  | zero => cases run
  | succ fuel => exact (Except.ok.inj run).symm

/-- Core reduction either performs the certified beta step or leaves that same redex stuck. -/
theorem AliasLeaf.whnfCore {md : Mode} {env : Env md} {fuel depth : Nat}
    {aliasName targetName : Key md} {targetLevels : List Level} {e out : Expr md}
    (shape : AliasLeaf aliasName targetName targetLevels e)
    (run : whnfCore .verified env fuel depth e = .ok out) : AliasLeaf aliasName targetName targetLevels out := by
  cases shape with
  | named => rw [whnfCore_const_eq run]; exact .named
  | target => rw [whnfCore_const_eq run]; exact .target
  | @beta domain argument metadata =>
    cases fuel with
    | zero => cases run
    | succ fuel =>
      obtain ⟨functionExpr, functionRun, branches⟩ := whnf_app_inv run
      obtain rfl := whnfCore_lam_eq functionRun
      rcases branches with ⟨domain', body', metadata', same, bodyRun, _⟩ |
        ⟨result, iota, _⟩ | same
      · obtain ⟨rfl, rfl, rfl⟩ := Expr.lam.inj same
        have resultEq := whnfCore_const_eq bodyRun
        rw [resultEq]
        exact .named
      · have impossible : iotaRecFueled .verified env fuel depth
            (.app (.lam domain (.const aliasName []) metadata) argument) = .ok none := rfl
        rw [impossible] at iota
        cases iota
      · rw [same]
        exact .beta

private theorem AliasLeaf.noNat {md : Mode} {env : Env md} {fuel depth : Nat}
    {aliasName targetName : Key md} {targetLevels : List Level} {e : Expr md}
    (shape : AliasLeaf aliasName targetName targetLevels e) :
    reduceNatFueled .verified env fuel depth e = .ok none := by cases shape <;> rfl

private theorem AliasLeaf.unfolded {md : Mode} {env : Env md}
    {aliasName targetName : Key md} {targetLevels : List Level}
    {aliasCV targetCV : ConstantVal md} {hint : ReducibilityHint} {caps : IndCaps md}
    (aliasFound : env.find? aliasName = some (.defnInfo aliasCV (.const targetName targetLevels) hint))
    (noLevels : aliasCV.levelParams = [])
    (targetFound : env.find? targetName = some (.indInfo targetCV caps))
    {e out : Expr md} (shape : AliasLeaf aliasName targetName targetLevels e)
    (unfolded : unfoldDefinition env e = some out) : AliasLeaf aliasName targetName targetLevels out := by
  cases shape with
  | named =>
    have step : unfoldDefinition env (.const aliasName []) = some (.const targetName targetLevels) := by
      simp only [unfoldDefinition, Expr.getAppFn, aliasFound, noLevels, List.length_nil,
        ↓reduceIte, Expr.getAppArgs, Expr.mkAppN]
      exact congrArg some (Expr.instantiateLevelParams_self [] (.const targetName targetLevels))
    rw [step] at unfolded
    obtain rfl := Option.some.inj unfolded
    exact .target
  | target => simp only [unfoldDefinition, Expr.getAppFn, targetFound] at unfolded; cases unfolded
  | beta => cases unfolded

/-- The complete kernel whnf loop preserves the fragment using the actual alias/target rows. -/
theorem AliasLeaf.whnf {md : Mode} {env : Env md} {fuel depth : Nat}
    {aliasName targetName : Key md} {targetLevels : List Level}
    {aliasCV targetCV : ConstantVal md} {hint : ReducibilityHint} {caps : IndCaps md}
    (aliasFound : env.find? aliasName = some (.defnInfo aliasCV (.const targetName targetLevels) hint))
    (noLevels : aliasCV.levelParams = [])
    (targetFound : env.find? targetName = some (.indInfo targetCV caps))
    {e out : Expr md} (shape : AliasLeaf aliasName targetName targetLevels e)
    (run : whnf .verified env fuel depth e = .ok out) : AliasLeaf aliasName targetName targetLevels out := by
  cases fuel with
  | zero => cases run
  | succ fuel =>
    rw [whnf_succ] at run
    have loop : ∀ budget {input output}, AliasLeaf aliasName targetName targetLevels input →
        whnfLoop (pureFns .verified env fuel) env depth budget input = .ok output →
        AliasLeaf aliasName targetName targetLevels output := by
      intro budget
      induction budget with
      | zero => intro input output _ impossible; cases impossible
      | succ budget ih =>
        intro input output inputShape checked
        obtain ⟨head, coreRun, branches⟩ := whnfStep_inv checked
        have headShape := inputShape.whnfCore coreRun
        rcases branches with ⟨next, natural, _⟩ | ⟨_, next, unfolded, continued⟩ | ⟨_, _, same⟩
        · rw [headShape.noNat] at natural
          cases natural
        · exact ih (headShape.unfolded aliasFound noLevels targetFound unfolded) continued
        · rw [same]
          exact headShape
    exact loop whnfLoopFuel shape run

end IxVM.Refinement.Decl
