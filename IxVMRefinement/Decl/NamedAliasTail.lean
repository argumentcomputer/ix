import IxVMRefinement.Decl.NamedAliasReduction

/-! # Product tails ending in an actually checked named alias

The accepted definition front relates the alias's declared sort to its stored target's sort.
Actual kernel evaluation and annotation preserve a small named-tail fragment. Its product
binder data then follow from the recorded inference derivations, including propositional
instances, without assuming that a surrounding context has inhabitants.
-/

namespace IxVM.Refinement.Decl

open Ix.Kernel Ix.Kernel.Model

universe u

private theorem checked_constant_sort {env : Env .anon} {depth : Nat} {name : Key .anon}
    {levels : List Level} {ci : ConstantInfo .anon} {declared resultSort : Level} {inferred : Expr .anon}
    (found : env.find? name = some ci)
    (header : ci.toConstantVal.type.instantiateLevelParams ci.toConstantVal.levelParams levels = .sort declared)
    (typed : Rules.Infer env .full depth (.const name levels) inferred)
    (sorted : Rules.Red env depth inferred (.sort resultSort)) : resultSort = declared := by
  obtain ⟨actual, actualFound, _, _, typeEq⟩ := Rules.Infer.const_inv typed
  obtain rfl := Option.some.inj (actualFound.symm.trans found)
  rw [typeEq, header] at sorted
  exact Rules.Red.sort_eq sorted

/-- The alias's actual declaration check fixes zero-ness in every leaf form. -/
theorem AliasLeaf.checked_zero {V : Type u} [SetTheory V] {env : Env .anon}
    (model : EnvModelM V .verified env) (definitions : DefinitionsTyped env)
    {aliasName targetName : Key .anon} {targetLevels : List Level}
    {aliasCV targetCV : ConstantVal .anon} {hint : ReducibilityHint} {caps : IndCaps .anon}
    {declared actual : Level}
    (aliasFound : env.find? aliasName = some (.defnInfo aliasCV (.const targetName targetLevels) hint))
    (noLevels : aliasCV.levelParams = [])
    (targetFound : env.find? targetName = some (.indInfo targetCV caps))
    (aliasHeader : aliasCV.type = .sort declared)
    (targetHeader : targetCV.type.instantiateLevelParams targetCV.levelParams targetLevels = .sort actual)
    {depth : Nat} {e inferred : Expr .anon} {resultSort : Level}
    (shape : AliasLeaf aliasName targetName targetLevels e)
    (typed : Rules.Infer env .full depth e inferred)
    (sorted : Rules.Red env depth inferred (.sort resultSort)) :
    Level.zeronessOf resultSort = Level.zeronessOf actual := by
  cases shape with
  | named =>
    have header : aliasCV.type.instantiateLevelParams aliasCV.levelParams [] = .sort declared := by
      rw [noLevels]
      exact (Expr.instantiateLevelParams_self [] aliasCV.type).trans aliasHeader
    rw [checked_constant_sort aliasFound header typed sorted]
    exact (definitions.constant_alias_sort model aliasFound targetFound aliasHeader targetHeader).2
  | target => rw [checked_constant_sort targetFound targetHeader typed sorted]
  | beta =>
    exact definitions.beta_constant_alias_zero model aliasFound noLevels targetFound
      aliasHeader targetHeader typed sorted

/-- A product telescope ending in the alias/target/beta fragment. -/
inductive AliasTail (aliasName targetName : Key md) (targetLevels : List Level) : Nat → Expr md → Prop
  | result {e : Expr md} : AliasLeaf aliasName targetName targetLevels e → AliasTail aliasName targetName targetLevels 0 e
  | pi {count : Nat} {domain body : Expr md} {metadata : BinderMeta} :
      AliasTail aliasName targetName targetLevels count body →
      AliasTail aliasName targetName targetLevels (count + 1) (.forallE domain body metadata)

theorem AliasTail.instantiate1 {md : Mode} {aliasName targetName : Key md} {targetLevels : List Level}
    {count : Nat} {e : Expr md} (shape : AliasTail aliasName targetName targetLevels count e) (value : Expr md) :
    ∀ cut, AliasTail aliasName targetName targetLevels count (e.instantiate1 value cut) := by
  induction shape with
  | result leaf => intro cut; exact .result (leaf.instantiate1 value cut)
  | pi _ ih => intro cut; exact .pi (ih (cut + 1))

theorem AliasTail.abstract1 {md : Mode} {aliasName targetName : Key md} {targetLevels : List Level}
    {count : Nat} {e : Expr md} (shape : AliasTail aliasName targetName targetLevels count e) (index : Nat) :
    ∀ cut, AliasTail aliasName targetName targetLevels count (e.abstract1 index cut) := by
  induction shape with
  | result leaf => intro cut; exact .result (leaf.abstract1 index cut)
  | pi _ ih => intro cut; exact .pi (ih (cut + 1))

theorem AliasTail.annotated {aliasName targetName : Key .anon} {targetLevels : List Level}
    {count : Nat} {e out : Expr .anon} (shape : AliasTail aliasName targetName targetLevels count e)
    (annotation : IxVM.Consistency.Annotates out e) : AliasTail aliasName targetName targetLevels count out := by
  induction shape generalizing out with
  | result leaf => exact .result (leaf.annotated annotation)
  | pi _ ih => cases annotation with | forallE _ body => exact .pi (ih body)

theorem AliasTail.whnf {md : Mode} {env : Env md} {fuel depth count : Nat}
    {aliasName targetName : Key md} {targetLevels : List Level}
    {aliasCV targetCV : ConstantVal md} {hint : ReducibilityHint} {caps : IndCaps md}
    (aliasFound : env.find? aliasName = some (.defnInfo aliasCV (.const targetName targetLevels) hint))
    (noLevels : aliasCV.levelParams = [])
    (targetFound : env.find? targetName = some (.indInfo targetCV caps))
    {e out : Expr md} (shape : AliasTail aliasName targetName targetLevels count e)
    (run : whnf .verified env fuel depth e = .ok out) : AliasTail aliasName targetName targetLevels count out := by
  cases shape with
  | result leaf => exact .result (leaf.whnf aliasFound noLevels targetFound run)
  | pi body =>
    rw [Rules.Red.rigid (Rules.whnf_bridge run) rfl]
    exact .pi body

/-- Closure follows the real normalizer calls; only literal product heads use rigidity. -/
theorem AliasTail.normalized {md : Mode} {env : Env md} {fuel steps depth count : Nat}
    {T aliasName targetName : Key md} {targetLevels : List Level}
    {aliasCV targetCV : ConstantVal md} {hint : ReducibilityHint} {caps : IndCaps md}
    (aliasFound : env.find? aliasName = some (.defnInfo aliasCV (.const targetName targetLevels) hint))
    (noLevels : aliasCV.levelParams = [])
    (targetFound : env.find? targetName = some (.indInfo targetCV caps))
    {e out : Expr md} (shape : AliasTail aliasName targetName targetLevels count e)
    (run : normPosDom (fueledOps .verified fuel) env T depth steps e = .ok out) :
    AliasTail aliasName targetName targetLevels count out := by
  induction steps generalizing depth count e out with
  | zero => cases run
  | succ steps ih =>
    simp only [normPosDom] at run
    split at run
    · obtain rfl := (Except.ok.inj run).symm
      exact shape
    · obtain ⟨head, reduced, rest⟩ := exceptBind_ok run
      change Ix.Kernel.whnf .verified env fuel depth e = .ok head at reduced
      have headShape := shape.whnf aliasFound noLevels targetFound reduced
      split at rest
      · obtain rfl := (Except.ok.inj rest).symm
        exact headShape
      · cases head with
        | forallE domain body metadata =>
          cases headShape with
          | result impossible => cases impossible
          | pi bodyShape =>
            dsimp only at rest
            split at rest
            · cases rest
            · obtain ⟨bodyOut, recursive, result⟩ := exceptBind_ok rest
              obtain rfl := (Except.ok.inj result).symm
              exact .pi ((ih (bodyShape.instantiate1 (.fvar depth domain) 0) recursive).abstract1 depth 0)
        | _ =>
          obtain rfl := (Except.ok.inj rest).symm
          exact headShape

/-- Actual typing propagates the target's zero-ness through the entire product tail. -/
theorem AliasTail.checked_zero {V : Type u} [SetTheory V] {env : Env .anon}
    (model : EnvModelM V .verified env) (definitions : DefinitionsTyped env)
    {aliasName targetName : Key .anon} {targetLevels : List Level}
    {aliasCV targetCV : ConstantVal .anon} {hint : ReducibilityHint} {caps : IndCaps .anon}
    {declared actual : Level}
    (aliasFound : env.find? aliasName = some (.defnInfo aliasCV (.const targetName targetLevels) hint))
    (noLevels : aliasCV.levelParams = [])
    (targetFound : env.find? targetName = some (.indInfo targetCV caps))
    (aliasHeader : aliasCV.type = .sort declared)
    (targetHeader : targetCV.type.instantiateLevelParams targetCV.levelParams targetLevels = .sort actual)
    {count depth : Nat} {e inferred : Expr .anon} {resultSort : Level}
    (shape : AliasTail aliasName targetName targetLevels count e)
    (typed : Rules.Infer env .full depth e inferred)
    (sorted : Rules.Red env depth inferred (.sort resultSort)) :
    Level.zeronessOf resultSort = Level.zeronessOf actual := by
  induction count generalizing depth e inferred resultSort with
  | zero =>
    cases shape with
    | result leaf => exact leaf.checked_zero model definitions aliasFound noLevels targetFound aliasHeader targetHeader typed sorted
  | succ count ih =>
    cases shape with
    | @pi _ domain _ _ bodyShape =>
      obtain ⟨_, _, _, _, _, _, bodyTyped, bodySorted, _, typeEq⟩ := Rules.Infer.forallE_inv typed
      have bodyZero := ih (bodyShape.instantiate1 (.fvar depth domain) 0) bodyTyped bodySorted
      rw [typeEq] at sorted
      rw [Rules.Red.sort_eq sorted]
      exact bodyZero

end IxVM.Refinement.Decl
