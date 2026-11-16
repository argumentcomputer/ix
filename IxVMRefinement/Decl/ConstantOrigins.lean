import IxVMRefinement.Decl.DomainCoherence
import IxVMRefinement.Decl.ReferenceDefinitionSorts
import IxC.Kernel.Verify.InferLemmas

/-! # A family of checked constant-result origins

The supported atoms are explicitly scoped by a predicate. Their actual stored headers and
actual delta results are proved once, then shared by beta wrappers and product tails. This
parameterization supports universe instances and dependency-closed alias families without
assuming a global loader fact or rigidity of arbitrary constant-headed Rules.Red derivations.
-/

namespace IxVM.Refinement.Decl

open Ix.Kernel Ix.Kernel.Model

/-- Actual rows and actual delta closure for a chosen family of named type results. -/
structure ConstantFamily (env : Env .anon) (atoms : Key .anon → List Level → Prop)
    (datum : PropWhen) : Prop where
  row : ∀ name levels, atoms name levels → ∃ ci sortLevel,
    env.find? name = some ci ∧
      ci.toConstantVal.type.instantiateLevelParams ci.toConstantVal.levelParams levels = .sort sortLevel ∧
      Level.zeronessOf sortLevel = datum
  delta : ∀ name levels out, atoms name levels → unfoldDefinition env (.const name levels) = some out →
    ∃ nextName nextLevels, out = .const nextName nextLevels ∧ atoms nextName nextLevels

/-- A named result in the chosen family, possibly behind a constant-body beta redex. -/
inductive ConstantLeaf (atoms : Key .anon → List Level → Prop) : Expr .anon → Prop
  | atom {name : Key .anon} {levels : List Level} : atoms name levels → ConstantLeaf atoms (.const name levels)
  | beta {name : Key .anon} {levels : List Level} {domain argument : Expr .anon} {metadata : BinderMeta} :
      atoms name levels → ConstantLeaf atoms (.app (.lam domain (.const name levels) metadata) argument)

theorem ConstantLeaf.instantiate1 {atoms : Key .anon → List Level → Prop} {e : Expr .anon}
    (origin : ConstantLeaf atoms e) (value : Expr .anon) :
    ∀ cut, ConstantLeaf atoms (e.instantiate1 value cut) := by
  cases origin with
  | atom member => intro cut; exact .atom member
  | beta member => intro cut; exact .beta member

theorem ConstantLeaf.abstract1 {atoms : Key .anon → List Level → Prop} {e : Expr .anon}
    (origin : ConstantLeaf atoms e) (index : Nat) :
    ∀ cut, ConstantLeaf atoms (e.abstract1 index cut) := by
  cases origin with
  | atom member => intro cut; exact .atom member
  | beta member => intro cut; exact .beta member

theorem ConstantLeaf.annotated {atoms : Key .anon → List Level → Prop} {e out : Expr .anon}
    (origin : ConstantLeaf atoms e) (annotation : IxVM.Consistency.Annotates out e) : ConstantLeaf atoms out := by
  cases origin with
  | atom member => cases annotation; exact .atom member
  | beta member =>
    cases annotation with
    | app functionAnn _ =>
      cases functionAnn with
      | lam _ bodyAnn => cases bodyAnn; exact .beta member

private theorem constant_core {env : Env .anon} {fuel depth : Nat} {name : Key .anon}
    {levels : List Level} {out : Expr .anon}
    (run : whnfCore .verified env fuel depth (.const name levels) = .ok out) : out = .const name levels := by
  cases fuel with
  | zero => cases run
  | succ fuel => exact (Except.ok.inj run).symm

private theorem lambda_core {env : Env .anon} {fuel depth : Nat} {domain body out : Expr .anon} {metadata : BinderMeta}
    (run : whnfCore .verified env fuel depth (.lam domain body metadata) = .ok out) :
    out = .lam domain body metadata := by
  cases fuel with
  | zero => cases run
  | succ fuel => exact (Except.ok.inj run).symm

theorem ConstantLeaf.whnfCore {env : Env .anon} {atoms : Key .anon → List Level → Prop}
    {fuel depth : Nat} {e out : Expr .anon} (origin : ConstantLeaf atoms e)
    (run : Ix.Kernel.whnfCore .verified env fuel depth e = .ok out) : ConstantLeaf atoms out := by
  cases origin with
  | atom member => rw [constant_core run]; exact .atom member
  | @beta name levels domain argument metadata member =>
    cases fuel with
    | zero => cases run
    | succ fuel =>
      obtain ⟨functionExpr, functionRun, branches⟩ := whnf_app_inv run
      obtain rfl := lambda_core functionRun
      rcases branches with ⟨domain', body', metadata', same, bodyRun, _⟩ | ⟨result, iota, _⟩ | same
      · obtain ⟨rfl, rfl, rfl⟩ := Expr.lam.inj same
        rw [constant_core bodyRun]
        exact .atom member
      · have impossible : iotaRecFueled .verified env fuel depth
            (.app (.lam domain (.const name levels) metadata) argument) = .ok none := rfl
        rw [impossible] at iota
        cases iota
      · rw [same]
        exact .beta member

private theorem ConstantLeaf.noNat {env : Env .anon} {atoms : Key .anon → List Level → Prop}
    {fuel depth : Nat} {e : Expr .anon} (origin : ConstantLeaf atoms e) :
    reduceNatFueled .verified env fuel depth e = .ok none := by cases origin <;> rfl

private theorem ConstantLeaf.unfolded {env : Env .anon} {atoms : Key .anon → List Level → Prop} {datum : PropWhen}
    (family : ConstantFamily env atoms datum) {e out : Expr .anon} (origin : ConstantLeaf atoms e)
    (unfolded : unfoldDefinition env e = some out) : ConstantLeaf atoms out := by
  cases origin with
  | atom member =>
    obtain ⟨name, levels, rfl, nextMember⟩ := family.delta _ _ _ member unfolded
    exact .atom nextMember
  | beta => cases unfolded

/-- Only actual kernel evaluation is used; the family handles the delta branch explicitly. -/
theorem ConstantLeaf.whnf {env : Env .anon} {atoms : Key .anon → List Level → Prop} {datum : PropWhen}
    (family : ConstantFamily env atoms datum) {fuel depth : Nat} {e out : Expr .anon}
    (origin : ConstantLeaf atoms e) (run : Ix.Kernel.whnf .verified env fuel depth e = .ok out) : ConstantLeaf atoms out := by
  cases fuel with
  | zero => cases run
  | succ fuel =>
    rw [whnf_succ] at run
    have loop : ∀ budget {input output}, ConstantLeaf atoms input →
        whnfLoop (pureFns .verified env fuel) env depth budget input = .ok output → ConstantLeaf atoms output := by
      intro budget
      induction budget with
      | zero => intro input output _ impossible; cases impossible
      | succ budget ih =>
        intro input output inputOrigin checked
        obtain ⟨head, coreRun, branches⟩ := whnfStep_inv checked
        have headOrigin := inputOrigin.whnfCore coreRun
        rcases branches with ⟨next, natural, _⟩ | ⟨_, next, unfolded, continued⟩ | ⟨_, _, same⟩
        · rw [headOrigin.noNat] at natural
          cases natural
        · exact ih (headOrigin.unfolded family unfolded) continued
        · rw [same]
          exact headOrigin
    exact loop whnfLoopFuel origin run

theorem ConstantLeaf.checked_zero {env : Env .anon} {atoms : Key .anon → List Level → Prop} {datum : PropWhen}
    (family : ConstantFamily env atoms datum) {depth : Nat} {e inferred : Expr .anon} {resultSort : Level}
    (origin : ConstantLeaf atoms e) (typed : Rules.Infer env .full depth e inferred)
    (sorted : Rules.Red env depth inferred (.sort resultSort)) : Level.zeronessOf resultSort = datum := by
  cases origin with
  | atom member =>
    obtain ⟨ci, sortLevel, found, header, zero⟩ := family.row _ _ member
    obtain ⟨actual, actualFound, _, _, typeEq⟩ := Rules.Infer.const_inv typed
    obtain rfl := Option.some.inj (actualFound.symm.trans found)
    rw [typeEq, header] at sorted
    rw [Rules.Red.sort_eq sorted]
    exact zero
  | beta member =>
    obtain ⟨ci, sortLevel, found, header, zero⟩ := family.row _ _ member
    rw [infer_beta_constant_sort found header typed] at sorted
    rw [Rules.Red.sort_eq sorted]
    exact zero

/-- Arbitrary product telescopes over the same parameterized family of constant results. -/
inductive ConstantTail (atoms : Key .anon → List Level → Prop) : Nat → Expr .anon → Prop
  | result {e : Expr .anon} : ConstantLeaf atoms e → ConstantTail atoms 0 e
  | pi {count : Nat} {domain body : Expr .anon} {metadata : BinderMeta} :
      ConstantTail atoms count body → ConstantTail atoms (count + 1) (.forallE domain body metadata)

theorem ConstantTail.instantiate1 {atoms : Key .anon → List Level → Prop} {count : Nat} {e : Expr .anon}
    (origin : ConstantTail atoms count e) (value : Expr .anon) : ∀ cut, ConstantTail atoms count (e.instantiate1 value cut) := by
  induction origin with
  | result leaf => intro cut; exact .result (leaf.instantiate1 value cut)
  | pi _ ih => intro cut; exact .pi (ih (cut + 1))

theorem ConstantTail.abstract1 {atoms : Key .anon → List Level → Prop} {count : Nat} {e : Expr .anon}
    (origin : ConstantTail atoms count e) (index : Nat) : ∀ cut, ConstantTail atoms count (e.abstract1 index cut) := by
  induction origin with
  | result leaf => intro cut; exact .result (leaf.abstract1 index cut)
  | pi _ ih => intro cut; exact .pi (ih (cut + 1))

theorem ConstantTail.annotated {atoms : Key .anon → List Level → Prop} {count : Nat} {e out : Expr .anon}
    (origin : ConstantTail atoms count e) (annotation : IxVM.Consistency.Annotates out e) : ConstantTail atoms count out := by
  induction origin generalizing out with
  | result leaf => exact .result (leaf.annotated annotation)
  | pi _ ih => cases annotation with | forallE _ body => exact .pi (ih body)

theorem ConstantTail.whnf {env : Env .anon} {atoms : Key .anon → List Level → Prop} {datum : PropWhen}
    (family : ConstantFamily env atoms datum) {fuel depth count : Nat} {e out : Expr .anon}
    (origin : ConstantTail atoms count e) (run : Ix.Kernel.whnf .verified env fuel depth e = .ok out) : ConstantTail atoms count out := by
  cases origin with
  | result leaf => exact .result (leaf.whnf family run)
  | pi body => rw [Rules.Red.rigid (Rules.whnf_bridge run) rfl]; exact .pi body

theorem ConstantTail.checked_zero {env : Env .anon} {atoms : Key .anon → List Level → Prop} {datum : PropWhen}
    (family : ConstantFamily env atoms datum) {count depth : Nat} {e inferred : Expr .anon} {resultSort : Level}
    (origin : ConstantTail atoms count e) (typed : Rules.Infer env .full depth e inferred)
    (sorted : Rules.Red env depth inferred (.sort resultSort)) : Level.zeronessOf resultSort = datum := by
  induction count generalizing depth e inferred resultSort with
  | zero => cases origin with | result leaf => exact leaf.checked_zero family typed sorted
  | succ count ih =>
    cases origin with
    | @pi _ domain _ _ bodyOrigin =>
      obtain ⟨_, _, _, _, _, _, bodyTyped, bodySorted, _, typeEq⟩ := Rules.Infer.forallE_inv typed
      have bodyZero := ih (bodyOrigin.instantiate1 (.fvar depth domain) 0) bodyTyped bodySorted
      rw [typeEq] at sorted
      rw [Rules.Red.sort_eq sorted]
      exact bodyZero

/-- A constructed constant family directly instantiates the shared rebuild/coherence protocol. -/
theorem ConstantFamily.invariant {env : Env .anon} {atoms : Key .anon → List Level → Prop} {datum : PropWhen}
    (family : ConstantFamily env atoms datum) :
    SyntacticDomainInvariant env (fun e => ∃ count, ConstantTail atoms count e) datum where
  checked := by
    intro depth e inferred level ⟨count, origin⟩ typed sorted
    exact origin.checked_zero family typed sorted
  abstracts := by
    intro e index cut ⟨count, origin⟩
    exact ⟨count, origin.abstract1 index cut⟩
  instantiates := by
    intro e value cut ⟨count, origin⟩
    exact ⟨count, origin.instantiate1 value cut⟩
  annotates := by
    intro e out ⟨count, origin⟩ annotation
    exact ⟨count, origin.annotated annotation⟩
  whnf_closed := by
    intro fuel depth e out ⟨count, origin⟩ run
    exact ⟨count, origin.whnf family run⟩
  product_body := by
    intro domain body metadata ⟨count, origin⟩
    cases origin with
    | result impossible => cases impossible
    | pi bodyOrigin => exact ⟨_, bodyOrigin⟩
  product := by
    intro domain body metadata ⟨count, origin⟩
    exact ⟨count + 1, .pi origin⟩

end IxVM.Refinement.Decl
