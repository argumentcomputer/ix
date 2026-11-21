import Aiur.Optimized.ChoiceWitness
import Aiur.Optimized.CompileFacts
import Aiur.Optimized.PatternWitness

namespace Aiur.Optimized.Compiler

variable {F : Type} [Field F] [DecidableEq F]
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

theorem fresh_scoped {role : Role} {id : Witness} {before after : State F}
    (compiled : fresh role before = .ok (id, after)) (scopeLayout : before.Scoped) : after.Scoped := by
  obtain ⟨_, rfl⟩ := fresh_eq compiled
  exact scopeLayout.fresh role

theorem freshValue_scoped {decls : Declarations} {role : Role} {type : Ty}
    {value : WireValue Witness} {before after : State F}
    (compiled : freshValue decls role type before = .ok (value, after))
    (scopeLayout : before.Scoped) : after.Scoped := by
  obtain ⟨scopes, equations, calls, cells⟩ := freshValue_preserves compiled
  have grow : before.roles.size ≤ after.roles.size := by
    obtain ⟨layout, _, _, stateEq⟩ := Circuit.Compiler.freshValue_eq (freshValue_reference compiled)
    have sizeEq := congrArg Circuit.Compiler.BuildState.nextVar stateEq
    change after.roles.size = before.roles.size + layout.width at sizeEq
    omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [scopes, equations] using scopeLayout.equations
  · simpa [scopes, calls] using scopeLayout.calls
  · simpa [scopes, cells] using scopeLayout.cells
  · intro scope member
    rw [scopes] at member
    exact Scalar.Circuit.ArithExpr.inBounds_mono grow (scopeLayout.activations scope member)

theorem destination_scoped {decls : Declarations} {scope : ScopeId} {type : Ty}
    {target : Option (WireValue Witness)} {value : WireValue Witness} {before after : State F}
    (compiled : destination decls scope type target before = .ok (value, after))
    (scopeLayout : before.Scoped) : after.Scoped := by
  cases target with
  | none => exact freshValue_scoped compiled scopeLayout
  | some target =>
      simp only [destination] at compiled
      split at compiled
      · simp [StateT.bind, bind, Except.bind] at compiled
      · obtain ⟨⟨⟩, middle, emptyRun, finished⟩ := bind_ok.mp compiled
        obtain ⟨_, stateEq⟩ := pure_ok.mp emptyRun
        subst middle
        obtain ⟨rfl, rfl⟩ := pure_ok.mp finished
        exact scopeLayout

theorem equation_scoped {scope : ScopeId} {polynomial : Polynomial F} {before after : State F}
    (compiled : equation scope polynomial before = .ok ((), after))
    (scopeLayout : before.Scoped) (scopeValid : scope < before.scopes.size) : after.Scoped := by
  obtain rfl := equation_eq compiled
  exact scopeLayout.equation scopeValid polynomial

theorem equations_scoped {scope : ScopeId} {conditions : List (Polynomial F)} {before after : State F}
    (compiled : (do for condition in conditions do equation scope condition : Build F Unit)
      before = .ok ((), after))
    (scopeLayout : before.Scoped) (scopeValid : scope < before.scopes.size) : after.Scoped := by
  induction conditions generalizing before with
  | nil =>
      have same : before = after := by
        simpa [List.forIn_nil, pure, StateT.pure, StateT.bind, bind, Except.bind, Except.pure] using compiled
      exact same ▸ scopeLayout
  | cons condition conditions ih =>
      simp [List.forIn_cons, equation, modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet,
        StateT.bind, bind, Except.bind, StateT.pure, pure, Except.pure] at compiled
      exact ih (before := {before with equations := before.equations.push ⟨scope, condition⟩})
        compiled (scopeLayout.equation scopeValid condition) scopeValid

theorem equalValue_scoped {scope : ScopeId} {left right : Symbolic F} {before after : State F}
    (compiled : equalValue scope left right before = .ok ((), after))
    (scopeLayout : before.Scoped) (scopeValid : scope < before.scopes.size) : after.Scoped := by
  simp only [equalValue] at compiled
  split at compiled
  · simp [StateT.bind, bind, Except.bind] at compiled
  · obtain ⟨⟨⟩, middle, unchanged, rest⟩ := bind_ok.mp compiled
    obtain ⟨_, rfl⟩ := pure_ok.mp unchanged
    have equations : (do
        for polynomial in (left.words.zip right.words).map (fun (a, b) => Polynomial.sub a b) do
          equation scope polynomial : Build F Unit) before = .ok ((), after) := by
      simpa only [List.forIn_map] using rest
    exact equations_scoped equations scopeLayout scopeValid

theorem equalValue_scopes {scope : ScopeId} {left right : Symbolic F} {before after : State F}
    (compiled : equalValue scope left right before = .ok ((), after)) : after.scopes = before.scopes := by
  simp only [equalValue] at compiled
  split at compiled
  · simp [StateT.bind, bind, Except.bind] at compiled
  · obtain ⟨⟨⟩, middle, unchanged, rest⟩ := bind_ok.mp compiled
    obtain ⟨_, rfl⟩ := pure_ok.mp unchanged
    have equations : (do
        for polynomial in (left.words.zip right.words).map (fun (a, b) => Polynomial.sub a b) do
          equation scope polynomial : Build F Unit) before = .ok ((), after) := by
      simpa only [List.forIn_map] using rest
    exact equations_scopes equations

theorem finish_scopes {scope : ScopeId} {target : Option (WireValue Witness)} {value output : Symbolic F}
    {before after : State F}
    (compiled : (do
      if let some result := target then
        equalValue scope (result.map Polynomial.var) value
        return result.map Polynomial.var
      return value : Build F (Symbolic F)) before = .ok (output, after)) :
    after.scopes = before.scopes := by
  cases target with
  | none =>
      obtain ⟨rfl, rfl⟩ := pure_ok.mp compiled
      rfl
  | some result =>
      obtain ⟨⟨⟩, middle, equalRun, finished⟩ := bind_ok.mp compiled
      obtain ⟨rfl, rfl⟩ := pure_ok.mp finished
      exact equalValue_scopes equalRun

theorem State.Extends.scopeValid {before after : State F} (extension : before.Extends after)
    {scope : ScopeId} (scopeValid : scope < before.scopes.size) : scope < after.scopes.size := by
  have found : before.scopes[scope]? = some before.scopes[scope] := by simp [scopeValid]
  exact (Array.getElem?_eq_some_iff.mp (extension.scopes _ _ found)).1

theorem Extension.activation {rom : WireROM F} {calls : Circuit.CallRelation F}
    {before after : State F} {initial assignment : Witness → F}
    (extension : Extension rom calls before after initial assignment)
    (structural : before.Extends after) (scopeLayout : before.Scoped)
    {scope : ScopeId} (scopeValid : scope < before.scopes.size) :
    (after.activation scope).denote assignment = (before.activation scope).denote initial := by
  rw [structural.activation_eq scopeValid]
  exact extension.polynomial (scopeLayout.activation_bound scope)

end Aiur.Optimized.Compiler
