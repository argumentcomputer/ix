import Aiur.Optimized.BuildFacts
import Aiur.Optimized.ScopedSemantics

namespace Aiur.Optimized.Compiler

variable {F : Type} [Field F] [DecidableEq F]

def State.activation (state : State F) (scope : ScopeId) : Polynomial F :=
  ((state.scopes[scope]?).map Scope.activation).getD (.const 0)

/-- Local soundness interprets calls through an arbitrary relation, so the
same lemma can later be used for trees and for memoized graphs. -/
def State.Valid (state : State F) (rom : WireROM F) (calls : Circuit.CallRelation F)
    (assignment : Witness → F) : Prop :=
  (∀ equation ∈ state.equations.toList,
    (state.activation equation.scope).denote assignment * equation.polynomial.denote assignment = 0) ∧
  (∀ call ∈ state.calls.toList, (state.activation call.scope).denote assignment = 1 →
    calls call.channel (call.message assignment).args (call.message assignment).result) ∧
  (∀ cell ∈ state.cells.toList, (state.activation cell.scope).denote assignment = 1 →
    (cell.address.denote assignment, cell.value.map (Circuit.ArithExpr.denote assignment)) ∈ rom.entries)

structure State.Extends (before after : State F) : Prop where
  scopes : ∀ (id : ScopeId) (scope : Scope F), before.scopes[id]? = some scope → after.scopes[id]? = some scope
  equations : before.equations.toList ⊆ after.equations.toList
  calls : before.calls.toList ⊆ after.calls.toList
  cells : before.cells.toList ⊆ after.cells.toList

theorem State.Extends.refl (state : State F) : state.Extends state :=
  ⟨fun _ _ => id, fun _ => id, fun _ => id, fun _ => id⟩

theorem State.Extends.trans {first second third : State F} (left : first.Extends second)
    (right : second.Extends third) : first.Extends third :=
  ⟨fun i value found => right.scopes i value (left.scopes i value found),
    fun _ member => right.equations (left.equations member),
    fun _ member => right.calls (left.calls member), fun _ member => right.cells (left.cells member)⟩

theorem State.Extends.activation {before after : State F} (extension : before.Extends after)
    {scope : ScopeId} {assignment : Witness → F} (active : (before.activation scope).denote assignment ≠ 0) :
    after.activation scope = before.activation scope := by
  cases found : before.scopes[scope]? with
  | none => simp [State.activation, found, Scalar.Circuit.ArithExpr.denote] at active
  | some value => simp only [State.activation, found, extension.scopes scope value found]

theorem State.Valid.of_extends {before after : State F} (extension : before.Extends after)
    {rom : WireROM F} {calls : Circuit.CallRelation F} {assignment : Witness → F}
    (valid : after.Valid rom calls assignment) : before.Valid rom calls assignment := by
  refine ⟨?_, ?_, ?_⟩
  · intro equation member
    by_cases inactive : (before.activation equation.scope).denote assignment = 0
    · simp [inactive]
    · rw [← extension.activation inactive]
      exact valid.1 equation (extension.equations member)
  · intro call member active
    have nonzero : (before.activation call.scope).denote assignment ≠ 0 := by rw [active]; exact one_ne_zero
    exact valid.2.1 call (extension.calls member) (by rw [extension.activation nonzero]; exact active)
  · intro cell member active
    have nonzero : (before.activation cell.scope).denote assignment ≠ 0 := by rw [active]; exact one_ne_zero
    exact valid.2.2 cell (extension.cells member) (by rw [extension.activation nonzero]; exact active)

theorem getScope_eq {scope : ScopeId} {value : Scope F} {before after : State F}
    (compiled : getScope scope before = .ok (value, after)) :
    before.scopes[scope]? = some value ∧ after = before := by
  simp only [getScope] at compiled
  obtain ⟨state, middle, getRun, rest⟩ := bind_ok.mp compiled
  change Except.ok (before, before) = Except.ok (state, middle) at getRun
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj getRun)
  cases found : before.scopes[scope]? with
  | none => simp [found] at rest
  | some result =>
    simp [found] at rest
    obtain ⟨rfl, rfl⟩ := rest
    exact ⟨rfl, rfl⟩

theorem fresh_eq {role : Role} {id : Witness} {before after : State F}
    (compiled : fresh role before = .ok (id, after)) :
    id = before.roles.size ∧ after = {before with roles := before.roles.push role, aliases := before.aliases.push none} := by
  change Except.ok (before.roles.size, {before with roles := before.roles.push role, aliases := before.aliases.push none}) =
    Except.ok (id, after) at compiled
  exact ⟨congrArg Prod.fst (Except.ok.inj compiled).symm, congrArg Prod.snd (Except.ok.inj compiled).symm⟩

theorem fresh_valid {role : Role} {id : Witness} {before after : State F}
    (compiled : fresh role before = .ok (id, after))
    {rom : WireROM F} {calls : Circuit.CallRelation F} {assignment : Witness → F}
    (valid : after.Valid rom calls assignment) : before.Valid rom calls assignment := by
  obtain ⟨_, rfl⟩ := fresh_eq compiled
  exact valid

theorem equation_eq {scope : ScopeId} {polynomial : Polynomial F} {before after : State F}
    (compiled : equation scope polynomial before = .ok ((), after)) :
    after = {before with equations := before.equations.push ⟨scope, polynomial⟩} := by
  change Except.ok ((), {before with equations := before.equations.push ⟨scope, polynomial⟩}) =
    Except.ok ((), after) at compiled
  exact congrArg Prod.snd (Except.ok.inj compiled).symm

theorem equation_valid {scope : ScopeId} {polynomial : Polynomial F} {before after : State F}
    (compiled : equation scope polynomial before = .ok ((), after))
    {rom : WireROM F} {calls : Circuit.CallRelation F} {assignment : Witness → F}
    (valid : after.Valid rom calls assignment) : before.Valid rom calls assignment ∧
      (before.activation scope).denote assignment * polynomial.denote assignment = 0 := by
  obtain rfl := equation_eq compiled
  refine ⟨⟨?_, valid.2⟩, valid.1 ⟨scope, polynomial⟩ (by simp)⟩
  intro prior member
  exact valid.1 prior (by simp [member])

end Aiur.Optimized.Compiler
