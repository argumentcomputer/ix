/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.Verify.Consistency.ScopedExpr
import Ix.Kernel.Verify.Consistency.InstUniv

/-!
# Universe instantiation of closed types in an active local context

The universe walker preserves the term binders of a closed declaration type.
Its returned type therefore has the same scoped reading in every active local
context. Simplifying levels retain the existing exact annotation and semantic
congruence guarantees. No runtime result reading is assumed.
-/

namespace Ix.Kernel.Consistency

open Theory Theory.Model

universe u
variable {β : Type u}

private theorem option_bind_success {α γ : Type _} {action : Option α}
    {next : α → Option γ} {result : γ} (run : action.bind next = some result) :
    ∃ intermediate, action = some intermediate ∧ next intermediate = some result := by
  cases action with
  | none => contradiction
  | some value => exact ⟨value, rfl, run⟩

private theorem except_bind_success {ε α γ : Type _} {action : Except ε α}
    {next : α → Except ε γ} {result : γ} (run : action.bind next = .ok result) :
    ∃ intermediate, action = .ok intermediate ∧ next intermediate = .ok result := by
  cases action with
  | error err => contradiction
  | ok value => exact ⟨value, rfl, run⟩

/-- Pure universe substitution preserves exactly the term-binding structure
needed to read a closed declaration type in an arbitrary local context. -/
theorem instUnivSpec_scoped_eq {resolve : Address → Option (ConstRef β)}
    {arguments : Array (KUniv .anon)} {term result : KExpr .anon}
    {source : VExpr β} {depth : Nat} (locals : List FVarId)
    (reading : readScopedExpr? resolve [] term depth = some source)
    (run : KExpr.instUnivSpec term arguments = .ok result) :
    readScopedExpr? resolve locals result depth = readExpr? resolve result := by
  induction term generalizing source result depth with
  | var index name info =>
      cases run
      simp only [readScopedExpr?] at reading ⊢
      split at reading
      next bound => simp [bound, readExpr?]
      · contradiction
  | fvar _ _ _ | str _ _ _ => contradiction
  | letE name domain value body nonDep info ihDomain ihValue ihBody =>
      obtain ⟨A, v, b, domainReads, valueReads, bodyReads, _⟩ := readScopedExpr?_let_parts reading
      rw [KExpr.instUnivSpec] at run
      obtain ⟨domain', domainRun, run⟩ := except_bind_success run
      obtain ⟨value', valueRun, run⟩ := except_bind_success run
      obtain ⟨body', bodyRun, run⟩ := except_bind_success run
      cases run
      simp only [readScopedExpr?_mkLet]
      rw [ihDomain domainReads domainRun, ihValue valueReads valueRun, ihBody bodyReads bodyRun]
      rfl
  | nat _ _ _ => cases run; rfl
  | sort _ _ | const _ _ _ =>
      rw [KExpr.instUnivSpec] at run
      obtain ⟨_, _, run⟩ := except_bind_success run
      cases run
      rfl
  | app fn arg info hf ha | lam _ _ fn arg info hf ha | all _ _ fn arg info hf ha =>
      rw [readScopedExpr?] at reading
      obtain ⟨f, fReads, reading⟩ := option_bind_success reading
      obtain ⟨a, aReads, reading⟩ := option_bind_success reading
      rw [KExpr.instUnivSpec] at run
      obtain ⟨fn', fRun, run⟩ := except_bind_success run
      obtain ⟨arg', aRun, run⟩ := except_bind_success run
      cases run
      simp only [readScopedExpr?_mkApp, readScopedExpr?_mkLam, readScopedExpr?_mkAll]
      rw [hf fReads fRun, ha aReads aRun]
      rfl
  | prj id index value info ih =>
      rw [readScopedExpr?] at reading
      obtain ⟨ref, _, reading⟩ := option_bind_success reading
      obtain ⟨value, valueReads, _⟩ := option_bind_success reading
      rw [KExpr.instUnivSpec] at run
      obtain ⟨value', valueRun, run⟩ := except_bind_success run
      cases run
      simp only [readScopedExpr?_mkPrj]
      rw [ih valueReads valueRun]
      rfl

/-- Include the production empty-argument shortcut in the structural result. -/
theorem instantiateUnivParamsSpec_scoped_eq {resolve : Address → Option (ConstRef β)}
    {arguments : Array (KUniv .anon)} {term result : KExpr .anon}
    {source : VExpr β} {depth : Nat} (locals : List FVarId)
    (reading : readScopedExpr? resolve [] term depth = some source)
    (run : KExpr.instantiateUnivParamsSpec term arguments = .ok result) :
    readScopedExpr? resolve locals result depth = readExpr? resolve result := by
  unfold KExpr.instantiateUnivParamsSpec at run
  split at run
  · cases run
    exact (readScopedExpr?_weaken_closed reading locals).trans
      (readScopedExpr?_closed reading).symm
  · exact instUnivSpec_scoped_eq locals reading run

/-- The real memoized and interned execution preserves closed term scope,
including when its universe constructors simplify the returned syntax. -/
theorem instantiateUnivParams_scoped_eq {resolve : Address → Option (ConstRef β)}
    {arguments : Array (KUniv .anon)} {term result : KExpr .anon}
    {source : VExpr β} {depth : Nat} {before after : TcState .anon}
    (locals : List FVarId) (support : UniverseInstantiationSupport before term arguments)
    (reading : readScopedExpr? resolve [] term depth = some source)
    (run : TcM.instantiateUnivParams term arguments before = .ok result after) :
    readScopedExpr? resolve locals result depth = readExpr? resolve result := by
  have post := TcM.instantiateUnivParams_wf support.faithful
    (fun _ h => Or.inr h) ⟨support.coherent, fun _ h => Or.inl h⟩
  rw [run] at post
  exact instantiateUnivParamsSpec_scoped_eq locals reading post.2.1

/-- The pure substituted tree has the admitted type's meaning, including the
empty shortcut and simplifying universe constructors. Cache verification uses
only level resources here; it does not run an interning operation. -/
theorem instantiateUnivParamsSpec_readScopedAnnotated
    {resolve : Address → Option (ConstRef β)} {locals : List FVarId}
    {arguments : Array (KUniv .anon)} {term result : KExpr .anon} {source : AExpr β}
    (support : UniverseSubstitutionSupport arguments term)
    (scope : source.erase.LevelWF arguments.size)
    (reading : readScopedExpr? resolve [] term = some source.erase)
    (run : KExpr.instantiateUnivParamsSpec term arguments = .ok result) :
    ∃ output : AExpr β, readScopedExpr? resolve locals result = some output.erase ∧
      AExpr.LevelEquivalent (source.instL (arguments.toList.map readLevel)) output := by
  have raw : ∃ output, readExpr? resolve result = some output ∧
      VExpr.LevelEquivalent (source.erase.instL (arguments.toList.map readLevel)) output := by
    by_cases empty : arguments.isEmpty = true
    · have args : arguments = #[] := Array.isEmpty_iff.mp empty
      subst arguments
      change Except.ok term = .ok result at run
      cases run
      refine ⟨source.erase, readScopedExpr?_closed reading, ?_⟩
      simpa only [Array.toList_empty, List.map_nil, scope.instL_nil] using
        VExpr.LevelEquivalent.refl source.erase
    · rw [KExpr.instantiateUnivParamsSpec, if_neg empty] at run
      exact instUnivSpec_readExpr? support (readScopedExpr?_closed reading) run
  obtain ⟨raw, rawReads, same⟩ := raw
  rw [← AExpr.erase_instL] at same
  obtain ⟨output, erased, equivalent⟩ := AExpr.reannotate_levels _ same
  exact ⟨output, (instantiateUnivParamsSpec_scoped_eq locals reading run).trans
    (erased ▸ rawReads), equivalent⟩

/-- Read the actual returned annotated type in an active local context.
Universe scope justifies the empty shortcut; all annotation occurrences and
hereditary validity are preserved by the level congruence. -/
theorem instantiateUnivParams_readScopedAnnotated
    {resolve : Address → Option (ConstRef β)} {locals : List FVarId}
    {arguments : Array (KUniv .anon)} {term result : KExpr .anon} {source : AExpr β}
    {before after : TcState .anon}
    (support : UniverseInstantiationSupport before term arguments)
    (scope : source.erase.LevelWF arguments.size)
    (reading : readScopedExpr? resolve [] term = some source.erase)
    (run : TcM.instantiateUnivParams term arguments before = .ok result after) :
    ∃ output : AExpr β, readScopedExpr? resolve locals result = some output.erase ∧
      AExpr.LevelEquivalent (source.instL (arguments.toList.map readLevel)) output := by
  obtain ⟨output, outputReads, same⟩ := instantiateUnivParams_readAnnotated support scope
    (readScopedExpr?_closed reading) run
  exact ⟨output, (instantiateUnivParams_scoped_eq locals support reading run).trans outputReads, same⟩

end Ix.Kernel.Consistency
