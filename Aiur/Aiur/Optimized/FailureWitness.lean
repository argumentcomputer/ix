import Aiur.Optimized.ScopedInvariant

namespace Aiur.Optimized.Compiler

variable {F : Type} [Field F] [DecidableEq F]
set_option maxHeartbeats 1500000
set_option maxRecDepth 4096

theorem failures_complete {scope : ScopeId} {previous : List (List (Polynomial F))} {before after : State F}
    (compiled : (do for earlier in previous do failure scope earlier : Build F Unit)
      before = .ok ((), after))
    {rom : WireROM F} {calls : Circuit.CallRelation F} {initial : Witness → F}
    (layout : before.toReference.WellFormed) (scopeLayout : before.Scoped)
    (valid : before.Valid rom calls initial) (scopeValid : scope < before.scopes.size)
    (bounded : ∀ earlier ∈ previous, ∀ condition ∈ earlier, condition.inBounds before.roles.size = true)
    (failed : (before.activation scope).denote initial = 0 ∨
      ∀ earlier ∈ previous, ¬AllZero earlier initial) :
    ∃ assignment, Extension rom calls before after initial assignment := by
  induction previous generalizing before initial with
  | nil =>
      have same : before = after := by
        simpa [List.forIn_nil, pure, StateT.pure, StateT.bind, bind, Except.bind, Except.pure] using compiled
      subst after
      exact ⟨initial, .refl layout ((before.valid_iff_reference rom calls initial).mp valid)⟩
  | cons earlier previous ih =>
      simp only [List.forIn_cons, bind_assoc, pure_bind] at compiled
      obtain ⟨⟨⟩, middle, headRun, tailRun⟩ := bind_ok.mp compiled
      obtain ⟨a, headExt⟩ := failure_complete headRun layout valid (scopeLayout.activation_bound scope)
        (bounded earlier (by simp)) (failed.imp_right (fun failures => failures earlier (by simp)))
      obtain ⟨headStructure, headScoped⟩ := failure_scoped headRun scopeLayout scopeValid
      obtain ⟨b, tailExt⟩ := ih tailRun headExt.layout headScoped headExt.validAssignment
        (headStructure.scopeValid scopeValid)
        (fun earlier member p leaf => headExt.bound (bounded earlier (by simp [member]) p leaf)) (by
          rw [headExt.activation headStructure scopeLayout scopeValid]
          rcases failed with inactive | failures
          · exact Or.inl inactive
          · right
            intro earlier member zero
            apply failures earlier (by simp [member])
            intro p leaf
            rw [← headExt.polynomial (bounded earlier (by simp [member]) p leaf)]
            exact zero p leaf)
      exact ⟨b, headExt.trans tailExt⟩

end Aiur.Optimized.Compiler
