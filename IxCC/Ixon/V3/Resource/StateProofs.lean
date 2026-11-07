import IxCC.Ixon.V3.Resource.State

namespace IxCC.Ixon.V3.Resource

/-- The meaning of an internal scope bound, independent of the executable
fuel-bounded ancestor walk. -/
inductive Ancestor (parents : Array (Option ScopeId)) (origin : ScopeId) : ScopeId → Prop
  | here (h : origin < parents.size) : Ancestor parents origin origin
  | parent {scope parent : ScopeId} (h : parents[scope]? = some (some parent))
      (outer : Ancestor parents origin parent) : Ancestor parents origin scope

/-- Generated parent tables point strictly backwards. -/
def ScopeTree (parents : Array (Option ScopeId)) : Prop :=
  ∀ (scope parent : ScopeId), parents[scope]? = some (some parent) → parent < scope

theorem root_scopeTree : ScopeTree #[none] := by
  intro scope parent h
  cases scope <;> simp at h

theorem push_scopeTree (parents : Array (Option ScopeId)) (parent : ScopeId)
    (tree : ScopeTree parents) (valid : parent < parents.size) :
    ScopeTree (parents.push (some parent)) := by
  intro scope outer h
  rw [Array.getElem?_push] at h
  split at h
  · rename_i same
    cases h
    simpa [same] using valid
  · exact tree scope outer h

theorem ancestor_older (parents : Array (Option ScopeId)) (origin destination : ScopeId)
    (tree : ScopeTree parents) (h : Ancestor parents origin destination) : origin ≤ destination := by
  induction h with
  | here => exact Nat.le_refl _
  | parent lookup _ ih =>
    have older := tree _ _ lookup
    exact Nat.le_trans ih (Nat.le_of_lt older)

theorem outlivesAux_sound (parents : Array (Option ScopeId)) (origin fuel destination : Nat)
    (h : outlivesAux parents origin fuel destination = true) :
    Ancestor parents origin destination := by
  induction fuel generalizing destination with
  | zero => simp [outlivesAux] at h
  | succ fuel ih =>
    simp only [outlivesAux] at h
    split at h
    · simp at h
    · rename_i valid
      split at h
      · rename_i same
        have eq : origin = destination := by simpa using same
        subst destination
        apply Ancestor.here
        have inside : ¬ origin >= parents.size := by
          intro outside
          exact valid (by simp [outside])
        exact Nat.lt_of_not_ge inside
      · split at h
        · rename_i parent hp
          exact Ancestor.parent hp (ih parent h)
        · simp at h

theorem outlives_sound (parents : Array (Option ScopeId)) (origin destination : Nat)
    (h : outlives parents origin destination = true) : Ancestor parents origin destination :=
  outlivesAux_sound parents origin _ destination h

theorem fresh_scope_cannot_escape (parents : Array (Option ScopeId)) (parent destination : ScopeId)
    (tree : ScopeTree parents) (valid : parent < parents.size) (older : destination < parents.size) :
    outlives (parents.push (some parent)) parents.size destination = false := by
  cases result : outlives (parents.push (some parent)) parents.size destination with
  | false => rfl
  | true =>
    have ancestor := outlives_sound _ _ _ result
    have order := ancestor_older _ _ _ (push_scopeTree parents parent tree valid) ancestor
    exact False.elim ((Nat.not_le_of_lt older) order)

theorem checkOrigins_sound (parents : Array (Option ScopeId)) (origins : List ScopeId)
    (destination : ScopeId) (h : checkOrigins parents origins destination = .ok ()) :
    ∀ origin ∈ origins, Ancestor parents origin destination := by
  induction origins with
  | nil => simp
  | cons origin rest ih =>
    simp only [checkOrigins] at h
    split at h
    · rename_i allowed
      intro x hx
      simp only [List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact outlives_sound parents x destination allowed
      · exact ih h x hx
    · simp at h

@[simp] theorem endLoan_live (scope : ScopeId) (owner : Owner) :
    (endLoan scope owner).live = owner.live := rfl

@[simp] theorem endLoan_unique (scope : ScopeId) (owner : Owner) :
    (endLoan scope owner).unique = owner.unique := rfl

theorem moveOwner_requires (id : OwnerId) (before after : Owner)
    (h : moveOwner id before = .ok after) :
    before.live = true ∧ before.unique = true ∧ before.loans = [] ∧ after.live = false := by
  rcases before with ⟨live, unique, loans⟩
  cases live <;> cases unique <;> cases loans <;>
    simp_all [moveOwner]
  cases h
  rfl

theorem shareOwner_permanent (id : OwnerId) (before after : Owner)
    (h : shareOwner id before = .ok after) : after.unique = false := by
  rcases before with ⟨live, unique, loans⟩
  cases live <;> simp_all [shareOwner]
  cases h
  rfl

theorem checkUnrestricted_sound (origins : List ScopeId)
    (h : checkUnrestricted origins = .ok ()) : origins = [] := by
  cases origins <;> simp_all [checkUnrestricted]

theorem joinOwner_live (left right : Owner)
    (h : (joinOwner left right).live = true) : left.live = true ∧ right.live = true := by
  simpa [joinOwner] using h

theorem joinOwner_unique (left right : Owner)
    (h : (joinOwner left right).unique = true) :
    left.unique = true ∧ right.unique = true := by
  simpa [joinOwner] using h

theorem checkDemand_sound (id : OwnerId) (declared actual : Uses) (count : Nat)
    (accepted : checkDemand id declared actual = .ok ()) (demand : actual.admits count) :
    declared.admits count := by
  simp only [checkDemand] at accepted
  split at accepted
  · rename_i covers
    exact Uses.covers_sound declared actual count covers demand
  · simp at accepted

end IxCC.Ixon.V3.Resource
