import Ix.CompileCert.Canon.ConstructorOwnership

namespace Ix.Compile.Canon.FreshFamilySeparation

/-- Two ancestors of one structural name lie on the same prefix chain. -/
theorem prefix_comparable {a b n : Lean.Name}
    (ha : a.isPrefixOf n = true) (hb : b.isPrefixOf n = true) :
    a.isPrefixOf b = true ∨ b.isPrefixOf a = true := by
  induction n with
  | anonymous =>
    have same : a = .anonymous := by simpa [Lean.Name.isPrefixOf] using ha
    subst a
    exact Or.inr hb
  | str n s ih =>
    have left : a = .str n s ∨ a.isPrefixOf n = true := by
      simpa [Lean.Name.isPrefixOf] using ha
    have right : b = .str n s ∨ b.isPrefixOf n = true := by
      simpa [Lean.Name.isPrefixOf] using hb
    rcases left with rfl | left
    · exact Or.inr hb
    rcases right with rfl | right
    · exact Or.inl ha
    exact ih left right
  | num n i ih =>
    have left : a = .num n i ∨ a.isPrefixOf n = true := by
      simpa [Lean.Name.isPrefixOf] using ha
    have right : b = .num n i ∨ b.isPrefixOf n = true := by
      simpa [Lean.Name.isPrefixOf] using hb
    rcases left with rfl | left
    · exact Or.inr hb
    rcases right with rfl | right
    · exact Or.inl ha
    exact ih left right

/-- Descendants of separated prefix families remain separated. -/
theorem Apart.descendants {a b x y : Lean.Name} (h : Apart a b)
    (hx : a.isPrefixOf x = true) (hy : b.isPrefixOf y = true) : Apart x y := by
  have forward {a b x y : Lean.Name} (h : Apart a b)
      (hx : a.isPrefixOf x = true) (hy : b.isPrefixOf y = true) :
      x.isPrefixOf y = false := by
    apply Bool.eq_false_iff.mpr
    intro hxy
    rcases prefix_comparable (prefix_trans hx hxy) hy with hab | hba
    · rw [h.1] at hab
      cases hab
    · rw [h.2] at hba
      cases hba
  exact ⟨forward h hx hy, forward h.symm hy hx⟩

/-- Internal finite allocation invariant. `roots` is a proof-side history of
actual auxiliary allocations, including a newly reserved root while its
constructors are being built. It is not a source-domain premise. -/
structure AllocationForest (parent : Lean.Name) (roots ctors : List Lean.Name) : Prop where
  rootShape : ∀ root ∈ roots, AuxRoot parent root
  rootApart : roots.Pairwise Apart
  ctorOwner : ∀ ctor ∈ ctors, ∃ owner ∈ roots,
    owner.isPrefixOf ctor = true ∧ ctor ≠ owner
  ctorApart : ctors.Pairwise Apart

theorem AllocationForest.empty (parent : Lean.Name) : AllocationForest parent [] [] := by
  constructor <;> simp

/-- The inverse prefix fact needed by the constructor fallback is derived
from existing ownership, even when the current root is the same owner. -/
theorem AllocationForest.ctor_not_prefix_root
    {parent : Lean.Name} {roots ctors : List Lean.Name}
    (forest : AllocationForest parent roots ctors) {current : Lean.Name}
    (shape : AuxRoot parent current) :
    ∀ old ∈ ctors, old.isPrefixOf current = false := by
  intro old member
  obtain ⟨owner,owned,child,strict⟩ := forest.ctorOwner old member
  exact ctorRoot_not_prefix_auxRoot (forest.rootShape owner owned) shape child strict

/-- Reserving a fresh root extends the finite forest. The only membership
condition here is on the actual internal forbidden list, established by the
runtime state's allocated-name history. -/
theorem AllocationForest.reserve
    {roots ctors : List Lean.Name} {parent : Ix.Name}
    (forest : AllocationForest (keyName parent) roots ctors)
    (forbidden : List Lean.Name) (covers : ∀ root ∈ roots, root ∈ forbidden)
    (label : String) :
    AllocationForest (keyName parent)
      (keyName (freshFamily forbidden parent label) :: roots) ctors := by
  constructor
  · intro root member
    rcases List.mem_cons.mp member with rfl | old
    · exact freshFamily_shape forbidden parent label
    · exact forest.rootShape root old
  · apply List.pairwise_cons.mpr
    refine ⟨?_, forest.rootApart⟩
    intro old member
    exact freshFamily_apart_old_aux forbidden parent label old
      (covers old member) (forest.rootShape old member)
  · intro ctor member
    obtain ⟨owner,owned,child,strict⟩ := forest.ctorOwner ctor member
    exact ⟨owner,List.mem_cons_of_mem _ owned,child,strict⟩
  · exact forest.ctorApart

/-- Adding the actual constructor allocation preserves strict ownership and
pairwise separation without requiring source constructor-prefix facts. The
source query is protected by the independently proved source-read closure. -/
theorem AllocationForest.addCtor
    {roots ctors : List Lean.Name} {parent : Lean.Name}
    (forest : AllocationForest parent roots ctors)
    (forbidden : List Lean.Name) (aux source old : Ix.Name) (index : Nat)
    (owned : keyName aux ∈ roots) (hsource : keyName source ∈ forbidden) :
    let generated := freshCtorFamily forbidden aux (nameReplacePrefix source old aux) index ctors
    AllocationForest parent roots (keyName generated :: ctors) := by
  dsimp only
  have ownership := freshCtorFamily_owner forbidden aux source old index ctors hsource
  constructor
  · exact forest.rootShape
  · exact forest.rootApart
  · intro ctor member
    rcases List.mem_cons.mp member with rfl | member
    · exact ⟨keyName aux,owned,ownership⟩
    · exact forest.ctorOwner ctor member
  · apply List.pairwise_cons.mpr
    refine ⟨?_, forest.ctorApart⟩
    intro previous member
    exact freshCtorFamily_apart_ctorRoot forbidden aux (nameReplacePrefix source old aux)
      index ctors previous member
      (forest.ctor_not_prefix_root (forest.rootShape _ owned) previous member)

/-- Every generated constructor is separate from every generated auxiliary
root other than its own; from its own root it is a strict descendant. -/
theorem AllocationForest.ctor_root_relation
    {parent : Lean.Name} {roots ctors : List Lean.Name}
    (forest : AllocationForest parent roots ctors)
    {ctor root : Lean.Name} (hc : ctor ∈ ctors) (hr : root ∈ roots) :
    (root.isPrefixOf ctor = true ∧ ctor ≠ root) ∨ Apart ctor root := by
  obtain ⟨owner,owned,child,strict⟩ := forest.ctorOwner ctor hc
  by_cases same : owner = root
  · subst owner
    exact Or.inl ⟨child,strict⟩
  · have separate := auxRoot_apart_of_ne (forest.rootShape _ owned)
      (forest.rootShape _ hr) same
    exact Or.inr (separate.descendants child (prefix_refl root))

end Ix.Compile.Canon.FreshFamilySeparation
