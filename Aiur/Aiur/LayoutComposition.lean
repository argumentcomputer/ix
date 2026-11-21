import Aiur.EncodingTypes
import Aiur.LayoutUnique

namespace Aiur

theorem forIn_success {action : α → Except ε Unit} {items : List α}
    (checked : ∀ item ∈ items, action item = .ok ()) :
    (do for item in items do action item : Except ε Unit) = .ok () := by
  induction items with
  | nil => rfl
  | cons item items ih =>
      simpa [List.forIn_cons, checked item (by simp), bind, Except.bind, pure, Except.pure] using
        ih (fun x h => checked x (by simp [h]))

theorem mapM_ok_of_forall₂ {action : α → Except ε β} {items : List α} {values : List β}
    (related : List.Forall₂ (fun item value => action item = .ok value) items values) :
    items.mapM action = .ok values := by
  induction related with
  | nil => rfl
  | cons head tail ih => simp [List.mapM_cons, head, ih, bind, Except.bind, pure, Except.pure]

theorem Declarations.layout_parts {decls : Declarations} {ty : Ty} {layout : Layout}
    (expanded : decls.layout ty = .ok layout) :
    ty.checkNames decls = .ok () ∧ decls.expand (decls.length + 1) ty = .ok layout := by
  unfold Declarations.layout at expanded
  obtain ⟨⟨⟩, names, inner⟩ := except_bind_ok.mp expanded
  exact ⟨names, inner⟩

theorem Declarations.layout_field (decls : Declarations) : decls.layout .field = .ok .field := by
  simp [Declarations.layout, Ty.checkNames, Declarations.expand, Ty.layoutWith, bind, Except.bind]

theorem Declarations.layout_ptr {decls : Declarations} {target : Ty}
    (names : target.checkNames decls = .ok ()) : decls.layout (.ptr target) = .ok (.ptr target) := by
  simp [Declarations.layout, Ty.checkNames, names, Declarations.expand, Ty.layoutWith, bind, Except.bind]

/-- Tuple composition preserves each component's independently computed inline layout. -/
theorem Declarations.layout_tuple {decls : Declarations} {types : List Ty} {layouts : List Layout}
    (related : List.Forall₂ (fun ty layout => decls.layout ty = .ok layout) types layouts) :
    decls.layout (.tuple types) = .ok (.tuple layouts) := by
  have names : ∀ ty ∈ types, ty.checkNames decls = .ok () := by
    induction related with
    | nil => simp
    | cons head tail ih => simpa using And.intro (Declarations.layout_parts head).1 ih
  have expanded : List.Forall₂
      (fun ty layout => decls.expand (decls.length + 1) ty = .ok layout) types layouts :=
    related.imp (fun _ _ h => (Declarations.layout_parts h).2)
  have expansion := mapM_ok_of_forall₂ expanded
  have checked : (Ty.tuple types).checkNames decls = .ok () := by
    simpa only [Ty.checkNames] using forIn_success names
  simp only [Declarations.expand] at expansion
  simp only [Declarations.layout, checked, bind, Except.bind]
  simp only [Declarations.expand, Ty.layoutWith]
  rw [expansion]
  rfl

end Aiur
