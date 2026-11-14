import Aiur.LayoutComposition

namespace Aiur

private theorem forIn_values_ok {action : α → Except ε β} {items : List α}
    (checked : (do for item in items do let _ ← action item : Except ε Unit) = .ok ()) :
    ∀ item ∈ items, ∃ value, action item = .ok value := by
  induction items with
  | nil => simp
  | cons item items ih =>
      cases first : action item with
      | error error => simp [List.forIn_cons, first, bind, Except.bind] at checked
      | ok value =>
          simp only [List.forIn_cons, first, bind, Except.bind, pure, Except.pure] at checked
          intro other member
          rcases List.mem_cons.mp member with rfl | member
          · exact ⟨value, first⟩
          · exact ih checked other member

theorem checkDeclarations_enum_layout {decls : Declarations}
    (checked : checkDeclarations decls = .ok ()) {decl : EnumDecl} (member : decl ∈ decls) :
    ∃ layout, decls.layout (.enum decl.name) = .ok layout := by
  unfold checkDeclarations at checked
  split at checked
  · cases checked
  · simp only [pure_bind] at checked
    obtain ⟨done, _, rest⟩ := except_bind_ok.mp checked
    cases done
    exact forIn_values_ok (action := fun decl : EnumDecl => decls.layout (.enum decl.name)) rest decl member

/-- Checked declarations give a finite layout to every type whose names resolve. -/
theorem Declarations.layout_total {decls : Declarations}
    (checked : checkDeclarations decls = .ok ()) {type : Ty}
    (names : type.checkNames decls = .ok ()) : ∃ layout, decls.layout type = .ok layout := by
  cases type with
  | field => exact ⟨.field, Declarations.layout_field decls⟩
  | ptr target => exact ⟨.ptr target, Declarations.layout_ptr (by simpa only [Ty.checkNames] using names)⟩
  | enum name =>
      cases found : decls.findEnum? name with
      | none => simp [Ty.checkNames, found] at names
      | some decl =>
          have same : decl.name = name := by simpa using List.find?_some found
          simpa only [same] using checkDeclarations_enum_layout checked (List.mem_of_find?_eq_some found)
  | tuple types =>
      have each := forIn_ok (by simpa only [Ty.checkNames] using names)
      have existsLayouts : ∀ type ∈ types, ∃ layout, decls.layout type = .ok layout :=
        fun type member => Declarations.layout_total checked (each type member)
      have related : ∃ layouts, List.Forall₂ (fun type layout => decls.layout type = .ok layout) types layouts := by
        clear names each
        induction types with
        | nil => exact ⟨[], .nil⟩
        | cons type types ih =>
            obtain ⟨layout, expanded⟩ := existsLayouts type (by simp)
            obtain ⟨layouts, related⟩ := ih (fun t h => existsLayouts t (by simp [h]))
            exact ⟨layout :: layouts, .cons expanded related⟩
      obtain ⟨layouts, related⟩ := related
      exact ⟨.tuple layouts, Declarations.layout_tuple related⟩
termination_by sizeOf type

end Aiur
