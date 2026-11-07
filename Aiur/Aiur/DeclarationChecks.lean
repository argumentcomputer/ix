import Aiur.DeclarationFacts
import Aiur.WireCanonical
import Mathlib.Data.List.Nodup

namespace Aiur

private theorem duplicateName_none {names seen : List String}
    (checked : duplicateName names seen = none) : names.Nodup ∧ ∀ name ∈ names, name ∉ seen := by
  induction names generalizing seen with
  | nil => simp
  | cons name names ih =>
      simp only [duplicateName] at checked
      split at checked
      · cases checked
      · rename_i fresh
        obtain ⟨unique, absent⟩ := ih checked
        refine ⟨List.nodup_cons.mpr ⟨?_, unique⟩, ?_⟩
        · intro member
          exact absent name member (by simp)
        · intro value member
          rcases List.mem_cons.mp member with rfl | member
          · exact fresh
          · intro seenMember
            exact absent value member (by simp [seenMember])

theorem checkDeclarations_names {decls : Declarations} (checked : checkDeclarations decls = .ok ()) :
    (decls.map EnumDecl.name).Nodup ∧ ∀ decl ∈ decls, (decl.constructors.map ConstructorDecl.name).Nodup := by
  unfold checkDeclarations at checked
  cases duplicate : duplicateName (decls.map EnumDecl.name) [] with
  | some name => simp [duplicate, bind, Except.bind] at checked
  | none =>
      simp only [duplicate, pure_bind] at checked
      obtain ⟨done, entries, _⟩ := except_bind_ok.mp checked
      cases done
      have each := forIn_ok (action := checkEnum decls) (by
        have combined := congrArg (fun r : Except DeclError PUnit => r >>= fun _ =>
          (pure () : Except DeclError Unit)) entries
        simpa only [bind, Except.bind, pure, Except.pure] using combined)
      refine ⟨(duplicateName_none duplicate).1, ?_⟩
      intro decl member
      have valid := each decl member
      cases repeated : duplicateName (decl.constructors.map ConstructorDecl.name) [] with
      | none => exact (duplicateName_none repeated).1
      | some name =>
          by_cases reserved : decl.name = "Field"
          · simp [checkEnum, reserved, repeated, bind, Except.bind, pure, Except.pure] at valid
          · cases empty : decl.constructors.isEmpty <;>
              simp [checkEnum, reserved, empty, repeated, bind, Except.bind, pure, Except.pure] at valid


theorem Layout.Describes.namesUnique {decls : Declarations}
    (names : ∀ decl ∈ decls, (decl.constructors.map ConstructorDecl.name).Nodup)
    {layout : Layout} {ty : Ty} (described : layout.Describes decls ty) : layout.NamesUnique := by
  refine Layout.Describes.rec
    (motive_1 := fun layout _ _ => layout.NamesUnique)
    (motive_2 := fun layouts _ _ => ∀ layout ∈ layouts, layout.NamesUnique)
    (motive_3 := fun layouts ctors _ => layouts.map Prod.fst = ctors.map ConstructorDecl.name ∧
      ∀ pair ∈ layouts, pair.2.NamesUnique)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ described
  · simp [Layout.NamesUnique]
  · intro target; simp [Layout.NamesUnique]
  · intro layouts types related ih
    simpa only [Layout.NamesUnique] using ih
  · intro name definition constructors found related ih
    simp only [Layout.NamesUnique]
    exact ⟨by rw [ih.1]; exact names _ (List.mem_of_find?_eq_some found), ih.2⟩
  · simp
  · intro layout type layouts types head tail h t
    simpa using And.intro h t
  · simp
  · intro name layout layouts ctors ctor same head tail h t
    exact ⟨by simp [same, t.1], by simpa using And.intro h t.2⟩

theorem tagsDistinct_zero [NatCast F] {count : Nat}
    (tags : ((List.range count).map (fun i : Nat => (i : F))).Nodup) : TagsDistinct F 0 count := by
  intro i j _ hi _ hj same
  exact List.inj_on_of_nodup_map tags (by simpa using hi) (by simpa using hj) same

theorem Layout.Describes.tagSafe [NatCast F]
    {decls : Declarations} (tags : ∀ decl ∈ decls, TagsDistinct F 0 decl.constructors.length)
    {layout : Layout} {ty : Ty} (described : layout.Describes decls ty) : layout.TagSafe F := by
  refine Layout.Describes.rec
    (motive_1 := fun layout _ _ => layout.TagSafe F)
    (motive_2 := fun layouts _ _ => ∀ layout ∈ layouts, layout.TagSafe F)
    (motive_3 := fun layouts ctors _ => layouts.length = ctors.length ∧
      ∀ pair ∈ layouts, pair.2.TagSafe F)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ described
  · simp [Layout.TagSafe]
  · intro target; simp [Layout.TagSafe]
  · intro layouts types related ih
    simpa only [Layout.TagSafe] using ih
  · intro name definition constructors found related ih
    simp only [Layout.TagSafe]
    exact ⟨by rw [ih.1]; exact tags _ (List.mem_of_find?_eq_some found), ih.2⟩
  · simp
  · intro layout type layouts types head tail h t
    simpa using And.intro h t
  · simp
  · intro name layout layouts ctors ctor same head tail h t
    exact ⟨by simp [t.1], by simpa using And.intro h t.2⟩

end Aiur
