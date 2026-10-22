import Aiur.DeclarationFacts

namespace Aiur

/-- Successful finite unfoldings of the same nominal type have the same layout. -/
theorem Layout.Describes.unique {decls : Declarations} {layout : Layout} {ty : Ty}
    (described : layout.Describes decls ty) {other : Layout}
    (also : other.Describes decls ty) : layout = other := by
  have all : ∀ other, other.Describes decls ty → layout = other := by
    refine Layout.Describes.rec
      (motive_1 := fun layout ty _ => ∀ other, Layout.Describes decls other ty → layout = other)
      (motive_2 := fun layouts types _ => ∀ others, LayoutsDescribe decls others types → layouts = others)
      (motive_3 := fun layouts ctors _ => ∀ others, ConstructorsDescribe decls others ctors → layouts = others)
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ described
    · intro other related; cases related; rfl
    · intro target other related; cases related; rfl
    · intro layouts types related ih other also
      cases also with
      | tuple more => rw [ih _ more]
    · intro name definition constructors found related ih other also
      cases also with
      | enum found' more =>
          have same := Option.some.inj (found.symm.trans found')
          subst same
          rw [ih _ more]
    · intro others related; cases related; rfl
    · intro layout type layouts types head tail h t others related
      cases related with
      | cons head' tail' => rw [h _ head', t _ tail']
    · intro others related; cases related; rfl
    · intro name layout layouts ctors ctor same head tail h t others related
      cases related with
      | cons same' head' tail' => rw [same, same', h _ head', t _ tail']
  exact all other also

end Aiur
