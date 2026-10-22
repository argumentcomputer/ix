import Aiur.DeclarationFacts

namespace Aiur

/-- Every constructor payload is a tuple layout, recursively through inline enums. -/
def Layout.TuplePayloads : Layout → Prop
  | .field | .ptr _ => True
  | .tuple layouts => ∀ layout ∈ layouts, layout.TuplePayloads
  | .enum _ constructors => ∀ pair ∈ constructors,
      (∃ layouts, pair.2 = .tuple layouts) ∧ pair.2.TuplePayloads
termination_by layout => sizeOf layout
decreasing_by
  all_goals simp_wf
  all_goals
    have h := List.sizeOf_lt_of_mem ‹_ ∈ _›
    first | omega | cases ‹String × Layout›; simp_all only [Prod.mk.sizeOf_spec]; omega

theorem Layout.Describes.tuple_shape {decls : Declarations} {layout : Layout} {types : List Ty}
    (described : layout.Describes decls (.tuple types)) : ∃ layouts, layout = .tuple layouts := by
  cases described with
  | tuple => exact ⟨_, rfl⟩

theorem Layout.Describes.tuplePayloads {decls : Declarations} {layout : Layout} {ty : Ty}
    (described : layout.Describes decls ty) : layout.TuplePayloads := by
  induction described using Layout.Describes.rec
    (motive_2 := fun layouts _ _ => ∀ layout ∈ layouts, layout.TuplePayloads)
    (motive_3 := fun constructors _ _ => ∀ pair ∈ constructors,
      (∃ layouts, pair.2 = .tuple layouts) ∧ pair.2.TuplePayloads) <;>
    simp_all [Layout.TuplePayloads]
  all_goals first
    | assumption
    | exact ⟨Layout.Describes.tuple_shape ‹Layout.Describes _ _ (.tuple _)›, by assumption⟩
    | aesop

end Aiur
