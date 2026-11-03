import Aiur.Declarations
import Aiur.ExceptFacts
import Mathlib.Data.List.Monad
import Mathlib.Data.List.Forall2

namespace Aiur

/- A finite layout is obtained by unfolding the declared nominal constructors. -/
mutual
  inductive Layout.Describes (decls : Declarations) : Layout → Ty → Prop where
    | field : Layout.Describes decls .field .field
    | ptr : Layout.Describes decls (.ptr target) (.ptr target)
    | tuple : LayoutsDescribe decls layouts types →
        Layout.Describes decls (.tuple layouts) (.tuple types)
    | enum : decls.findEnum? name = some definition →
        ConstructorsDescribe decls constructors definition.constructors →
        Layout.Describes decls (.enum name constructors) (.enum name)

  inductive LayoutsDescribe (decls : Declarations) : List Layout → List Ty → Prop where
    | nil : LayoutsDescribe decls [] []
    | cons : Layout.Describes decls layout type → LayoutsDescribe decls layouts types →
        LayoutsDescribe decls (layout :: layouts) (type :: types)

  inductive ConstructorsDescribe (decls : Declarations) :
      List (String × Layout) → List ConstructorDecl → Prop where
    | nil : ConstructorsDescribe decls [] []
    | cons : name = ctor.name → Layout.Describes decls layout (.tuple ctor.fields) →
        ConstructorsDescribe decls layouts ctors →
        ConstructorsDescribe decls ((name, layout) :: layouts) (ctor :: ctors)
end

private theorem mapM_describes {f : α → Except ε β} {xs : List α} {ys : List β}
    (run : xs.mapM f = .ok ys) : List.Forall₂ (fun x y => f x = .ok y) xs ys := by
  induction xs generalizing ys with
  | nil =>
      simp [List.mapM_nil, pure, Except.pure] at run
      subst ys
      exact .nil
  | cons x xs ih =>
      cases first : f x with
      | error error => simp [List.mapM_cons, first, bind, Except.bind] at run
      | ok y =>
          cases rest : xs.mapM f with
          | error error => simp [List.mapM_cons, first, rest, bind, Except.bind] at run
          | ok zs =>
              simp [List.mapM_cons, first, rest, bind, Except.bind, pure, Except.pure] at run
              subst ys
              exact .cons first (ih rest)

private theorem layoutWith_describes {decls : Declarations}
    {resolve : String → Except DeclError Layout}
    (resolved : ∀ name layout, resolve name = .ok layout → Layout.Describes decls layout (.enum name))
    (type : Ty) {layout : Layout} (run : type.layoutWith resolve = .ok layout) :
    Layout.Describes decls layout type := by
  cases type with
  | field => simp only [Ty.layoutWith, Except.ok.injEq] at run; subst layout; exact .field
  | ptr => simp only [Ty.layoutWith, Except.ok.injEq] at run; subst layout; exact .ptr
  | enum name => exact resolved name layout (by simpa [Ty.layoutWith] using run)
  | tuple types =>
      cases mapped : types.mapM (Ty.layoutWith resolve) with
      | error error => simp [Ty.layoutWith, mapped, bind, Except.bind] at run
      | ok layouts =>
          simp [Ty.layoutWith, mapped, bind, Except.bind, pure, Except.pure] at run
          subst layout
          apply Layout.Describes.tuple
          have paired := mapM_describes mapped
          have recur : ∀ type ∈ types, ∀ layout, type.layoutWith resolve = .ok layout →
              Layout.Describes decls layout type := fun type member layout run =>
            layoutWith_describes resolved type run
          clear resolved mapped
          induction paired with
          | nil => exact .nil
          | cons head tail ih =>
              exact .cons (recur _ (by simp) _ head) (ih (fun t h => recur t (by simp [h])))
termination_by sizeOf type

/-- Successful expansion, at any depth, describes precisely the declared type. -/
theorem Declarations.expand_describes (decls : Declarations) (depth : Nat) (type : Ty)
    {layout : Layout} (run : decls.expand depth type = .ok layout) :
    Layout.Describes decls layout type := by
  induction depth generalizing type layout with
  | zero =>
      exact layoutWith_describes (decls := decls) (by intro name layout run; cases run) type run
  | succ depth ih =>
      simp only [Declarations.expand] at run
      apply layoutWith_describes (decls := decls) (type := type) (run := run)
      intro name layout resolved
      cases found : decls.findEnum? name with
      | none => simp [found] at resolved
      | some definition =>
          simp only [found] at resolved
          obtain ⟨constructors, mapped, finished⟩ := except_bind_ok.mp resolved
          have same := except_pure_ok.mp finished
          subst layout
          apply Layout.Describes.enum found
          have paired := mapM_describes mapped
          clear mapped run resolved found finished
          generalize hdefs : definition.constructors = definitions at paired ⊢
          clear hdefs
          induction paired with
          | nil => exact .nil
          | @cons ctor pair ctors pairs head tail recur =>
              obtain ⟨layouts, fields, finished⟩ := except_bind_ok.mp head
              have same := except_pure_ok.mp finished
              subst pair
              refine .cons rfl (.tuple ?_) recur
              have pairedFields := mapM_describes fields
              clear fields head finished
              generalize hfields : ctor.fields = types at pairedFields ⊢
              clear hfields
              induction pairedFields with
              | nil => exact .nil
              | cons h hs recur => exact .cons (ih _ h) recur

theorem Declarations.layout_describes {decls : Declarations} {type : Ty} {layout : Layout}
    (run : decls.layout type = .ok layout) : Layout.Describes decls layout type := by
  unfold Declarations.layout at run
  cases names : type.checkNames decls with
  | error error => simp [names, bind, Except.bind] at run
  | ok done => exact decls.expand_describes _ type (by simpa [names, bind, Except.bind] using run)

/-- Layout expansion preserves the nominal type, independently of field encodings. -/
theorem Layout.Describes.type {decls : Declarations} {layout : Layout} {ty : Ty}
    (described : layout.Describes decls ty) : layout.type = ty := by
  induction described using Layout.Describes.rec
    (motive_2 := fun layouts types _ => layouts.map Layout.type = types)
    (motive_3 := fun _ _ _ => True) <;> simp_all [Layout.type]

end Aiur
