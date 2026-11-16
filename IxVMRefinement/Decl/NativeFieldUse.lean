import IxVMRefinement.Decl.NativeFront

/-! # Constructor field use forced by the checked return spine

A non-indexed constructor returns only its parameters. Its final field is therefore unused
in the residual, independently of typing or positivity. This closes the dependency condition
for constructors with at most one field while leaving earlier-field dependence separate.
-/

namespace IxVM.Refinement.Decl

open Ix.Kernel

private theorem app_spine_unused {md : Mode} {index : Nat} :
    ∀ (args : List (Expr md)) (head : Expr md),
      head.hasLooseBVar index = false →
      (∀ arg ∈ args, arg.hasLooseBVar index = false) →
      (Expr.mkAppN head args).hasLooseBVar index = false
  | [], _, headUnused, _ => headUnused
  | arg :: rest, head, headUnused, argsUnused => by
    apply app_spine_unused rest (.app head arg)
    · simp only [Expr.hasLooseBVar, headUnused, argsUnused arg List.mem_cons_self, Bool.false_or]
    · intro next member
      exact argsUnused next (List.mem_cons_of_mem _ member)

/-- The parameter spine has no reference to any of the intervening field binders. -/
theorem structPsAt_unused_below {md : Mode} {fields parameters index : Nat}
    (beforeParameters : index < fields) :
    ∀ arg ∈ (structPsAt fields parameters : List (Expr md)), arg.hasLooseBVar index = false := by
  intro arg member
  obtain ⟨position, bound, rfl⟩ := List.mem_map.mp member
  have positionBound := List.mem_range.mp bound
  simp only [Expr.hasLooseBVar]
  exact beq_eq_false_iff_ne.mpr (by omega)

/-- A non-indexed constructor's last field is absent from its checked return spine. -/
theorem structUsedLater_last_noIndices {md : Mode} {type : Expr md}
    {parameters fields index : Nat} {T : Key md} {levels : List Level}
    {binders : List (Expr md × BinderMeta)}
    (telescope : type.stripPis (parameters + fields) =
      some (binders, Expr.mkAppN (.const T levels) (structPsAt fields parameters)))
    (last : index + 1 = fields) : structUsedLater type parameters index = false := by
  have count : parameters + index + 1 = parameters + fields := by omega
  simp only [structUsedLater, count, telescope, Expr.hasLooseBVarB_eq]
  exact app_spine_unused _ _ rfl (structPsAt_unused_below (by omega))

/-- The actual checked constructor output discharges its final field's use condition when
the family has no indices. -/
theorem NativeCtorOut.unused_last {env : Env .anon} {T : Core.KKey}
    {levels : List LevelParam} {parameters indices : Nat} {sortLevel : Core.KLevel}
    {former raw : Core.KExpr} {ctor annotated : KConstantVal × Nat} {sorts : List Core.KLevel}
    (checked : NativeCtorOut env T levels parameters indices sortLevel former raw ctor annotated sorts)
    (noIndices : indices = 0) {index : Nat} (last : index + 1 = annotated.2) :
    structUsedLater annotated.1.type parameters index = false := by
  obtain ⟨_, _, binders, arguments, _, _, telescope, _, argumentCount, _⟩ := checked.residual
  have empty : arguments = [] := List.length_eq_zero_iff.mp (argumentCount.trans noIndices)
  rw [empty, List.append_nil] at telescope
  exact structUsedLater_last_noIndices telescope (last.trans checked.nF_eq)

/-- No caller dependency witness is needed for a non-indexed constructor with at most one
field; any field present is already the last field. -/
theorem NativeCtorOut.unused_single_field {env : Env .anon} {T : Core.KKey}
    {levels : List LevelParam} {parameters indices : Nat} {sortLevel : Core.KLevel}
    {former raw : Core.KExpr} {ctor annotated : KConstantVal × Nat} {sorts : List Core.KLevel}
    (checked : NativeCtorOut env T levels parameters indices sortLevel former raw ctor annotated sorts)
    (noIndices : indices = 0) (atMostOne : annotated.2 ≤ 1) :
    ∀ index < annotated.2, structUsedLater annotated.1.type parameters index = false := by
  intro index present
  exact checked.unused_last noIndices (by omega)

/-- If every earlier field is free of the family, any recursive or reflexive field is
last. Its unused-later condition therefore follows from the actual checked return spine. -/
theorem NativeCtorOut.unused_recursive_last {env : Env .anon} {T : Core.KKey}
    {levels : List LevelParam} {parameters : Nat} {sortLevel : Core.KLevel}
    {former raw : Core.KExpr} {ctor annotated : KConstantVal × Nat} {sorts : List Core.KLevel}
    (checked : NativeCtorOut env T levels parameters 0 sortLevel former raw ctor annotated sorts)
    {binders : List (Core.KExpr × BinderMeta)} {body : Core.KExpr}
    (_telescope : annotated.1.type.stripPis (parameters + annotated.2) = some (binders, body))
    (earlier : ∀ index, index + 1 < annotated.2 →
      (binders.getD (parameters + index) default).1.mentionsConst T = false) :
    ∀ index < annotated.2,
      (recFieldKind T levels parameters 0 index
          (binders.getD (parameters + index) default).1 = .recursive ∨
        recFieldKind T levels parameters 0 index
          (binders.getD (parameters + index) default).1 = .reflexive) →
      structUsedLater annotated.1.type parameters index = false := by
  intro index present recursive
  by_cases last : index + 1 = annotated.2
  · exact checked.unused_last rfl last
  · have free := earlier index (by omega)
    simp only [recFieldKind, free, Bool.false_eq_true, ↓reduceIte] at recursive
    rcases recursive with impossible | impossible <;> cases impossible

end IxVM.Refinement.Decl
