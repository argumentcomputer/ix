import IxVMRefinement.Decl.ReferencePreludeProps

/-! # The prepared prelude front contains no accepted theorem declaration -/

namespace IxVM.Refinement.Decl

open Ix.Kernel Ix.Kernel.Reader Ix.Kernel.Frontend

private theorem pickSpec_declares {md : Mode} {name : Option (Key md)} :
    ∀ {ds : List (Declaration md)} {d : Declaration md},
      (pickSpec name ds).1 = some d → declares name d = true
  | [], _, found => by cases found
  | first :: rest, d, found => by
    unfold pickSpec at found
    split at found
    · rename_i selected
      obtain rfl := Option.some.inj found
      exact selected
    · exact pickSpec_declares found

private theorem frontSpec_entry {md : Mode} :
    ∀ (prelude input : List (Declaration md)) {d : Declaration md},
      d ∈ (frontSpec prelude input).1 →
      ∃ p ∈ prelude, d = p ∨ declares (preludeKey p) d = true
  | [], _, _, member => by cases member
  | p :: ps, input, d, member => by
    change d ∈ (pickSpec (preludeKey p) input).1.getD p ::
      (frontSpec ps (pickSpec (preludeKey p) input).2).1 at member
    rcases List.mem_cons.mp member with first | rest
    · refine ⟨p, List.mem_cons_self, ?_⟩
      cases chosen : (pickSpec (preludeKey p) input).1 with
      | none =>
        simp only [chosen, Option.getD_none] at first
        exact Or.inl first
      | some selected =>
        simp only [chosen, Option.getD_some] at first
        subst d
        exact Or.inr (pickSpec_declares chosen)
    · obtain ⟨p, member, relation⟩ := frontSpec_entry ps _ rest
      exact ⟨p, List.mem_cons_of_mem _ member, relation⟩

private theorem prelude_head_cases {p : Declaration .anon} {name : Key .anon}
    (shape : p.names ∈ preludeShape.map (List.map Key.role))
    (head : preludeKey p = some name) :
    name ∈ [eqName, natName, punitName, emptyName, falseName,
      quotName, quotMkName, quotLiftName, quotIndName, quotSoundName, andName, boolName] := by
  simp only [preludeShape, List.map_cons, List.map_nil, List.mem_cons,
    List.not_mem_nil, or_false] at shape
  rcases shape with shape | shape | shape | shape | shape | shape |
    shape | shape | shape | shape | shape | shape
  all_goals
    rw [preludeKey, shape] at head
    obtain rfl := Option.some.inj head
    decide

/-- Any selected prelude-front theorem would have a forbidden prelude head name. -/
theorem ReferenceReplay.prepared_front_no_theorem
    {fuel : Nat} {ev : Evidences .anon} {sourceOut targetOut : Env .anon}
    {table : RoleTable} {pre : Prelude .anon} (prepared : preludeFor table = .ok pre)
    {input : Array (Declaration .anon)}
    (replay : ReferenceReplay fuel ev Env.empty Env.empty
      ((preparePrelude pre.ix input).toList.map IxVM.Refinement.thmToOpaqueDefn) sourceOut targetOut)
    (propositions : IxVM.Refinement.TheoremsInProp sourceOut (preparePrelude pre.ix input).toList)
    (anchors : IxVM.Refinement.AnchorsTyped (preparePrelude pre.ix input).toList)
    (cv : ConstantVal .anon) (value : Expr .anon) :
    Declaration.thmDecl cv value ∉ (frontOf #[] pre.ix.decls.toList input).1.toList := by
  intro member
  have fullMember : Declaration.thmDecl cv value ∈ (preparePrelude pre.ix input).toList := by
    rw [preparePrelude_front, Array.toList_append]
    exact List.mem_append_left _ member
  apply replay.theorem_not_prelude_head propositions anchors fullMember
  rw [(frontOf_toList pre.ix.decls.toList #[] input).1, Array.toList_empty,
    List.nil_append] at member
  obtain ⟨p, inPrelude, relation⟩ := frontSpec_entry _ _ member
  have shape : p.names ∈ preludeShape.map (List.map Key.role) := by
    rw [← preludeFor_shape prepared]
    exact List.mem_map_of_mem inPrelude
  apply prelude_head_cases shape
  rcases relation with rfl | chosen
  · rfl
  · unfold declares at chosen
    cases name : preludeKey p with
    | none => rw [name] at chosen; cases chosen
    | some key =>
      rw [name]
      simp only [name, Option.any_some, Declaration.names, List.contains_cons,
        List.contains_nil, Bool.or_false, beq_iff_eq] at chosen
      exact congrArg some chosen

end IxVM.Refinement.Decl
