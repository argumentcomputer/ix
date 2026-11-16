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
      simp only [name, Option.any_some, Declaration.names, List.contains_cons,
        List.contains_nil, Bool.or_false, beq_iff_eq] at chosen
      exact congrArg some chosen

private theorem frontSpec_length {md : Mode} :
    ∀ (prelude input : List (Declaration md)), (frontSpec prelude input).1.length = prelude.length
  | [], _ => rfl
  | _ :: prelude, _ => by
    simp only [frontSpec, List.length_cons, frontSpec_length]

/-- The selected front has the required length and consists of complete singleton units. -/
theorem prepared_front_properties {table : RoleTable} {pre : Prelude .anon}
    (prepared : preludeFor table = .ok pre) (input : Array (Declaration .anon)) :
    (frontOf #[] pre.ix.decls.toList input).1.toList.length = preludeSize ∧
      ∀ d ∈ (frontOf #[] pre.ix.decls.toList input).1.toList, d.isGenerated = false := by
  rw [(frontOf_toList pre.ix.decls.toList #[] input).1, Array.toList_empty, List.nil_append]
  refine ⟨?_, ?_⟩
  · rw [frontSpec_length, Array.length_toList, preludeFor_size prepared]
  · intro d member
    obtain ⟨p, inPrelude, relation⟩ := frontSpec_entry _ _ member
    rcases relation with rfl | chosen
    · exact IxVM.Refinement.Assembly.preludeFor_decls_not_generated prepared _ inPrelude
    · have shape : p.names ∈ preludeShape.map (List.map Key.role) := by
        rw [← preludeFor_shape prepared]
        exact List.mem_map_of_mem inPrelude
      unfold declares at chosen
      cases name : preludeKey p with
      | none => rw [name] at chosen; cases chosen
      | some key =>
        have heads := prelude_head_cases shape name
        have notAux : key.isAux = false := by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at heads
          rcases heads with h | h | h | h | h | h | h | h | h | h | h | h <;> rw [h] <;> rfl
        have named : key ∈ d.names := by
          simpa only [name, Option.any_some, List.contains_iff_mem] using chosen
        cases generated : d.isGenerated with
        | false => rfl
        | true =>
          simp only [Declaration.isGenerated, Bool.and_eq_true] at generated
          have auxiliary := List.all_eq_true.mp generated.2 key named
          rw [notAux] at auxiliary
          cases auxiliary

/-- Every public theorem in the actual prepared stream closes a unit after the prelude. -/
theorem ReferenceReplay.prepared_theorem_unit
    {fuel : Nat} {ev : Evidences .anon} {sourceOut targetOut : Env .anon}
    {table : RoleTable} {pre : Prelude .anon} (prepared : preludeFor table = .ok pre)
    {input : Array (Declaration .anon)}
    (replay : ReferenceReplay fuel ev Env.empty Env.empty
      ((preparePrelude pre.ix input).toList.map IxVM.Refinement.thmToOpaqueDefn) sourceOut targetOut)
    (propositions : IxVM.Refinement.TheoremsInProp sourceOut (preparePrelude pre.ix input).toList)
    (anchors : IxVM.Refinement.AnchorsTyped (preparePrelude pre.ix input).toList)
    {cv : ConstantVal .anon} {value : Expr .anon}
    (member : Declaration.thmDecl cv value ∈ (preparePrelude pre.ix input).toList)
    (publicName : cv.name.isAux = false) :
    ∃ before after generated,
      unitsOf (preparePrelude pre.ix input).toList =
        before ++ (generated ++ [.thmDecl cv value]) :: after ∧
      (∀ d ∈ generated, d.isGenerated = true) ∧
      preludeSize ≤ before.flatten.length := by
  let front := (frontOf #[] pre.ix.decls.toList input).1.toList
  let body := (hoistNatOpGround (frontOf #[] pre.ix.decls.toList input).2).1.toList
  have declarations : (preparePrelude pre.ix input).toList = front ++ body := by
    rw [preparePrelude_front, Array.toList_append]
  have notInFront := replay.prepared_front_no_theorem prepared propositions anchors cv value
  have inBody : Declaration.thmDecl cv value ∈ body := by
    rw [declarations, List.mem_append] at member
    exact member.resolve_left notInFront
  have notGenerated : (Declaration.thmDecl cv value).isGenerated = false := by
    simp only [Declaration.isGenerated, Declaration.names, List.isEmpty_cons, Bool.not_false,
      List.all_cons, List.all_nil, publicName, Bool.false_and, Bool.and_false]
  obtain ⟨before, after, generated, split, allGenerated⟩ := unitsOf_closer inBody notGenerated
  obtain ⟨frontLength, frontNotGenerated⟩ := prepared_front_properties prepared input
  refine ⟨front.map (fun d => [d]) ++ before, after, generated, ?_, allGenerated, ?_⟩
  · rw [declarations, unitsOf_append_front front body frontNotGenerated, split, List.append_assoc]
  · have frontFlat : (front.map fun d => [d]).flatten = front := by
      induction front with
      | nil => rfl
      | cons d rest ih => simp only [List.map_cons, List.flatten_cons, ih, List.singleton_append]
    rw [List.flatten_append, frontFlat, List.length_append]
    change preludeSize ≤ front.length + before.flatten.length
    change front.length = preludeSize at frontLength
    omega

end IxVM.Refinement.Decl
