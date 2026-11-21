import Aiur.Tables
import Aiur.Memory.Representation

namespace Aiur

variable {F : Type} {rom : ROM F} {heap : Heap F}

namespace RepresentsArgs

theorem types {sources : List (SourceValue F)} {targets : List (Value F)}
    (related : RepresentsArgs rom heap sources targets) :
    sources.map Value.type = targets.map Value.type := by
  induction related with
  | nil => rfl
  | cons head _ ih => simp only [List.map_cons, head.type, ih]

theorem zip (names : List String) {sources : List (SourceValue F)} {targets : List (Value F)}
    (related : RepresentsArgs rom heap sources targets) :
    RepresentsEnv rom heap (names.zip sources) (names.zip targets) := by
  induction related generalizing names with
  | nil => simp
  | cons head _ ih =>
      cases names with
      | nil => exact .nil
      | cons name names => exact .cons ⟨rfl, head⟩ (ih names)

theorem get {sources : List (SourceValue F)} {targets : List (Value F)}
    (related : RepresentsArgs rom heap sources targets) {i : Nat} {target : Value F}
    (found : targets[i]? = some target) :
    ∃ source, sources[i]? = some source ∧ Represents rom heap source target := by
  induction related generalizing i with
  | nil => simp at found
  | cons head _ ih =>
      cases i with
      | zero => simp only [List.getElem?_cons_zero, Option.some.injEq] at found; subst target; exact ⟨_, rfl, head⟩
      | succ i => exact ih found

end RepresentsArgs

theorem RepresentsEnv.lookup {sources : Environment F Nat} {targets : Environment F}
    (related : RepresentsEnv rom heap sources targets) {name : String} {target : Value F}
    (found : targets.find? (·.1 == name) = some (name, target)) :
    ∃ source, sources.find? (·.1 == name) = some (name, source) ∧ Represents rom heap source target := by
  induction related with
  | nil => simp at found
  | @cons a b _ _ head tail ih =>
      simp only [List.find?_cons] at found ⊢
      rw [head.1]
      split at found
      · rename_i selected
        cases found
        exact ⟨a.2, by cases a; simp_all, head.2⟩
      · rename_i rejected
        simpa only [rejected, ↓reduceIte] using ih found

mutual
  theorem Pattern.represents [DecidableEq F] (pattern : Pattern F)
      {source : SourceValue F} {target : Value F} (related : Represents rom heap source target) :
      Option.Rel (RepresentsEnv rom heap) (pattern.bindings source) (pattern.bindings target) := by
    cases pattern with
    | wildcard => simpa only [Pattern.bindings] using Option.Rel.some (List.Forall₂.nil)
    | bind name =>
        simpa only [Pattern.bindings] using Option.Rel.some (List.Forall₂.cons ⟨rfl, related⟩ .nil)
    | literal literal =>
        cases related with
        | field => simp only [Pattern.bindings]; split
                   · exact .some .nil
                   · exact .none
        | tuple | ptr | construct => simp only [Pattern.bindings]; exact .none
    | tuple patterns =>
        cases related with
        | field | ptr | construct => simp only [Pattern.bindings]; exact .none
        | tuple items => simpa only [Pattern.bindings] using Pattern.representsList patterns items
    | construct name ctor patterns =>
        cases related with
        | field | ptr | tuple => simp only [Pattern.bindings]; exact .none
        | construct items =>
            simp only [Pattern.bindings]
            split
            · exact Pattern.representsList patterns items
            · exact .none
  termination_by sizeOf pattern

  theorem Pattern.representsList [DecidableEq F] (patterns : List (Pattern F))
      {sources : List (SourceValue F)} {targets : List (Value F)}
      (related : RepresentsArgs rom heap sources targets) :
      Option.Rel (RepresentsEnv rom heap) (Pattern.bindingsList patterns sources)
        (Pattern.bindingsList patterns targets) := by
    cases patterns with
    | nil => cases related <;> simp only [Pattern.bindingsList]; exact .some .nil; exact .none
    | cons pattern patterns =>
        cases related with
        | nil => simp only [Pattern.bindingsList]; exact .none
        | cons head tail =>
            have heads := pattern.represents head
            have tails := Pattern.representsList patterns tail
            simp only [Pattern.bindingsList]
            generalize hs : pattern.bindings _ = sourceHead at heads ⊢
            generalize ht : pattern.bindings _ = targetHead at heads ⊢
            generalize hss : Pattern.bindingsList patterns _ = sourceTail at tails ⊢
            generalize htt : Pattern.bindingsList patterns _ = targetTail at tails ⊢
            cases heads <;> cases tails
            all_goals first | exact .some (List.rel_append ‹_› ‹_›) | exact .none
  termination_by sizeOf patterns
end

theorem selectArm_represents [DecidableEq F] {source : SourceValue F} {target : Value F}
    (related : Represents rom heap source target) (arms : List (Pattern F × Expr F)) :
    Option.Rel (fun a b => RepresentsEnv rom heap a.1 b.1 ∧ a.2 = b.2)
      (selectArm source arms) (selectArm target arms) := by
  induction arms with
  | nil => exact .none
  | cons arm arms ih =>
      rcases arm with ⟨pattern, body⟩
      have matched := pattern.represents related
      simp only [selectArm]
      generalize hs : pattern.bindings source = sourceMatch at matched ⊢
      generalize ht : pattern.bindings target = targetMatch at matched ⊢
      cases matched with
      | none => exact ih
      | some bindings => exact .some ⟨bindings, rfl⟩

theorem Represents.project {source : SourceValue F} {target result : Value F} {index : Nat}
    (related : Represents rom heap source target) (projected : projectValue target index = .ok result) :
    ∃ value, projectValue source index = .ok value ∧ Represents rom heap value result := by
  cases related with
  | field | ptr | construct => cases projected
  | @tuple sources targets items =>
      cases found : targets[index]? with
      | none => simp [projectValue, found] at projected
      | some target =>
          simp [projectValue, found, pure, Except.pure] at projected
          subst result
          obtain ⟨value, source, relation⟩ := RepresentsArgs.get items found
          exact ⟨value, by simp [projectValue, source, pure, Except.pure], relation⟩

theorem Represents.neg [Field F] {source : SourceValue F} {target result : Value F}
    (related : Represents rom heap source target) (operation : evalNeg target = .ok result) :
    ∃ value, evalNeg source = .ok value ∧ Represents rom heap value result := by
  cases related with
  | field => cases operation; exact ⟨_, rfl, .field⟩
  | tuple | ptr | construct => cases operation

theorem Represents.assertEq [DecidableEq F]
    {left right : SourceValue F} {x y result : Value F}
    (first : Represents rom heap left x) (second : Represents rom heap right y)
    (operation : evalAssertEq message x y = .ok result) :
    ∃ value, evalAssertEq message left right = .ok value ∧ Represents rom heap value result := by
  obtain ⟨free, rfl, rfl⟩ := evalAssertEq_ok.mp operation
  have lhs := first.pointerFree_eq free
  have rhs := second.pointerFree_eq free
  refine ⟨.tuple [], evalAssertEq_ok.mpr ⟨?_, lhs.trans rhs.symm, rfl⟩, .tuple .nil⟩
  rw [lhs, Value.pointerFree_mapAddress]
  exact free

theorem Represents.binary [Field F] [DecidableEq F]
    {left right : SourceValue F} {x y result : Value F} {op : BinOp}
    (l : Represents rom heap left x) (r : Represents rom heap right y)
    (operation : evalBinOp op x y = .ok result) :
    ∃ value, evalBinOp op left right = .ok value ∧ Represents rom heap value result := by
  cases l with
  | tuple | ptr | construct => cases operation
  | field =>
      cases r with
      | tuple | ptr | construct => cases operation
      | field =>
          cases op with
          | add | sub | mul => cases operation; exact ⟨_, rfl, .field⟩
          | div =>
              simp only [evalBinOp] at operation
              split at operation
              · cases operation
              · rename_i nonzero
                cases operation
                exact ⟨_, by simp [evalBinOp, nonzero], .field⟩

theorem prepareCall_represents [DecidableEq F] {program : Program F} {name : String}
    {sources : List (SourceValue F)} {targets : List (Value F)}
    (related : RepresentsArgs rom heap sources targets) {locals : Environment F} {body : Expr F}
    (prepared : prepareCall program name targets = .ok (locals, body)) :
    ∃ sourceLocals, prepareCall program name sources = .ok (sourceLocals, body) ∧
      RepresentsEnv rom heap sourceLocals locals := by
  rcases prepareCall_spec prepared with function | table
  · obtain ⟨fn, found, types, formed, rfl, rfl⟩ := function
    refine ⟨_, prepareCall_of_types found (types.trans related.types.symm) ?_, related.zip _⟩
    clear types prepared found
    induction related with
    | nil => simp
    | cons head tail ih =>
        intro source member
        rcases List.mem_cons.mp member with rfl | member
        · rw [head.wellFormed program.enums]
          exact formed _ (by simp)
        · exact ih (fun v h => formed v (by simp [h])) source member
  · obtain ⟨constant, absent, looked, rfl, rfl⟩ := table
    obtain ⟨_, key, _, _, _, extracted, _, _⟩ := lookupMap_spec looked
    have free : (Value.tuple targets).pointerFree = true := by
      rw [← Value.toConstant_spec extracted]
      exact Constant.toValue_pointerFree key
    have same := (Represents.tuple related).pointerFree_eq free
    have same : sources = targets.map (Value.mapAddress (fun _ => 0)) := by
      simpa only [Value.mapAddress, Value.tuple.injEq] using same
    refine ⟨[], prepareCall_map absent ?_, .nil⟩
    rw [same, lookupMap_mapAddress]
    exact looked

end Aiur
