import Aiur.Generic.LoweringTypes
import Aiur.Generic.OrPatternFacts
import Aiur.Generic.PatternTreeFacts
import Aiur.Generic.PatternTreeSoundness
import Aiur.Memory.Typing

namespace Aiur.Generic.PatternLowering
open SourceSemantics

theorem load_good {decls : Declarations} {heap : Heap F} {target : Aiur.Ty}
    (good : heap.Good decls) (loaded : loadValue heap (.ptr target address) = .ok value) :
    value.type = target ∧ value.Good decls := by
  cases found : heap[address]? with
  | none => simp [loadValue, found] at loaded
  | some stored =>
      by_cases typed : stored.type = target
      · simp [loadValue, found, typed, bind, Except.bind, pure, Except.pure] at loaded
        subst value
        exact ⟨typed, good _ (List.mem_of_getElem? found)⟩
      · simp [loadValue, found, typed] at loaded

theorem typeList_map (run : B → Aiur.Ty → Option LocalTypes) (f : A → B)
    (xs : List A) (types : List Aiur.Ty) :
    typeListWith run (xs.map f) types = typeListWith (fun x t => run (f x) t) xs types := by
  induction xs generalizing types with
  | nil => cases types <;> rfl
  | cons x xs ih => cases types <;> simp only [List.map_cons, typeListWith, ih]

theorem typeList_attach (run : A → Aiur.Ty → Option LocalTypes) (xs : List A) (types : List Aiur.Ty) :
    typeListWith (fun x t => run x.val t) xs.attach types = typeListWith run xs types := by
  rw [← typeList_map run Subtype.val, List.attach_map_subtype_val]

private theorem sequence_typed [DecidableEq F]
    {run : A → SourceValue F → Except EvalError (Option (Environment F Nat))}
    {check : A → Aiur.Ty → Option LocalTypes} {xs : List A} {values : List (SourceValue F)}
    (each : ∀ x ∈ xs, ∀ value bindings types, value.Good decls →
      run x value = .ok (some bindings) → check x value.type = some types →
      environmentTypes bindings = types ∧ bindings.Good decls)
    (good : ∀ value ∈ values, value.Good decls)
    (matched : matchListWith run xs values = .ok (some bindings))
    (typed : typeListWith check xs (values.map Value.type) = some types) :
    environmentTypes bindings = types ∧ bindings.Good decls := by
  induction xs generalizing values bindings types with
  | nil =>
      cases values <;> simp only [matchListWith, pure, Except.pure, Except.ok.injEq] at matched
      · cases matched
        cases typed
        exact ⟨rfl, by simp [Environment.Good]⟩
      · cases matched
  | cons x xs ih =>
      cases values with
      | nil => simp [matchListWith, pure, Except.pure] at matched
      | cons value values =>
          cases head : run x value with
          | error e => simp [matchListWith, head, bind, Except.bind] at matched
          | ok result => cases result with
            | none => simp [matchListWith, head, bind, Except.bind, pure, Except.pure] at matched
            | some first =>
                cases tail : matchListWith run xs values with
                | error e => simp [matchListWith, head, tail, bind, Except.bind] at matched
                | ok result => cases result with
                  | none => simp [matchListWith, head, tail, bind, Except.bind, pure, Except.pure] at matched
                  | some rest =>
                      have same : first ++ rest = bindings := by
                        simpa [matchListWith, head, tail, bind, Except.bind, pure, Except.pure] using matched
                      subst bindings
                      cases headType : check x value.type with
                      | none => simp [typeListWith, headType] at typed
                      | some firstType =>
                          cases tailType : typeListWith check xs (values.map Value.type) with
                          | none => simp [typeListWith, headType, tailType] at typed
                          | some restType =>
                              have same : firstType ++ restType = types := by
                                simpa [typeListWith, headType, tailType] using typed
                              subst types
                              obtain ⟨hf, gf⟩ := each x (by simp) value first firstType (good _ (by simp)) head headType
                              obtain ⟨hr, gr⟩ := ih (fun y hy => each y (by simp [hy]))
                                (fun v hv => good v (by simp [hv])) tail tailType
                              exact ⟨by simp only [environmentTypes_append, hf, hr], Environment.good_append.mpr ⟨gf, gr⟩⟩

theorem reorder_typed {names positions} {bindings ordered : Environment F Nat}
    (same : environmentTypes bindings = types) (good : bindings.Good decls)
    (reordered : reorderBindings names positions bindings = some ordered)
    (typed : reorderBindings names positions types = some orderedTypes) :
    environmentTypes ordered = orderedTypes ∧ ordered.Good decls := by
  have mapped := reorderBindings_mapValues (Value.type (α := F) (Address := Nat)) names positions bindings
  change reorderBindings names positions (environmentTypes bindings) =
    (reorderBindings names positions bindings).map environmentTypes at mapped
  rw [same, typed, reordered, Option.map_some] at mapped
  exact ⟨(Option.some.inj mapped).symm, reorderBindings_good good reordered⟩

/-- A successful native match produces exactly its statically inferred user
binding types. Read-only loads preserve well-formed values from the heap. -/
theorem PlanTree.match_typed [DecidableEq F] (tree : PlanTree F)
    (heapGood : heap.Good decls) (valueGood : value.Good decls)
    (matched : matchPatternWith constant depth [] heap tree.erase value = .ok (some bindings))
    (typed : tree.bindTypes decls value.type = some types) :
    environmentTypes bindings = types ∧ bindings.Good decls := by
  have sub (child : PlanTree F) (smaller : sizeOf child < sizeOf tree)
      (v : SourceValue F) (bs : Environment F Nat) (ts : LocalTypes)
      (vg : v.Good decls)
      (hm : matchPatternWith constant depth [] heap child.erase v = .ok (some bs))
      (ht : child.bindTypes decls v.type = some ts) :
      environmentTypes bs = ts ∧ bs.Good decls :=
    child.match_typed heapGood vg hm ht
  have children (parts : List (String × PlanTree F))
      (smaller : ∀ part ∈ parts, sizeOf part.2 < sizeOf tree)
      (values : List (SourceValue F)) (good : ∀ v ∈ values, v.Good decls)
      (matched : matchListWith (fun part v => matchPatternWith constant depth [] heap part.2.erase v)
        parts values = .ok (some bindings))
      (typed : typeListWith (fun part type => part.2.bindTypes decls type) parts (values.map Value.type) = some types) :
      environmentTypes bindings = types ∧ bindings.Good decls :=
    sequence_typed (fun part member v bs ts vg hm ht => sub part.2 (smaller part member) v bs ts vg hm ht)
      good matched typed
  cases tree with
  | wildcard =>
      simp only [PlanTree.erase, matchPatternWith, pure, Except.pure, Except.ok.injEq, Option.some.injEq] at matched
      subst bindings
      simp only [PlanTree.bindTypes, Option.some.injEq] at typed
      subst types
      exact ⟨rfl, by simp [Environment.Good]⟩
  | bind name =>
      simp only [PlanTree.erase, matchPatternWith, pure, Except.pure, Except.ok.injEq, Option.some.injEq] at matched
      subst bindings
      simp only [PlanTree.bindTypes, Option.some.injEq] at typed
      subst types
      exact ⟨rfl, by simpa [Environment.Good] using valueGood⟩
  | literal x =>
      cases value <;> simp only [Value.type, PlanTree.bindTypes] at typed
      all_goals first | contradiction | skip
      cases typed
      simp only [PlanTree.erase, matchPatternWith, Aiur.Pattern.bindings, pure, Except.pure] at matched
      split at matched
      · cases matched; exact ⟨rfl, by simp [Environment.Good]⟩
      · cases matched
  | choice stem left right layout =>
      rw [PlanTree.bindTypes] at typed
      obtain ⟨lts, leftTyped, typed⟩ := Option.bind_eq_some_iff.mp typed
      obtain ⟨rts, rightTyped, typed⟩ := Option.bind_eq_some_iff.mp typed
      obtain ⟨lhs, lhsTyped, typed⟩ := Option.bind_eq_some_iff.mp typed
      obtain ⟨rhs, rhsTyped, typed⟩ := Option.bind_eq_some_iff.mp typed
      split at typed
      · rename_i equal
        have equal : lhs = rhs := by simpa using equal
        have result : lhs = types := Option.some.inj typed
        subst types
        simp only [PlanTree.erase] at matched
        rcases match_or_some_iff.mp matched with ⟨bs, matched, reordered⟩ | ⟨_, bs, matched, reordered⟩
        · obtain ⟨same, good⟩ := sub left (by simp_wf; omega) value bs lts valueGood matched leftTyped
          exact reorder_typed same good reordered lhsTyped
        · obtain ⟨same, good⟩ := sub right (by simp_wf; omega) value bs rts valueGood matched rightTyped
          simpa only [equal] using reorder_typed same good reordered rhsTyped
      · contradiction
  | load name child =>
      cases value <;> simp only [Value.type, PlanTree.bindTypes] at typed
      all_goals first | contradiction | skip
      rename_i target address
      simp only [PlanTree.erase, matchPatternWith, except_bind_ok] at matched
      obtain ⟨stored, loaded, matched⟩ := matched
      obtain ⟨shape, good⟩ := load_good heapGood loaded
      exact sub child (by simp_wf <;> omega) stored _ _ good matched (by rw [shape]; exact typed)
  | tuple parts =>
      cases value <;> simp only [Value.type, PlanTree.bindTypes] at typed
      all_goals first | contradiction | skip
      rename_i values
      simp only [PlanTree.erase, matchPatternWith, List.length_map] at matched
      split at matched
      · cases matched
      · simp only [Preparation.matchList_attach, matchList_map, pure_bind] at matched
        rw [typeList_attach (fun (part : String × PlanTree F) type => part.2.bindTypes decls type)] at typed
        exact children parts (by intros; simp_wf; have := List.sizeOf_lt_of_mem ‹_ ∈ _›; cases ‹String × PlanTree F›; simp_all only [Prod.mk.sizeOf_spec]; omega)
          values ((Value.good_tuple _ _).mp valueGood) matched typed
  | construct name ctor parts =>
      cases value <;> simp only [Value.type, PlanTree.bindTypes] at typed
      all_goals first | contradiction | skip
      rename_i actual constructor values
      simp only [PlanTree.erase, matchPatternWith, nominal_name, List.length_map] at matched
      split at matched
      · cases matched
      · rename_i names
        simp only [Bool.or_eq_true, bne_iff_ne, not_or, not_not] at names
        obtain ⟨⟨rfl, rfl⟩, _⟩ := names
        obtain ⟨definition, found, shape, fieldsGood⟩ := (Value.wellFormed_construct _ _ _ _).mp valueGood.1
        simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, found, pure_bind] at typed
        change typeListWith (fun child type => child.val.2.bindTypes decls type)
          parts.attach definition.fields = some types at typed
        rw [typeList_attach (fun (part : String × PlanTree F) type => part.2.bindTypes decls type), ← shape] at typed
        simp only [Preparation.matchList_attach, matchList_map, pure_bind] at matched
        exact children parts (by intros; simp_wf; have := List.sizeOf_lt_of_mem ‹_ ∈ _›; cases ‹String × PlanTree F›; simp_all only [Prod.mk.sizeOf_spec]; omega)
          values (fun v hv => ⟨fieldsGood v hv,
            (Value.pointerNames_construct _ _ _ _).mp valueGood.2 v hv⟩) matched typed
termination_by sizeOf tree
decreasing_by exact smaller

end Aiur.Generic.PatternLowering

namespace Aiur.Generic

theorem Pattern.lowerBindingTypes_sound [DecidableEq F] {pat : Pattern F}
    (heapGood : heap.Good decls) (valueGood : value.Good decls)
    (matched : SourceSemantics.matchPatternWith constant depth types heap pat value = .ok (some bindings))
    (typed : pat.lowerBindingTypes decls types value.type = some bindingTypes) :
    environmentTypes bindings = bindingTypes ∧ bindings.Good decls := by
  unfold Pattern.lowerBindingTypes at typed
  split at typed
  · rename_i resolved
    rw [PatternLowering.planTree_match pat resolved types "" 0] at matched
    exact PatternLowering.PlanTree.match_typed _ heapGood valueGood matched typed
  · cases typed

end Aiur.Generic
