import Aiur.Generic.PatternTreeSoundness

namespace Aiur.Generic.PatternLowering
open SourceSemantics

/-- Every non-error native pattern result has a matching execution of its
read/test plan. Inactive later tests and loads are never prerequisites. -/
theorem PlanTree.attempt_complete [DecidableEq F] (tree : PlanTree F) (input : String)
    (safe : (input :: tree.temps).Nodup)
    (constant : String → Ty → Except EvalError (Pattern F)) (depth : Nat)
    (heap : Heap F) (value : SourceValue F) (locals : Environment F Nat)
    (found : locals.find? (·.1 == input) = some (input, value))
    {outcome : Option (Environment F Nat)}
    (matched : matchPatternWith constant depth [] heap tree.erase value = .ok outcome) :
    ∃ final, Attempt heap (tree.toPlan input).steps locals outcome.isSome final := by
  have sub (child : PlanTree F) (smaller : sizeOf child < sizeOf tree) (name : String)
      (safe : (name :: child.temps).Nodup) (value : SourceValue F) (locals : Environment F Nat)
      (found : locals.find? (·.1 == name) = some (name, value)) {outcome}
      (matched : matchPatternWith constant depth [] heap child.erase value = .ok outcome) :
      ∃ final, Attempt heap (child.toPlan name).steps locals outcome.isSome final :=
    PlanTree.attempt_complete child name safe constant depth heap value locals found matched
  have children (parts : List (String × PlanTree F))
      (smaller : ∀ p ∈ parts, sizeOf p.2 < sizeOf tree)
      (safe : (parts.map Prod.fst ++ parts.flatMap (fun p => p.2.temps)).Nodup)
      (values : List (SourceValue F)) (lengths : parts.length = values.length)
      (locals : Environment F Nat) {outcome}
      (matched : matchListWith (fun p v => matchPatternWith constant depth [] heap p.2.erase v) parts values = .ok outcome) :
      ∃ final, Attempt heap (parts.flatMap (fun p => (p.2.toPlan p.1).steps))
        (((parts.map Prod.fst).zip values) ++ locals) outcome.isSome final := by
    apply sequence_complete _ parts _ ((grouped_names_perm parts Prod.fst (fun p => p.2.temps)).nodup_iff.mp safe) _ matched
    · intro part hp locals value outcome safe found matched
      exact sub part.2 (smaller part hp) part.1 safe value locals found matched
    · apply (List.forall₂_map_left_iff
        (R := fun name value => (((parts.map Prod.fst).zip values) ++ locals).find? (·.1 == name) = some (name, value))
        (f := Prod.fst)).mp
      exact lookup_zip _ values locals (List.nodup_append.mp safe).1 (by simpa using lengths)
  cases tree with
  | literal x =>
      simp only [PlanTree.erase, matchPatternWith, pure, Except.pure, Except.ok.injEq] at matched
      subst outcome
      simp only [PlanTree.toPlan]
      cases bindings : (Aiur.Pattern.literal x).bindings value with
      | none => exact ⟨locals, .testMiss found bindings⟩
      | some bs => exact ⟨bs ++ locals, .testHit found bindings .done⟩
  | wildcard | bind =>
      simp only [PlanTree.erase, matchPatternWith, pure, Except.pure, Except.ok.injEq] at matched
      subst outcome
      simp only [PlanTree.toPlan]
      exact ⟨locals, .done⟩
  | choice stem left right layout =>
      obtain ⟨safeLeft, safeRight, unique⟩ := PlanTree.safe_choice safe
      simp only [PlanTree.erase] at matched
      simp only [PlanTree.toPlan]
      cases outcome with
      | none =>
          obtain ⟨hmLeft, hmRight⟩ := match_or_none_iff.mp matched
          obtain ⟨middle, missed⟩ := sub left (by simp_wf; omega) input safeLeft value locals found hmLeft
          have nextFound := missed.unchanged (by rw [PlanTree.written]; exact (List.nodup_cons.mp safeLeft).1)
          rw [found] at nextFound
          obtain ⟨final, rejected⟩ := sub right (by simp_wf; omega) input safeRight value middle nextFound hmRight
          exact ⟨final, .choiceMiss missed rejected⟩
      | some ordered =>
          rcases match_or_some_iff.mp matched with ⟨bs, hm, reordered⟩ | ⟨failed, bs, hm, reordered⟩
          · obtain ⟨middle, selected⟩ := sub left (by simp_wf; omega) input safeLeft value locals found hm
            obtain ⟨actual, same, resolved⟩ := left.attempt_sound input safeLeft constant depth heap value locals found selected
            have same := Except.ok.inj (hm.symm.trans same)
            cases Option.some.inj same
            obtain ⟨aliases, installed, aligned, copied⟩ := choice_copy_exists (stem := stem) resolved reordered
            refine ⟨installed ++ middle, .choiceLeft selected ?_ copied .done⟩
            simpa only [choiceBindings, List.length_map] using aligned
          · obtain ⟨rejected, missed⟩ := sub left (by simp_wf; omega) input safeLeft value locals found failed
            have nextFound := missed.unchanged (by rw [PlanTree.written]; exact (List.nodup_cons.mp safeLeft).1)
            rw [found] at nextFound
            obtain ⟨middle, selected⟩ := sub right (by simp_wf; omega) input safeRight value rejected nextFound hm
            obtain ⟨actual, same, resolved⟩ := right.attempt_sound input safeRight constant depth heap value rejected nextFound selected
            have same := Except.ok.inj (hm.symm.trans same)
            cases Option.some.inj same
            obtain ⟨aliases, installed, aligned, copied⟩ := choice_copy_exists (stem := stem) resolved reordered
            exact ⟨installed ++ middle, .choiceRight missed selected aligned copied .done⟩
  | load name child =>
      simp only [PlanTree.erase, matchPatternWith, except_bind_ok] at matched
      obtain ⟨contents, loaded, matched⟩ := matched
      obtain ⟨final, rest⟩ := sub child (by simp_wf <;> omega) name (PlanTree.safe_load safe)
        contents ((name, contents) :: locals) (by simp) matched
      simp only [PlanTree.toPlan]
      exact ⟨final, .load found loaded rest⟩
  | tuple parts =>
      have safeParts : (parts.map Prod.fst ++ parts.flatMap (fun p => p.2.temps)).Nodup := by
        simpa only [PlanTree.temps] using (List.nodup_cons.mp safe).2
      have pats : parts.map (fun p => (Aiur.Pattern.bind p.1 : Aiur.Pattern F)) =
          (parts.map Prod.fst).map Aiur.Pattern.bind := by simp only [List.map_map, Function.comp_def]
      simp only [PlanTree.toPlan, List.map_map, List.flatMap_map, Function.comp_def]
      rw [pats]
      cases value with
      | tuple values =>
          simp only [PlanTree.erase, matchPatternWith, Preparation.matchList_attach, List.length_map,
            matchList_map] at matched
          by_cases lengths : parts.length = values.length
          · have matched : matchListWith (fun p v => matchPatternWith constant depth [] heap p.2.erase v) parts values = .ok outcome := by
              convert matched using 1 <;> simp only [lengths, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, bind, Except.bind,
                pure, Except.pure] <;> rfl
            obtain ⟨final, rest⟩ := children parts (by intros; simp_wf; have := List.sizeOf_lt_of_mem ‹_ ∈ _›; cases ‹String × PlanTree F›; simp_all only [Prod.mk.sizeOf_spec]; omega)
              safeParts values lengths locals matched
            exact ⟨final, .testHit found (by simpa [Aiur.Pattern.bindings] using bindingsList_binders (parts.map Prod.fst) values (by simpa using lengths)) rest⟩
          · have same : outcome = none := by
              simpa [lengths, bind, Except.bind, pure, Except.pure] using matched.symm
            subst outcome
            exact ⟨locals, .testMiss found (by simp only [Aiur.Pattern.bindings, and_self, ↓reduceIte, bindingsList_binders_eq, List.length_map, lengths])⟩
      | _ =>
          simp only [PlanTree.erase, matchPatternWith, pure, Except.pure, Except.ok.injEq] at matched
          subst outcome
          exact ⟨locals, .testMiss found (by simp only [Aiur.Pattern.bindings])⟩
  | construct name ctor parts =>
      have safeParts : (parts.map Prod.fst ++ parts.flatMap (fun p => p.2.temps)).Nodup := by
        simpa only [PlanTree.temps] using (List.nodup_cons.mp safe).2
      have pats : parts.map (fun p => (Aiur.Pattern.bind p.1 : Aiur.Pattern F)) =
          (parts.map Prod.fst).map Aiur.Pattern.bind := by simp only [List.map_map, Function.comp_def]
      simp only [PlanTree.toPlan, List.map_map, List.flatMap_map, Function.comp_def]
      rw [pats]
      cases value with
      | construct other ctor' values =>
          simp only [PlanTree.erase, matchPatternWith, nominal_name, Preparation.matchList_attach,
            List.length_map, matchList_map] at matched
          by_cases names : name = other ∧ ctor = ctor'
          · rcases names with ⟨rfl, rfl⟩
            by_cases lengths : parts.length = values.length
            · have matched : matchListWith (fun p v => matchPatternWith constant depth [] heap p.2.erase v) parts values = .ok outcome := by
                convert matched using 1 <;> simp only [lengths, bne_self_eq_false, Bool.or_self, Bool.false_eq_true, ↓reduceIte,
                  bind, Except.bind, pure, Except.pure] <;> rfl
              obtain ⟨final, rest⟩ := children parts (by intros; simp_wf; have := List.sizeOf_lt_of_mem ‹_ ∈ _›; cases ‹String × PlanTree F›; simp_all only [Prod.mk.sizeOf_spec]; omega)
                safeParts values lengths locals matched
              exact ⟨final, .testHit found (by simpa [Aiur.Pattern.bindings] using bindingsList_binders (parts.map Prod.fst) values (by simpa using lengths)) rest⟩
            · have same : outcome = none := by
                simpa [lengths, bind, Except.bind, pure, Except.pure] using matched.symm
              subst outcome
              exact ⟨locals, .testMiss found (by simp only [Aiur.Pattern.bindings, and_self, ↓reduceIte, bindingsList_binders_eq, List.length_map, lengths])⟩
          · have different : other ≠ name ∨ ctor' ≠ ctor := by
              by_cases h : other = name
              · right; intro hc; apply names; exact ⟨h.symm, hc.symm⟩
              · exact Or.inl h
            have same : outcome = none := by
              rcases different with h | h <;>
                simpa [h, bind, Except.bind, pure, Except.pure] using matched.symm
            subst outcome
            exact ⟨locals, .testMiss found (by simp [Aiur.Pattern.bindings, names])⟩
      | _ =>
          simp only [PlanTree.erase, matchPatternWith, pure, Except.pure, Except.ok.injEq] at matched
          subst outcome
          exact ⟨locals, .testMiss found (by simp only [Aiur.Pattern.bindings])⟩
termination_by sizeOf tree
decreasing_by exact smaller

end Aiur.Generic.PatternLowering
