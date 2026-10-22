import Aiur.Generic.ControlEnvironment
import Aiur.Generic.BindingOrderFacts
import Mathlib.Data.List.Nodup

namespace Aiur.Generic.ControlLower
set_option linter.unusedSimpArgs false
open SourceSemantics Preparation

def renameBindings (env : Renaming) (bs : Environment F Nat) : Environment F Nat :=
  bs.map (fun (name, value) => (rename env name, value))

@[simp] theorem renameBindings_nil : renameBindings env ([] : Environment F Nat) = [] := rfl

@[simp] theorem renameBindings_append (left right : Environment F Nat) :
    renameBindings env (left ++ right) = renameBindings env left ++ renameBindings env right :=
  List.map_append

theorem matchList_rename [DecidableEq F]
    {left : A → SourceValue F → Except EvalError (Option (Environment F Nat))}
    {right : B → SourceValue F → Except EvalError (Option (Environment F Nat))}
    {xs : List A} {ys : List B}
    (related : List.Forall₂ (fun x y => ∀ v,
      right y v = (left x v).map (Option.map (renameBindings env))) xs ys)
    (values : List (SourceValue F)) :
    matchListWith right ys values =
      (matchListWith left xs values).map (Option.map (renameBindings env)) := by
  induction related generalizing values with
  | nil => cases values <;> rfl
  | @cons x y xs ys rel _ ih =>
      cases values with
      | nil => rfl
      | cons value values =>
          simp only [matchListWith, rel, ih]
          cases left x value with
          | error e => rfl
          | ok bs => cases bs with
            | none => rfl
            | some bs =>
                cases matchListWith left xs values with
                | error e => rfl
                | ok rest => cases rest <;>
                    simp [Except.map, Option.map, bind, Except.bind, pure, Except.pure]

/-- Renaming a pattern changes only the keys of its successful bindings.
It preserves failure, short-circuiting, and invalid-pointer errors exactly. -/
theorem matchPattern_rename [DecidableEq F]
    (pat : Pattern F) (plain : Consts.dependencies pat = [])
    (env : Renaming) (constant depth types heap value) :
    matchPatternWith constant depth types heap (renamePattern env pat) value =
      (matchPatternWith constant depth types heap pat value).map (Option.map (renameBindings env)) := by
  have sub (p : Pattern F) (smaller : sizeOf p < sizeOf pat)
      (hp : Consts.dependencies p = []) (v : SourceValue F) :
      matchPatternWith constant depth types heap (renamePattern env p) v =
        (matchPatternWith constant depth types heap p v).map (Option.map (renameBindings env)) :=
    matchPattern_rename p hp env constant depth types heap v
  have children (ps : List (Pattern F)) (small : ∀ p ∈ ps, sizeOf p < sizeOf pat)
      (plain : ∀ p ∈ ps, Consts.dependencies p = []) (vs : List (SourceValue F)) :
      matchListWith (fun p v => matchPatternWith constant depth types heap p.val v)
        (ps.map (renamePattern env)).attach vs =
      (matchListWith (fun p v => matchPatternWith constant depth types heap p.val v) ps.attach vs).map
        (Option.map (renameBindings env)) := by
    rw [matchList_attach, matchList_attach]
    apply matchList_rename
    apply List.forall₂_map_right_iff.mpr
    exact List.forall₂_same.mpr (fun p hp => sub p (small p hp) (plain p hp))
  cases pat with
  | literal x =>
      cases value <;> simp [renamePattern, matchPatternWith, Aiur.Pattern.bindings, renameBindings, pure, Except.pure, Except.map]
  | wildcard | bind => simp [renamePattern, matchPatternWith, renameBindings, pure, Except.pure, Except.map]
  | global => simp [Consts.dependencies] at plain
  | orElse left right layout =>
      have plain := plain
      simp only [Consts.dependencies, List.append_eq_nil_iff] at plain
      simp only [renamePattern, matchPatternWith,
        sub left (by simp_wf; omega) plain.1, sub right (by simp_wf; omega) plain.2]
      cases hl : matchPatternWith constant depth types heap left value with
      | error e => rfl
      | ok selected =>
          cases selected with
          | some bs =>
              simp only [Except.map, Option.map, bind, Except.bind, pure, Except.pure,
                List.length_map, renameBindings, reorderBindings_rename]
              cases reorderBindings layout.names (List.range layout.names.length) bs <;> rfl
          | none =>
              cases hr : matchPatternWith constant depth types heap right value with
              | error e => rfl
              | ok selected =>
                  cases selected with
                  | none => rfl
                  | some bs =>
                      simp only [Except.map, Option.map, bind, Except.bind, pure, Except.pure,
                        List.length_map, renameBindings, reorderBindings_rename]
                      cases reorderBindings layout.names layout.rightOrder bs <;> rfl
  | load p =>
      simp only [renamePattern, matchPatternWith]
      cases loaded : loadValue heap value with
      | error e => rfl
      | ok v => exact sub p (by simp_wf <;> omega) (by simpa [Consts.dependencies] using plain) v
  | record head ps =>
      have noGlobals : ∀ p ∈ ps, Consts.dependencies p = [] := by
        simpa [Consts.dependencies, List.flatMap_eq_nil_iff] using plain
      have rel : List.Forall₂ (fun p q => ∀ v,
          matchPatternWith constant depth types heap q v =
          (matchPatternWith constant depth types heap p v).map (Option.map (renameBindings env)))
          ps (ps.map (renamePattern env)) := by
        apply List.forall₂_map_right_iff.mpr
        apply List.forall₂_same.mpr
        intro p hp
        exact sub p (by simp_wf; have := List.sizeOf_lt_of_mem hp; omega) (noGlobals p hp)
      have ordered := head.order_rel rel (a := Pattern.wildcard) (b := Pattern.wildcard)
        (by intro v; simp [matchPatternWith, renameBindings, pure, Except.pure, Except.map])
      cases value <;> simp only [renamePattern, match_record, ordered.length_eq]
      all_goals first | rfl | skip
      split
      · rfl
      · split
        · rfl
        · exact matchList_rename ordered _
  | tuple ps | array ps | construct _ _ ps | constructAs _ _ _ ps =>
      have noGlobals : ∀ p ∈ ps, Consts.dependencies p = [] := by
        simpa [Consts.dependencies, List.flatMap_eq_nil_iff] using plain
      have ih := children ps (by intros; simp_wf; have := List.sizeOf_lt_of_mem ‹_ ∈ _›; omega) noGlobals
      cases value <;> simp only [renamePattern, matchPatternWith, List.length_map]
      all_goals first | rfl | skip
      all_goals split
      all_goals first | rfl | apply ih
  | «repeat» p n =>
      have hp : Consts.dependencies p = [] := by simpa [Consts.dependencies] using plain
      cases value <;> simp only [renamePattern, matchPatternWith]
      all_goals first | rfl | skip
      split
      · rfl
      · apply matchList_rename
        exact List.forall₂_same.mpr (fun _ _ v => sub p (by simp_wf <;> omega) hp v)
termination_by sizeOf pat
decreasing_by all_goals exact smaller

theorem matchList_names
    {run : A → SourceValue F → Except EvalError (Option (Environment F Nat))}
    {xs : List A} {vs : List (SourceValue F)} {bs : Environment F Nat}
    (getNames : A → List String)
    (correct : ∀ x ∈ xs, ∀ v result, run x v = .ok (some result) → result.map Prod.fst = getNames x)
    (matched : matchListWith run xs vs = .ok (some bs)) :
    bs.map Prod.fst = xs.flatMap getNames := by
  induction xs generalizing vs bs with
  | nil => cases vs <;> simp_all [matchListWith, pure, Except.pure]
  | cons x xs ih =>
      cases vs with
      | nil => simp [matchListWith] at matched
      | cons v vs =>
          cases hfirst : run x v with
          | error e => simp [matchListWith, hfirst, bind, Except.bind] at matched
          | ok first => cases first with
            | none => simp [matchListWith, hfirst, bind, Except.bind] at matched
            | some bindings =>
                cases hrest : matchListWith run xs vs with
                | error e => simp [matchListWith, hfirst, hrest, bind, Except.bind] at matched
                | ok rest => cases rest with
                  | none => simp [matchListWith, hfirst, hrest, bind, Except.bind] at matched
                  | some more =>
                      have same : bindings ++ more = bs := by
                        simpa [matchListWith, hfirst, hrest, bind, Except.bind, pure, Except.pure] using matched
                      subst bs
                      simp only [List.map_append, List.flatMap_cons]
                      rw [correct x (by simp) _ _ hfirst, ih (fun y hy => correct y (by simp [hy])) hrest]

theorem matchPattern_names [DecidableEq F]
    (pat : Pattern F) (plain : Consts.dependencies pat = [])
    {constant depth types heap value bs}
    (matched : matchPatternWith constant depth types heap pat value = .ok (some bs)) :
    bs.map Prod.fst = pat.bindingNames := by
  have sub (p : Pattern F) (smaller : sizeOf p < sizeOf pat)
      (hp : Consts.dependencies p = []) {v : SourceValue F} {bindings}
      (h : matchPatternWith constant depth types heap p v = .ok (some bindings)) :
      bindings.map Prod.fst = p.bindingNames := matchPattern_names p hp h
  cases pat with
  | literal x =>
      cases value <;> simp [matchPatternWith, Aiur.Pattern.bindings] at matched
      simp_all [Pattern.bindingNames]
  | wildcard | bind =>
      simp only [matchPatternWith, except_pure_ok, Option.some.injEq] at matched
      subst bs
      simp [Pattern.bindingNames]
  | global => simp [Consts.dependencies] at plain
  | orElse left right layout =>
      simp only [Pattern.bindingNames]
      cases hl : matchPatternWith constant depth types heap left value with
      | error e => simp [matchPatternWith, hl, bind, Except.bind] at matched
      | ok selected =>
          cases selected with
          | some first =>
              simp only [matchPatternWith, hl, bind, Except.bind, pure, Except.pure] at matched
              cases ordered : reorderBindings layout.names (List.range layout.names.length) first with
              | none => simp [ordered] at matched
              | some result =>
                  simp only [ordered, Except.ok.injEq, Option.some.injEq] at matched
                  subst bs
                  exact reorderBindings_names ordered
          | none =>
              cases hr : matchPatternWith constant depth types heap right value with
              | error e => simp [matchPatternWith, hl, hr, bind, Except.bind, pure, Except.pure, Except.map] at matched
              | ok selected =>
                  cases selected with
                  | none => simp [matchPatternWith, hl, hr, bind, Except.bind, pure, Except.pure, Except.map] at matched
                  | some second =>
                      simp only [matchPatternWith, hl, hr, bind, Except.bind, pure, Except.pure, Except.map] at matched
                      cases ordered : reorderBindings layout.names layout.rightOrder second with
                      | none => simp [ordered] at matched
                      | some result =>
                          simp only [ordered, Except.ok.injEq, Option.some.injEq] at matched
                          subst bs
                          exact reorderBindings_names ordered
  | load p =>
      simp only [matchPatternWith, except_bind_ok] at matched
      obtain ⟨v, _, matched⟩ := matched
      simpa only [Pattern.bindingNames] using sub p (by simp_wf <;> omega) (by simpa [Consts.dependencies] using plain) matched
  | record head ps =>
      have noGlobals : ∀ p ∈ ps, Consts.dependencies p = [] := by
        simpa [Consts.dependencies, List.flatMap_eq_nil_iff] using plain
      cases value <;> simp only [match_record] at matched
      all_goals try simp only [Except.ok.injEq, reduceCtorEq] at matched
      split at matched
      · simp at matched
      · split at matched
        · simp at matched
        · rw [record_bindingNames]
          apply matchList_names Pattern.bindingNames _ matched
          refine head.order_mem (P := fun x => ∀ v result, matchPatternWith constant depth types heap x v = .ok (some result) → result.map Prod.fst = x.bindingNames) ps Pattern.wildcard ?_ ?_
          · intro p hp v bindings h
            exact sub p (by simp_wf; have := List.sizeOf_lt_of_mem hp; omega) (noGlobals p hp) h
          · intro v bindings h
            simp only [matchPatternWith, except_pure_ok, Option.some.injEq] at h
            subst bindings
            simp [Pattern.bindingNames]
  | tuple ps | array ps | construct _ _ ps | constructAs _ _ _ ps =>
      have noGlobals : ∀ p ∈ ps, Consts.dependencies p = [] := by
        simpa [Consts.dependencies, List.flatMap_eq_nil_iff] using plain
      cases value <;> simp only [matchPatternWith, pure, Except.pure] at matched
      all_goals try simp only [Except.ok.injEq, reduceCtorEq] at matched
      all_goals split at matched
      all_goals try simp only [Except.ok.injEq, reduceCtorEq] at matched
      all_goals
        rw [matchList_attach] at matched
        simp only [Pattern.bindingNames]
        apply matchList_names Pattern.bindingNames _ matched
        intro p hp v bindings h
        exact sub p (by simp_wf; have := List.sizeOf_lt_of_mem hp; omega) (noGlobals p hp) h
  | «repeat» p n =>
      cases value <;> simp only [matchPatternWith, pure, Except.pure] at matched
      all_goals try simp only [Except.ok.injEq, reduceCtorEq] at matched
      split at matched
      · simp at matched
      · have h := matchList_names (fun (_ : Unit) => p.bindingNames)
          (fun _ _ _ _ h => sub p (by simp_wf <;> omega) (by simpa [Consts.dependencies] using plain) h) matched
        simpa [Pattern.bindingNames, List.flatMap_replicate] using h
termination_by sizeOf pat
decreasing_by all_goals exact smaller

end Aiur.Generic.ControlLower
