import Aiur.Generic.Preparation
import Aiur.Generic.TypeFacts
import Aiur.Generic.RecordFacts
import Mathlib.Data.List.Forall2

namespace Aiur.Generic.Preparation
open SourceSemantics

theorem mapM_relation {f : A → Except E B} {xs : List A} {ys : List B}
    (mapped : xs.mapM f = .ok ys) : List.Forall₂ (fun x y => f x = .ok y) xs ys := by
  induction xs generalizing ys with
  | nil => simp at mapped; subst ys; exact .nil
  | cons x xs ih =>
      simp only [List.mapM_cons, except_bind_ok, except_pure_ok] at mapped
      obtain ⟨y, hy, rest, hr, rfl⟩ := mapped
      exact .cons hy (ih hr)

theorem mapM_forall {f : A → Except E B} {xs : List A} {ys : List B} {P : B → Prop}
    (mapped : xs.mapM f = .ok ys)
    (good : ∀ x ∈ xs, ∀ y, f x = .ok y → P y) : ∀ y ∈ ys, P y := by
  induction xs generalizing ys with
  | nil => simp at mapped; subst ys; simp
  | cons x xs ih =>
      simp only [List.mapM_cons, except_bind_ok, except_pure_ok] at mapped
      obtain ⟨y, hy, rest, hr, rfl⟩ := mapped
      intro z hz
      rcases List.mem_cons.mp hz with rfl | hz
      · exact good x (by simp) _ hy
      · exact ih hr (fun x hx => good x (by simp [hx])) z hz

theorem matchList_congr [DecidableEq F]
    {left : A → SourceValue F → Except EvalError (Option (Environment F Nat))}
    {right : B → SourceValue F → Except EvalError (Option (Environment F Nat))}
    {xs : List A} {ys : List B}
    (related : List.Forall₂ (fun x y => ∀ v, left x v = right y v) xs ys)
    (values : List (SourceValue F)) :
    matchListWith left xs values = matchListWith right ys values := by
  induction related generalizing values with
  | nil => cases values <;> rfl
  | cons h _ ih => cases values <;> simp only [matchListWith, h, ih]

theorem matchList_attach [DecidableEq F]
    (run : Pattern F → SourceValue F → Except EvalError (Option (Environment F Nat)))
    (ps : List (Pattern F)) (values : List (SourceValue F)) :
    matchListWith (fun p v => run p.val v) ps.attach values = matchListWith run ps values := by
  apply matchList_congr
  apply (List.forall₂_map_left_iff
    (R := fun p q => ∀ v, run p v = run q v)
    (f := fun p : { p // p ∈ ps } => p.val)).mp
  simpa using (List.forall₂_same.mpr (fun p _ v => rfl) :
    List.Forall₂ (fun p q => ∀ v, run p v = run q v) ps ps)

/-- Instantiating type metadata and unfolding checked const references leaves
every pattern result unchanged, including failed matches and invalid loads.
The prepared pattern no longer depends on any declaration lookup or depth. -/
theorem pattern_match [DecidableEq F] (program : Program F)
    (constant : String → Ty → Except EvalError (Pattern F))
    (lookup : ∀ n t, constant n t = (elaborateConst program n t).mapError
      (fun _ => EvalError.unboundVariable ("::" ++ n)))
    (depth : Nat) (types : Types) (pat : Pattern F) {prepared : Pattern F}
    (expanded : pattern program depth types pat = .ok prepared)
    (other : String → Ty → Except EvalError (Pattern F)) (otherDepth : Nat)
    (heap : Heap F) (value : SourceValue F) :
    matchPatternWith constant depth types heap pat value =
      matchPatternWith other otherDepth [] heap prepared value := by
  have sub (d : Nat) (ts : Types) (p : Pattern F)
      (smaller : Prod.Lex (· < ·) (· < ·) (d, sizeOf p) (depth, sizeOf pat)) {q : Pattern F}
      (h : pattern program d ts p = .ok q) (v : SourceValue F) :
      matchPatternWith constant d ts heap p v = matchPatternWith other otherDepth [] heap q v :=
    pattern_match program constant lookup d ts p h other otherDepth heap v
  have children (ps : List (Pattern F)) (smaller : ∀ p ∈ ps, sizeOf p < sizeOf pat)
      (qs : List (Pattern F)) (mapped : ps.mapM (pattern program depth types) = .ok qs)
      (vs : List (SourceValue F)) :
      matchListWith (fun p v => matchPatternWith constant depth types heap p.val v) ps.attach vs =
        matchListWith (fun q v => matchPatternWith other otherDepth [] heap q.val v) qs.attach vs := by
    rw [matchList_attach, matchList_attach]
    apply matchList_congr
    have rel := mapM_relation mapped
    have withMem : List.Forall₂ (fun p q => p ∈ ps ∧ pattern program depth types p = .ok q) ps qs :=
      (List.forall₂_and_left _ _).mpr ⟨fun _ h => h, rel⟩
    apply withMem.imp
    intro p q h v
    exact sub depth types p (Prod.Lex.right _ (smaller p h.1)) h.2 v
  cases pat with
  | literal | wildcard | bind =>
      simp only [pattern, except_pure_ok] at expanded
      subst prepared
      simp only [matchPatternWith]
  | global name annotation =>
      cases annotation with
      | none => simp [pattern] at expanded
      | some type =>
          cases depth with
          | zero => simp [pattern] at expanded
          | succ depth =>
              simp only [pattern, except_bind_ok] at expanded
              obtain ⟨body, found, expanded⟩ := expanded
              simp only [matchPatternWith, lookup, found, Except.mapError,
                bind, Except.bind]
              exact sub depth [] body (by exact Prod.Lex.left _ _ (by omega)) expanded value
  | orElse left right names =>
      simp only [pattern, except_bind_ok, except_pure_ok] at expanded
      obtain ⟨l, hl, r, hr, rfl⟩ := expanded
      simp only [matchPatternWith, sub depth types left (by apply Prod.Lex.right; simp_wf; omega) hl,
        sub depth types right (by apply Prod.Lex.right; simp_wf; omega) hr]
  | load child =>
      simp only [pattern, except_bind_ok, except_pure_ok] at expanded
      obtain ⟨q, hq, rfl⟩ := expanded
      simp only [matchPatternWith]
      cases loaded : loadValue heap value with
      | error e => rfl
      | ok v =>
          exact sub depth types child (by apply Prod.Lex.right; simp_wf <;> omega) hq v
  | tuple ps | array ps =>
      simp only [pattern, except_bind_ok, except_pure_ok] at expanded
      obtain ⟨qs, hqs, rfl⟩ := expanded
      have lengths := (mapM_relation hqs).length_eq
      cases value <;> simp only [matchPatternWith, lengths]
      rename_i vs
      split
      · rfl
      · exact children ps (by intros; simp_wf; have := List.sizeOf_lt_of_mem ‹_ ∈ _›; omega) qs hqs vs
  | «repeat» child n =>
      simp only [pattern, except_bind_ok, except_pure_ok] at expanded
      obtain ⟨q, hq, rfl⟩ := expanded
      have single := sub depth types child (by apply Prod.Lex.right; simp_wf; omega) hq
      cases value <;> simp only [matchPatternWith]
      rename_i vs
      split
      · rfl
      · apply matchList_congr
        exact List.forall₂_same.mpr (fun _ _ v => single v)
  | record head ps =>
      simp only [pattern, except_bind_ok, except_pure_ok] at expanded
      obtain ⟨qs, hqs, rfl⟩ := expanded
      have base := mapM_relation hqs
      have withMem : List.Forall₂ (fun p q => p ∈ ps ∧ pattern program depth types p = .ok q) ps qs :=
        (List.forall₂_and_left _ _).mpr ⟨fun _ h => h, base⟩
      have rel : List.Forall₂ (fun p q => ∀ v,
          matchPatternWith constant depth types heap p v =
          matchPatternWith other otherDepth [] heap q v) ps qs := by
        apply withMem.imp
        intro p q h v
        exact sub depth types p (Prod.Lex.right _ (by simp_wf; have := List.sizeOf_lt_of_mem h.1; omega)) h.2 v
      have ordered := head.order_rel rel (a := Pattern.wildcard) (b := Pattern.wildcard)
        (by intro v; simp only [matchPatternWith])
      have names : constructorName [] (head.subst types).type = constructorName types head.type := by
        simp [RecordHead.subst, constructorName]
      cases value <;> simp only [match_record, names, RecordHead.order_subst, ordered.length_eq]
      split
      · rfl
      · split
        · simp_all only [ite_true]
        · simp_all only [ite_false]
          exact matchList_congr ordered _
  | construct t ctor ps | constructAs params t ctor ps =>
      simp only [pattern, except_bind_ok, except_pure_ok] at expanded
      obtain ⟨qs, hqs, rfl⟩ := expanded
      have lengths := (mapM_relation hqs).length_eq
      have names : constructorName [] (t.subst types) = constructorName types t := by
        simp only [constructorName, Ty.subst_nil]
      cases value <;> simp only [matchPatternWith, names, lengths]
      rename_i name ctor' vs
      split
      · rfl
      · exact children ps (by intros; simp_wf; have := List.sizeOf_lt_of_mem ‹_ ∈ _›; omega) qs hqs vs
termination_by (depth, sizeOf pat)
decreasing_by exact smaller

end Aiur.Generic.Preparation
