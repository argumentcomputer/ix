import Aiur.Generic.SourceSemantics
import Aiur.Generic.RecordFacts
import Aiur.Generic.PatternFacts
import Mathlib.Data.List.Forall2

namespace Aiur.Generic
open SourceSemantics

theorem option_mapM_relation {f : A → Option B} {xs : List A} {ys : List B}
    (mapped : xs.mapM f = some ys) : List.Forall₂ (fun x y => f x = some y) xs ys := by
  induction xs generalizing ys with
  | nil => simp at mapped; subst ys; exact .nil
  | cons x xs ih =>
      cases head : f x with
      | none => simp [List.mapM_cons, head] at mapped
      | some y =>
          cases tail : xs.mapM f with
          | none => simp [List.mapM_cons, head, tail] at mapped
          | some rest =>
              have same : y :: rest = ys := by simpa [List.mapM_cons, head, tail] using mapped
              subst ys
              exact .cons head (ih tail)

private theorem bindingsList_length [DecidableEq F] {ps : List (Aiur.Pattern F)}
    {values : List (SourceValue F)} (different : ps.length ≠ values.length) :
    Aiur.Pattern.bindingsList ps values = none := by
  induction ps generalizing values with
  | nil => cases values <;> simp_all [Aiur.Pattern.bindingsList]
  | cons p ps ih =>
      cases values with
      | nil => simp [Aiur.Pattern.bindingsList, matchListWith]
      | cons v vs =>
          have h : ps.length ≠ vs.length := by simpa using different
          simp [Aiur.Pattern.bindingsList, ih h]

private theorem matchList_core [DecidableEq F]
    {run : A → SourceValue F → Except EvalError (Option (Environment F Nat))}
    {xs : List A} {ps : List (Aiur.Pattern F)}
    (related : List.Forall₂ (fun x p => ∀ v, run x v = .ok (p.bindings v)) xs ps)
    (values : List (SourceValue F)) :
    matchListWith run xs values = .ok (Aiur.Pattern.bindingsList ps values) := by
  induction related generalizing values with
  | nil => cases values <;> simp [Aiur.Pattern.bindingsList, matchListWith]
  | @cons x p xs ps h related ih =>
      cases values with
      | nil => simp [Aiur.Pattern.bindingsList, matchListWith]
      | cons v vs =>
          simp only [matchListWith, h, Aiur.Pattern.bindingsList]
          cases matched : p.bindings v <;> cases tail : Aiur.Pattern.bindingsList ps vs <;>
            simp [ih vs, tail, bind, Except.bind, pure, Except.pure]

/-- Pure patterns are translated without changing their ordered bindings or
matching condition. Arrays and repeated patterns retain their source meaning
while using tuple storage in the compiler language. -/
theorem Pattern.toCore_match [DecidableEq F] (pat : Pattern F) {core : Aiur.Pattern F}
    (lowered : pat.toCore? types = some core) (value : SourceValue F) :
    matchPatternWith constant depth types heap pat value = .ok (core.bindings value) := by
  have sub (p : Pattern F) (smaller : sizeOf p < sizeOf pat) {c : Aiur.Pattern F}
      (h : p.toCore? types = some c) (v : SourceValue F) :
      matchPatternWith constant depth types heap p v = .ok (c.bindings v) :=
    Pattern.toCore_match p h v
  have children (ps : List (Pattern F)) (smaller : ∀ p ∈ ps, sizeOf p < sizeOf pat)
      (cs : List (Aiur.Pattern F)) (h : ps.mapM (Pattern.toCore? types) = some cs)
      (vs : List (SourceValue F)) :
      matchListWith (fun p v => matchPatternWith constant depth types heap p.val v) ps.attach vs =
        .ok (Aiur.Pattern.bindingsList cs vs) := by
    have rel := option_mapM_relation h
    have attached : List.Forall₂ (fun p c => p.val.toCore? types = some c) ps.attach cs := by
      apply (List.forall₂_map_left_iff (R := fun p c => p.toCore? types = some c)
        (f := fun p : { p // p ∈ ps } => p.val)).mp
      simpa using rel
    apply matchList_core (attached.imp ?_) vs
    intro p c hc v
    exact sub p.val (smaller p.val p.property) hc v
  cases pat with
  | literal x | wildcard | bind name =>
      simp only [Pattern.toCore?, Option.some.injEq] at lowered
      subst core
      simp only [matchPatternWith, Aiur.Pattern.bindings, pure, Except.pure]
  | global | load | orElse => simp [Pattern.toCore?] at lowered
  | tuple ps | array ps =>
      cases mapped : ps.mapM (Pattern.toCore? types) with
      | none => simp [Pattern.toCore?, mapped] at lowered
      | some cs =>
          have same : Aiur.Pattern.tuple cs = core := by simpa [Pattern.toCore?, mapped] using lowered
          subst core
          have lengths := (option_mapM_relation mapped).length_eq
          cases value <;> simp only [matchPatternWith, Aiur.Pattern.bindings, pure, Except.pure, bind, Except.bind]
          rename_i vs
          by_cases equal : ps.length = vs.length
          · simp only [equal, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
            exact children ps (by intros; simp_wf; have := List.sizeOf_lt_of_mem ‹_ ∈ _›; omega) cs mapped vs
          · have unequal : cs.length ≠ vs.length := by omega
            simp [equal, bindingsList_length unequal]
  | «repeat» p n =>
      cases mapped : p.toCore? types with
      | none => simp [Pattern.toCore?, mapped] at lowered
      | some c =>
          have same : Aiur.Pattern.tuple (List.replicate n c) = core := by
            simpa [Pattern.toCore?, mapped] using lowered
          subst core
          cases value <;> simp only [matchPatternWith, Aiur.Pattern.bindings, pure, Except.pure, bind, Except.bind]
          rename_i vs
          by_cases equal : vs.length = n
          · simp only [equal, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
            have single := sub p (by simp_wf <;> omega) mapped
            have rel : ∀ k, List.Forall₂
                (fun (_ : Unit) (cp : Aiur.Pattern F) => ∀ v,
                  matchPatternWith constant depth types heap p v = .ok (cp.bindings v))
                (List.replicate k ()) (List.replicate k c) := by
              intro k
              induction k with
              | zero => exact .nil
              | succ k ih => exact .cons single ih
            exact matchList_core (rel n) vs
          · have unequal : (List.replicate n c).length ≠ vs.length := by simp; omega
            simp [equal, bindingsList_length unequal]
  | record head ps =>
      cases type : (head.type.subst types).toCore <;> simp only [Pattern.toCore?, type] at lowered
      all_goals first | contradiction | skip
      rename_i name
      cases mapped : ps.mapM (Pattern.toCore? types) with
      | none => simp [mapped] at lowered
      | some cs =>
          have same : Aiur.Pattern.construct name structConstructor (head.order cs .wildcard) = core := by
            simpa [mapped] using lowered
          subst core
          have base := option_mapM_relation mapped
          have withMem : List.Forall₂ (fun p c => p ∈ ps ∧ p.toCore? types = some c) ps cs :=
            (List.forall₂_and_left _ _).mpr ⟨fun _ h => h, base⟩
          have rel : List.Forall₂ (fun p c => ∀ v,
              matchPatternWith constant depth types heap p v = .ok (c.bindings v)) ps cs := by
            apply withMem.imp
            intro p c h v
            exact sub p (by simp_wf; have := List.sizeOf_lt_of_mem h.1; omega) h.2 v
          have ordered := head.order_rel rel (a := Pattern.wildcard) (b := Aiur.Pattern.wildcard)
            (by intro v; simp [matchPatternWith, Aiur.Pattern.bindings])
          cases value <;> simp only [match_record, Aiur.Pattern.bindings, constructorName, type]
          rename_i actual ctor vs
          by_cases names : actual = name
          · subst actual
            by_cases ctors : ctor = structConstructor
            · subst ctor
              simp only [beq_self_eq_true, bne_self_eq_false, Bool.false_or, true_and, ↓reduceIte]
              by_cases equal : (head.order ps Pattern.wildcard).length = vs.length
              · simp only [equal, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
                exact matchList_core ordered vs
              · have unequal : (head.order cs Aiur.Pattern.wildcard).length ≠ vs.length := by
                  rw [← ordered.length_eq]; exact equal
                have different : (head.positions ps.length).length ≠ vs.length := by simpa using equal
                simp [different, bindingsList_length unequal]
            · simp [ctors, Ne.symm ctors]
          · simp [names, Ne.symm names]
  | construct t ctor ps | constructAs _ t ctor ps =>
      cases type : (t.subst types).toCore <;> simp only [Pattern.toCore?, type] at lowered
      all_goals first | contradiction | skip
      rename_i name
      cases mapped : ps.mapM (Pattern.toCore? types) with
      | none => simp [mapped] at lowered
      | some cs =>
          have same : Aiur.Pattern.construct name ctor cs = core := by simpa [mapped] using lowered
          subst core
          have lengths := (option_mapM_relation mapped).length_eq
          cases value <;> simp only [matchPatternWith, Aiur.Pattern.bindings, pure, Except.pure, bind, Except.bind]
          rename_i other ctor' vs
          by_cases names : name = other
          · subst other
            by_cases ctors : ctor = ctor'
            · subst ctor'
              simp only [constructorName, type, beq_self_eq_true, bne_self_eq_false,
                Bool.false_or, true_and, ↓reduceIte]
              by_cases equal : ps.length = vs.length
              · simp only [equal, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
                exact children ps (by intros; simp_wf; have := List.sizeOf_lt_of_mem ‹_ ∈ _›; omega) cs mapped vs
              · have unequal : cs.length ≠ vs.length := by omega
                simp [equal, bindingsList_length unequal]
            · simp [constructorName, type, ctors, Ne.symm ctors]
          · simp [constructorName, type, names, Ne.symm names]
termination_by sizeOf pat
decreasing_by all_goals exact smaller

end Aiur.Generic
