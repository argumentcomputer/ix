import Aiur.Generic.SourceSemantics

namespace Aiur.Generic.SourceSemantics
set_option linter.unusedSimpArgs false

def inScope (names : List String) (hintType : Aiur.Ty → Bool) (types : Types) : Expr α → Bool
  | .literal _ | .var _ => true
  | .global _ _ => true
  | .builtin _ xs | .update _ xs | .record _ xs | .tuple xs | .array xs | .construct _ _ _ xs | .constructAs _ _ _ xs => (xs.map (inScope names hintType types)).all id
  | .call n ts xs => names.contains (instanceName types n ts) && (xs.map (inScope names hintType types)).all id
  | .member x _ | .control _ x | .project x _ | .index x _ | .slice x _ _ | .repeat x _ | .store x | .load x | .neg x => inScope names hintType types x
  | .hint t x channel => hintType (t.subst types).toCore && inScope names hintType types x
  | .letValue _ x b | .binary _ x b => inScope names hintType types x && inScope names hintType types b
  | .matchValue x arms => inScope names hintType types x && (arms.map fun a => inScope names hintType types a.2).all id
termination_by e => sizeOf e
decreasing_by
  all_goals simp_wf
  all_goals first | omega | have h := List.sizeOf_lt_of_mem ‹_ ∈ _›; first | omega | cases ‹_ × _›; simp_all only [Prod.mk.sizeOf_spec]; omega

private theorem mapM_forall {xs : List A} {ys : List B} {f : A → Except E B} {P : B → Prop}
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

/-- Const bodies have no calls or hints. Following another const reference
also preserves this syntactic property. -/
theorem const_inScope (pattern : Pattern F) {expr : Expr F}
    (interpreted : Consts.toExpr pattern = .ok expr) :
    inScope names hintType types expr = true := by
  have sub (p : Pattern F) (hsize : sizeOf p < sizeOf pattern) {e : Expr F}
      (h : Consts.toExpr p = .ok e) : inScope names hintType types e = true :=
    const_inScope p h
  have children (ps : List (Pattern F)) (smaller : ∀ p ∈ ps, sizeOf p < sizeOf pattern)
      (es : List (Expr F)) (mapped : ps.mapM Consts.toExpr = .ok es) :
      ∀ e ∈ es, inScope names hintType types e = true :=
    mapM_forall mapped (fun p hp _ h => sub p (smaller p hp) h)
  cases pattern with
  | literal | global =>
      simp only [Consts.toExpr, except_pure_ok] at interpreted
      subst expr
      simp only [inScope]
  | wildcard | bind | orElse => simp [Consts.toExpr] at interpreted
  | load p | «repeat» p n =>
      simp only [Consts.toExpr, except_bind_ok, except_pure_ok] at interpreted
      obtain ⟨e, he, rfl⟩ := interpreted
      simpa only [inScope] using sub p (by simp_wf <;> omega) he
  | record _ ps | tuple ps | array ps | constructAs _ _ _ ps =>
      simp only [Consts.toExpr, except_bind_ok, except_pure_ok] at interpreted
      obtain ⟨es, mapped, rfl⟩ := interpreted
      simp only [inScope, List.all_map, List.all_eq_true, Function.comp_def, id_eq]
      exact children ps (by intros; simp_wf; have := List.sizeOf_lt_of_mem ‹_ ∈ _›; omega) es mapped
  | construct t c ps =>
      cases t <;> simp only [Consts.toExpr] at interpreted
      all_goals first | contradiction | skip
      simp only [except_bind_ok, except_pure_ok] at interpreted
      obtain ⟨es, mapped, rfl⟩ := interpreted
      simp only [inScope, List.all_map, List.all_eq_true, Function.comp_def, id_eq]
      exact children ps (by intros; simp_wf; have := List.sizeOf_lt_of_mem ‹_ ∈ _›; omega) es mapped
termination_by sizeOf pattern
decreasing_by
  all_goals exact hsize

theorem selected_inScope [DecidableEq F] {input : SourceValue F} {arms : List (Pattern F × Expr F)}
    (selected : selectArm world types heap input arms = .ok (some (bindings, body)))
    (safe : ∀ a ∈ arms, inScope names hintType types a.2 = true) : inScope names hintType types body = true := by
  induction arms with
  | nil => simp [selectArm] at selected
  | cons a rest ih =>
      rcases a with ⟨p, e⟩
      cases matched : world.matchPattern types heap p input with
      | error e => simp [selectArm, matched, bind, Except.bind] at selected
      | ok bs => cases bs with
        | none => exact ih (by simpa [selectArm, matched, bind, Except.bind, pure, Except.pure] using selected) (fun a h => safe a (by simp [h]))
        | some bs =>
            obtain ⟨rfl, rfl⟩ := (by simpa [selectArm, matched, bind, Except.bind, pure, Except.pure] using selected : bs = bindings ∧ e = body)
            exact safe (p, e) (by simp)

/-- The finite certificate concerns syntax and lookup, not evaluation or
termination. This simulation works for all finite evaluations and all hints. -/
structure Agreement (left right : World F) (names : List String) (hintType : Aiur.Ty → Bool) : Prop where
  constants : left.constant = right.constant
  constDepth : left.constDepth = right.constDepth
  prepare : ∀ n ∈ names, ∀ args types locals body,
    left.prepare n args = .ok (types, locals, body) ↔ right.prepare n args = .ok (types, locals, body)
  hint : ∀ t, hintType t = true → ∀ v, left.typed t v = true ↔ right.typed t v = true
  closed : ∀ n ∈ names, ∀ args types locals body,
    left.prepare n args = .ok (types, locals, body) → inScope names hintType types body = true

def Agreement.symm (a : Agreement left right names hintType) : Agreement right left names hintType where
  constants := a.constants.symm
  constDepth := a.constDepth.symm
  prepare n hn args types locals body := (a.prepare n hn args types locals body).symm
  hint t ht v := (a.hint t ht v).symm
  closed n hn args types locals body h := a.closed n hn args types locals body ((a.prepare n hn args types locals body).mpr h)

variable {F : Type} {left right : World F} {names : List String} {hintType : Aiur.Ty → Bool}

theorem Agreement.patterns [DecidableEq F] (a : Agreement left right names hintType) :
    left.matchPattern = right.matchPattern := by
  simp only [World.matchPattern, a.constants, a.constDepth]

theorem Agreement.select [DecidableEq F] (a : Agreement left right names hintType) :
    selectArm left types heap input arms = selectArm right types heap input arms := by
  induction arms with
  | nil => rfl
  | cons arm rest ih => simp only [selectArm, a.patterns, ih]



theorem EvalExpr.transfer [Field F] [DecidableEq F]
    (a : Agreement left right names hintType)
    (ev : EvalExpr left types locals expr before result after) :
    inScope names hintType types expr = true → EvalExpr right types locals expr before result after := by
  induction ev using EvalExpr.rec
    (motive_2 := fun ts ls es b vs h _ => (∀ e ∈ es, inScope names hintType ts e = true) → EvalArgs right ts ls es b vs h)
    (motive_3 := fun n xs b v h _ => n ∈ names → EvalFn right n xs b v h)
    (motive_4 := fun ts ls e b target v h _ => inScope names hintType ts e = true → EvalExit right ts ls e b target v h)
    (motive_5 := fun ts ls es b target v h _ => (∀ e ∈ es, inScope names hintType ts e = true) → EvalArgsExit right ts ls es b target v h) with
  | block _ ih => intro h; exact .block (ih (by simpa only [inScope] using h))
  | blockExit _ ih => intro h; exact .blockExit (ih (by simpa only [inScope] using h))
  | literal => intro _; exact .literal
  | var h => intro _; exact .var h
  | global lookup interpreted _ ih =>
      intro _
      exact .global (by simpa only [← a.constants] using lookup) interpreted
        (ih (const_inScope _ interpreted))
  | tuple _ ih => intro h; exact .tuple (ih (by simpa [inScope] using h))
  | array _ ih => intro h; exact .array (ih (by simpa [inScope] using h))
  | «repeat» _ ih => intro h; exact .repeat (ih (by simpa [inScope] using h))
  | index _ op ih => intro h; exact .index (ih (by simpa [inScope] using h)) op
  | slice _ op ih => intro h; exact .slice (ih (by simpa [inScope] using h)) op
  | constructAs _ ih => intro h; exact .constructAs (ih (by simpa [inScope] using h))
  | builtin _ op ih => intro h; exact .builtin (ih (by simpa [inScope] using h)) op
  | update _ op ih => intro h; exact .update (ih (by simpa [inScope] using h)) op
  | record _ ih => intro h; exact .record (ih (by simpa [inScope] using h))
  | construct _ ih => intro h; exact .construct (ih (by simpa [inScope] using h))
  | project _ op ih => intro h; exact .project (ih (by simpa [inScope] using h)) op
  | member _ op ih => intro h; exact .member (ih (by simpa [inScope] using h)) op
  | letValue _ matched _ ih1 ih2 =>
      intro h
      simp only [inScope, Bool.and_eq_true] at h
      exact .letValue (ih1 h.1) (by simpa only [← a.patterns] using matched) (ih2 h.2)
  | store _ ih => intro h; exact .store (ih (by simpa [inScope] using h))
  | load _ op ih => intro h; exact .load (ih (by simpa [inScope] using h)) op
  | hint _ typed ih =>
      intro h
      simp only [inScope, Bool.and_eq_true] at h
      exact .hint (ih h.2) ((a.hint _ h.1 _).mp typed)
  | neg _ op ih => intro h; exact .neg (ih (by simpa [inScope] using h)) op
  | binary _ _ op ih1 ih2 =>
      intro h
      simp only [inScope, Bool.and_eq_true] at h
      exact .binary (ih1 h.1) (ih2 h.2) op
  | call _ _ ih1 ih2 =>
      intro h
      simp only [inScope, Bool.and_eq_true, List.contains_iff_mem, List.all_map, List.all_eq_true, Function.comp_def, id_eq] at h
      exact .call (ih1 h.2) (ih2 h.1)
  | matchValue _ selected _ ih1 ih2 =>
      intro h
      simp only [inScope, Bool.and_eq_true, List.all_map, List.all_eq_true, Function.comp_def, id_eq] at h
      exact .matchValue (ih1 h.1) (by rw [← a.select]; exact selected) (ih2 (selected_inScope selected h.2))
  | nil => exact .nil
  | cons _ _ ih1 ih2 =>
      rename_i h
      exact .cons (ih1 (h _ (by simp))) (ih2 (fun e he => h e (by simp [he])))
  | intro prepared _ ih =>
      rename_i hn
      exact .intro ((a.prepare _ hn _ _ _ _).mp prepared) (ih (a.closed _ hn _ _ _ _ prepared))
  | returned prepared _ ih =>
      rename_i hn
      exact .returned ((a.prepare _ hn _ _ _ _).mp prepared) (ih (a.closed _ hn _ _ _ _ prepared))
  | exit _ ih => rename_i h; exact .exit (ih (by simpa only [inScope] using h))
  | exitPayload _ ih => rename_i h; exact .exitPayload (ih (by simpa only [inScope] using h))
  | fromBlock different _ ih => rename_i h; exact .fromBlock different (ih (by simpa only [inScope] using h))
  | fromGlobal lookup interpreted _ ih =>
      rename_i _unused
      exact .fromGlobal (by simpa only [← a.constants] using lookup) interpreted (ih (const_inScope _ interpreted))
  | fromTuple _ ih => rename_i h; exact .fromTuple (ih (by simpa [inScope] using h))
  | fromArray _ ih => rename_i h; exact .fromArray (ih (by simpa [inScope] using h))
  | fromRepeat _ ih => rename_i h; exact .fromRepeat (ih (by simpa [inScope] using h))
  | fromIndex _ ih => rename_i h; exact .fromIndex (ih (by simpa [inScope] using h))
  | fromSlice _ ih => rename_i h; exact .fromSlice (ih (by simpa [inScope] using h))
  | fromConstructAs _ ih => rename_i h; exact .fromConstructAs (ih (by simpa [inScope] using h))
  | fromBuiltin _ ih => rename_i h; exact .fromBuiltin (ih (by simpa [inScope] using h))
  | fromUpdate _ ih => rename_i h; exact .fromUpdate (ih (by simpa [inScope] using h))
  | fromRecord _ ih => rename_i h; exact .fromRecord (ih (by simpa [inScope] using h))
  | fromConstruct _ ih => rename_i h; exact .fromConstruct (ih (by simpa [inScope] using h))
  | fromProject _ ih => rename_i h; exact .fromProject (ih (by simpa [inScope] using h))
  | fromMember _ ih => rename_i h; exact .fromMember (ih (by simpa [inScope] using h))
  | fromStore _ ih => rename_i h; exact .fromStore (ih (by simpa [inScope] using h))
  | fromLoad _ ih => rename_i h; exact .fromLoad (ih (by simpa [inScope] using h))
  | fromNeg _ ih => rename_i h; exact .fromNeg (ih (by simpa [inScope] using h))
  | fromLetValue _ ih =>
      rename_i h
      simp only [inScope, Bool.and_eq_true, List.all_map, List.all_eq_true, Function.comp_def, id_eq] at h
      exact .fromLetValue (ih h.1)
  | fromHint _ ih =>
      rename_i h
      simp only [inScope, Bool.and_eq_true, List.all_map, List.all_eq_true, Function.comp_def, id_eq] at h
      exact .fromHint (ih h.2)
  | binaryLeft _ ih =>
      rename_i h
      simp only [inScope, Bool.and_eq_true, List.all_map, List.all_eq_true, Function.comp_def, id_eq] at h
      exact .binaryLeft (ih h.1)
  | fromCall _ ih =>
      rename_i h
      simp only [inScope, Bool.and_eq_true, List.all_map, List.all_eq_true, Function.comp_def, id_eq] at h
      exact .fromCall (ih h.2)
  | fromMatchValue _ ih =>
      rename_i h
      simp only [inScope, Bool.and_eq_true, List.all_map, List.all_eq_true, Function.comp_def, id_eq] at h
      exact .fromMatchValue (ih h.1)
  | letBody _ matched _ ih1 ih2 =>
      rename_i h
      simp only [inScope, Bool.and_eq_true] at h
      exact .letBody (ih1 h.1) (by simpa only [← a.patterns] using matched) (ih2 h.2)
  | binaryRight _ _ ih1 ih2 =>
      rename_i h
      simp only [inScope, Bool.and_eq_true] at h
      exact .binaryRight (ih1 h.1) (ih2 h.2)
  | matchBody _ selected _ ih1 ih2 =>
      rename_i h
      simp only [inScope, Bool.and_eq_true, List.all_map, List.all_eq_true, Function.comp_def, id_eq] at h
      exact .matchBody (ih1 h.1) (by rw [← a.select]; exact selected) (ih2 (selected_inScope selected h.2))
  | head _ ih => rename_i h; exact .head (ih (h _ (by simp)))
  | tail _ _ ih1 ih2 =>
      rename_i h
      exact .tail (ih1 (h _ (by simp))) (ih2 (fun e he => h e (by simp [he])))

theorem EvalExit.transfer [Field F] [DecidableEq F]
    (a : Agreement left right names hintType)
    (ev : EvalExit left types locals expr before target result after) :
    inScope names hintType types expr = true → EvalExit right types locals expr before target result after := by
  induction ev using EvalExit.rec
    (motive_1 := fun ts ls e b v h _ => inScope names hintType ts e = true → EvalExpr right ts ls e b v h)
    (motive_2 := fun ts ls es b vs h _ => (∀ e ∈ es, inScope names hintType ts e = true) → EvalArgs right ts ls es b vs h)
    (motive_3 := fun n xs b v h _ => n ∈ names → EvalFn right n xs b v h)
    (motive_5 := fun ts ls es b target v h _ => (∀ e ∈ es, inScope names hintType ts e = true) → EvalArgsExit right ts ls es b target v h) with
  | block _ ih => rename_i h; exact .block (ih (by simpa only [inScope] using h))
  | blockExit _ ih => rename_i h; exact .blockExit (ih (by simpa only [inScope] using h))
  | literal => rename_i _unused; exact .literal
  | var h => rename_i _unused; exact .var h
  | global lookup interpreted _ ih =>
      rename_i _unused
      exact .global (by simpa only [← a.constants] using lookup) interpreted
        (ih (const_inScope _ interpreted))
  | tuple _ ih => rename_i h; exact .tuple (ih (by simpa [inScope] using h))
  | array _ ih => rename_i h; exact .array (ih (by simpa [inScope] using h))
  | «repeat» _ ih => rename_i h; exact .repeat (ih (by simpa [inScope] using h))
  | index _ op ih => rename_i h; exact .index (ih (by simpa [inScope] using h)) op
  | slice _ op ih => rename_i h; exact .slice (ih (by simpa [inScope] using h)) op
  | constructAs _ ih => rename_i h; exact .constructAs (ih (by simpa [inScope] using h))
  | builtin _ op ih => rename_i h; exact .builtin (ih (by simpa [inScope] using h)) op
  | update _ op ih => rename_i h; exact .update (ih (by simpa [inScope] using h)) op
  | record _ ih => rename_i h; exact .record (ih (by simpa [inScope] using h))
  | construct _ ih => rename_i h; exact .construct (ih (by simpa [inScope] using h))
  | project _ op ih => rename_i h; exact .project (ih (by simpa [inScope] using h)) op
  | member _ op ih => rename_i h; exact .member (ih (by simpa [inScope] using h)) op
  | letValue _ matched _ ih1 ih2 =>
      rename_i h
      simp only [inScope, Bool.and_eq_true] at h
      exact .letValue (ih1 h.1) (by simpa only [← a.patterns] using matched) (ih2 h.2)
  | store _ ih => rename_i h; exact .store (ih (by simpa [inScope] using h))
  | load _ op ih => rename_i h; exact .load (ih (by simpa [inScope] using h)) op
  | hint _ typed ih =>
      rename_i h
      simp only [inScope, Bool.and_eq_true] at h
      exact .hint (ih h.2) ((a.hint _ h.1 _).mp typed)
  | neg _ op ih => rename_i h; exact .neg (ih (by simpa [inScope] using h)) op
  | binary _ _ op ih1 ih2 =>
      rename_i h
      simp only [inScope, Bool.and_eq_true] at h
      exact .binary (ih1 h.1) (ih2 h.2) op
  | call _ _ ih1 ih2 =>
      rename_i h
      simp only [inScope, Bool.and_eq_true, List.contains_iff_mem, List.all_map, List.all_eq_true, Function.comp_def, id_eq] at h
      exact .call (ih1 h.2) (ih2 h.1)
  | matchValue _ selected _ ih1 ih2 =>
      rename_i h
      simp only [inScope, Bool.and_eq_true, List.all_map, List.all_eq_true, Function.comp_def, id_eq] at h
      exact .matchValue (ih1 h.1) (by rw [← a.select]; exact selected) (ih2 (selected_inScope selected h.2))
  | nil => exact .nil
  | cons _ _ ih1 ih2 =>
      rename_i h
      exact .cons (ih1 (h _ (by simp))) (ih2 (fun e he => h e (by simp [he])))
  | intro prepared _ ih =>
      rename_i hn
      exact .intro ((a.prepare _ hn _ _ _ _).mp prepared) (ih (a.closed _ hn _ _ _ _ prepared))
  | returned prepared _ ih =>
      rename_i hn
      exact .returned ((a.prepare _ hn _ _ _ _).mp prepared) (ih (a.closed _ hn _ _ _ _ prepared))
  | exit _ ih => intro h; exact .exit (ih (by simpa only [inScope] using h))
  | exitPayload _ ih => intro h; exact .exitPayload (ih (by simpa only [inScope] using h))
  | fromBlock different _ ih => intro h; exact .fromBlock different (ih (by simpa only [inScope] using h))
  | fromGlobal lookup interpreted _ ih =>
      intro _
      exact .fromGlobal (by simpa only [← a.constants] using lookup) interpreted (ih (const_inScope _ interpreted))
  | fromTuple _ ih => intro h; exact .fromTuple (ih (by simpa [inScope] using h))
  | fromArray _ ih => intro h; exact .fromArray (ih (by simpa [inScope] using h))
  | fromRepeat _ ih => intro h; exact .fromRepeat (ih (by simpa [inScope] using h))
  | fromIndex _ ih => intro h; exact .fromIndex (ih (by simpa [inScope] using h))
  | fromSlice _ ih => intro h; exact .fromSlice (ih (by simpa [inScope] using h))
  | fromConstructAs _ ih => intro h; exact .fromConstructAs (ih (by simpa [inScope] using h))
  | fromBuiltin _ ih => intro h; exact .fromBuiltin (ih (by simpa [inScope] using h))
  | fromUpdate _ ih => intro h; exact .fromUpdate (ih (by simpa [inScope] using h))
  | fromRecord _ ih => intro h; exact .fromRecord (ih (by simpa [inScope] using h))
  | fromConstruct _ ih => intro h; exact .fromConstruct (ih (by simpa [inScope] using h))
  | fromProject _ ih => intro h; exact .fromProject (ih (by simpa [inScope] using h))
  | fromMember _ ih => intro h; exact .fromMember (ih (by simpa [inScope] using h))
  | fromStore _ ih => intro h; exact .fromStore (ih (by simpa [inScope] using h))
  | fromLoad _ ih => intro h; exact .fromLoad (ih (by simpa [inScope] using h))
  | fromNeg _ ih => intro h; exact .fromNeg (ih (by simpa [inScope] using h))
  | fromLetValue _ ih =>
      intro h
      simp only [inScope, Bool.and_eq_true, List.all_map, List.all_eq_true, Function.comp_def, id_eq] at h
      exact .fromLetValue (ih h.1)
  | fromHint _ ih =>
      intro h
      simp only [inScope, Bool.and_eq_true, List.all_map, List.all_eq_true, Function.comp_def, id_eq] at h
      exact .fromHint (ih h.2)
  | binaryLeft _ ih =>
      intro h
      simp only [inScope, Bool.and_eq_true, List.all_map, List.all_eq_true, Function.comp_def, id_eq] at h
      exact .binaryLeft (ih h.1)
  | fromCall _ ih =>
      intro h
      simp only [inScope, Bool.and_eq_true, List.all_map, List.all_eq_true, Function.comp_def, id_eq] at h
      exact .fromCall (ih h.2)
  | fromMatchValue _ ih =>
      intro h
      simp only [inScope, Bool.and_eq_true, List.all_map, List.all_eq_true, Function.comp_def, id_eq] at h
      exact .fromMatchValue (ih h.1)
  | letBody _ matched _ ih1 ih2 =>
      intro h
      simp only [inScope, Bool.and_eq_true] at h
      exact .letBody (ih1 h.1) (by simpa only [← a.patterns] using matched) (ih2 h.2)
  | binaryRight _ _ ih1 ih2 =>
      intro h
      simp only [inScope, Bool.and_eq_true] at h
      exact .binaryRight (ih1 h.1) (ih2 h.2)
  | matchBody _ selected _ ih1 ih2 =>
      intro h
      simp only [inScope, Bool.and_eq_true, List.all_map, List.all_eq_true, Function.comp_def, id_eq] at h
      exact .matchBody (ih1 h.1) (by rw [← a.select]; exact selected) (ih2 (selected_inScope selected h.2))
  | head _ ih => rename_i h; exact .head (ih (h _ (by simp)))
  | tail _ _ ih1 ih2 =>
      rename_i h
      exact .tail (ih1 (h _ (by simp))) (ih2 (fun e he => h e (by simp [he])))

theorem EvalFn.transfer [Field F] [DecidableEq F]
    (a : Agreement left right names hintType) (hn : n ∈ names)
    (ev : EvalFn left n args before result after) : EvalFn right n args before result after := by
  cases ev with
  | intro prepared body =>
      exact .intro ((a.prepare _ hn _ _ _ _).mp prepared)
        (body.transfer a (a.closed _ hn _ _ _ _ prepared))
  | returned prepared body =>
      exact .returned ((a.prepare _ hn _ _ _ _).mp prepared)
        (body.transfer a (a.closed _ hn _ _ _ _ prepared))

theorem evalFn_iff [Field F] [DecidableEq F]
    (a : Agreement left right names hintType) (hn : n ∈ names) :
    EvalFn left n args before result after ↔ EvalFn right n args before result after :=
  ⟨EvalFn.transfer a hn, EvalFn.transfer a.symm hn⟩

end Aiur.Generic.SourceSemantics
