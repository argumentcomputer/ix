import Aiur.Generic.OpenSource
import Aiur.Generic.SourceSimulation

namespace Aiur.Generic.SourceSemantics
set_option linter.unusedSimpArgs false

/-! Induction on finite source evaluations discharges recursive call premises.
Both ordinary fallthrough and an explicit function return close a call. -/

theorem EvalExpr.openCalls [Field F] [DecidableEq F]
    {world : World F} {calls : CallRelation F} {names : List String}
    (closed : ∀ n ∈ names, ∀ args ts ls e, world.prepare n args = .ok (ts, ls, e) →
      inScope names (fun _ => true) ts e = true)
    (step : ∀ n ∈ names, ∀ args ts ls e b v a,
      world.prepare n args = .ok (ts, ls, e) →
      (OpenSource.EvalExpr world calls ts ls e b v a ∨
        OpenSource.EvalExit world calls ts ls e b .function v a) → calls n args b v a)
    (ev : EvalExpr world types locals expr before result after) :
    inScope names (fun _ => true) types expr = true → OpenSource.EvalExpr world calls types locals expr before result after := by
  induction ev using EvalExpr.rec
    (motive_2 := fun ts ls es b vs h _ => (∀ e ∈ es, inScope names (fun _ => true) ts e = true) → OpenSource.EvalArgs world calls ts ls es b vs h)
    (motive_3 := fun n xs b v h _ => n ∈ names → calls n xs b v h)
    (motive_4 := fun ts ls e b target v h _ => inScope names (fun _ => true) ts e = true → OpenSource.EvalExit world calls ts ls e b target v h)
    (motive_5 := fun ts ls es b target v h _ => (∀ e ∈ es, inScope names (fun _ => true) ts e = true) → OpenSource.EvalArgsExit world calls ts ls es b target v h) with
  | block _ ih => intro h; exact .block (ih (by simpa only [inScope] using h))
  | blockExit _ ih => intro h; exact .blockExit (ih (by simpa only [inScope] using h))
  | literal => intro _; exact .literal
  | var h => intro _; exact .var h
  | global lookup interpreted _ ih =>
      intro _
      exact .global lookup interpreted
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
      exact .letValue (ih1 h.1) matched (ih2 h.2)
  | store _ ih => intro h; exact .store (ih (by simpa [inScope] using h))
  | load _ op ih => intro h; exact .load (ih (by simpa [inScope] using h)) op
  | hint _ typed ih =>
      intro h
      simp only [inScope, Bool.and_eq_true] at h
      exact .hint (ih h.2) typed
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
      exact .matchValue (ih1 h.1) selected (ih2 (selected_inScope selected h.2))
  | nil => exact .nil
  | cons _ _ ih1 ih2 =>
      rename_i h
      exact .cons (ih1 (h _ (by simp))) (ih2 (fun e he => h e (by simp [he])))
  | intro prepared _ ih =>
      rename_i hn
      exact step _ hn _ _ _ _ _ _ _ prepared (.inl (ih (closed _ hn _ _ _ _ prepared)))
  | returned prepared _ ih =>
      rename_i hn
      exact step _ hn _ _ _ _ _ _ _ prepared (.inr (ih (closed _ hn _ _ _ _ prepared)))
  | exit _ ih => rename_i h; exact .exit (ih (by simpa only [inScope] using h))
  | exitPayload _ ih => rename_i h; exact .exitPayload (ih (by simpa only [inScope] using h))
  | fromBlock different _ ih => rename_i h; exact .fromBlock different (ih (by simpa only [inScope] using h))
  | fromGlobal lookup interpreted _ ih =>
      rename_i _unused
      exact .fromGlobal lookup interpreted (ih (const_inScope _ interpreted))
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
      exact .letBody (ih1 h.1) matched (ih2 h.2)
  | binaryRight _ _ ih1 ih2 =>
      rename_i h
      simp only [inScope, Bool.and_eq_true] at h
      exact .binaryRight (ih1 h.1) (ih2 h.2)
  | matchBody _ selected _ ih1 ih2 =>
      rename_i h
      simp only [inScope, Bool.and_eq_true, List.all_map, List.all_eq_true, Function.comp_def, id_eq] at h
      exact .matchBody (ih1 h.1) selected (ih2 (selected_inScope selected h.2))
  | head _ ih => rename_i h; exact .head (ih (h _ (by simp)))
  | tail _ _ ih1 ih2 =>
      rename_i h
      exact .tail (ih1 (h _ (by simp))) (ih2 (fun e he => h e (by simp [he])))

theorem EvalExit.openCalls [Field F] [DecidableEq F]
    {world : World F} {calls : CallRelation F} {names : List String}
    (closed : ∀ n ∈ names, ∀ args ts ls e, world.prepare n args = .ok (ts, ls, e) →
      inScope names (fun _ => true) ts e = true)
    (step : ∀ n ∈ names, ∀ args ts ls e b v a,
      world.prepare n args = .ok (ts, ls, e) →
      (OpenSource.EvalExpr world calls ts ls e b v a ∨
        OpenSource.EvalExit world calls ts ls e b .function v a) → calls n args b v a)
    (ev : EvalExit world types locals expr before target result after) :
    inScope names (fun _ => true) types expr = true → OpenSource.EvalExit world calls types locals expr before target result after := by
  induction ev using EvalExit.rec
    (motive_1 := fun ts ls e b v h _ => inScope names (fun _ => true) ts e = true → OpenSource.EvalExpr world calls ts ls e b v h)
    (motive_2 := fun ts ls es b vs h _ => (∀ e ∈ es, inScope names (fun _ => true) ts e = true) → OpenSource.EvalArgs world calls ts ls es b vs h)
    (motive_3 := fun n xs b v h _ => n ∈ names → calls n xs b v h)
    (motive_5 := fun ts ls es b target v h _ => (∀ e ∈ es, inScope names (fun _ => true) ts e = true) → OpenSource.EvalArgsExit world calls ts ls es b target v h) with
  | block _ ih => rename_i h; exact .block (ih (by simpa only [inScope] using h))
  | blockExit _ ih => rename_i h; exact .blockExit (ih (by simpa only [inScope] using h))
  | literal => rename_i _unused; exact .literal
  | var h => rename_i _unused; exact .var h
  | global lookup interpreted _ ih =>
      rename_i _unused
      exact .global lookup interpreted
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
      exact .letValue (ih1 h.1) matched (ih2 h.2)
  | store _ ih => rename_i h; exact .store (ih (by simpa [inScope] using h))
  | load _ op ih => rename_i h; exact .load (ih (by simpa [inScope] using h)) op
  | hint _ typed ih =>
      rename_i h
      simp only [inScope, Bool.and_eq_true] at h
      exact .hint (ih h.2) typed
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
      exact .matchValue (ih1 h.1) selected (ih2 (selected_inScope selected h.2))
  | nil => exact .nil
  | cons _ _ ih1 ih2 =>
      rename_i h
      exact .cons (ih1 (h _ (by simp))) (ih2 (fun e he => h e (by simp [he])))
  | intro prepared _ ih =>
      rename_i hn
      exact step _ hn _ _ _ _ _ _ _ prepared (.inl (ih (closed _ hn _ _ _ _ prepared)))
  | returned prepared _ ih =>
      rename_i hn
      exact step _ hn _ _ _ _ _ _ _ prepared (.inr (ih (closed _ hn _ _ _ _ prepared)))
  | exit _ ih => intro h; exact .exit (ih (by simpa only [inScope] using h))
  | exitPayload _ ih => intro h; exact .exitPayload (ih (by simpa only [inScope] using h))
  | fromBlock different _ ih => intro h; exact .fromBlock different (ih (by simpa only [inScope] using h))
  | fromGlobal lookup interpreted _ ih =>
      intro _
      exact .fromGlobal lookup interpreted (ih (const_inScope _ interpreted))
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
      exact .letBody (ih1 h.1) matched (ih2 h.2)
  | binaryRight _ _ ih1 ih2 =>
      intro h
      simp only [inScope, Bool.and_eq_true] at h
      exact .binaryRight (ih1 h.1) (ih2 h.2)
  | matchBody _ selected _ ih1 ih2 =>
      intro h
      simp only [inScope, Bool.and_eq_true, List.all_map, List.all_eq_true, Function.comp_def, id_eq] at h
      exact .matchBody (ih1 h.1) selected (ih2 (selected_inScope selected h.2))
  | head _ ih => rename_i h; exact .head (ih (h _ (by simp)))
  | tail _ _ ih1 ih2 =>
      rename_i h
      exact .tail (ih1 (h _ (by simp))) (ih2 (fun e he => h e (by simp [he])))

theorem EvalFn.openCalls [Field F] [DecidableEq F]
    {world : World F} {calls : CallRelation F} {names : List String}
    (closed : ∀ n ∈ names, ∀ args ts ls e, world.prepare n args = .ok (ts, ls, e) →
      inScope names (fun _ => true) ts e = true)
    (step : ∀ n ∈ names, ∀ args ts ls e b v a,
      world.prepare n args = .ok (ts, ls, e) →
      (OpenSource.EvalExpr world calls ts ls e b v a ∨
        OpenSource.EvalExit world calls ts ls e b .function v a) → calls n args b v a)
    (ev : EvalFn world name args before result after) (member : name ∈ names) :
    calls name args before result after := by
  cases ev with
  | intro prepared body =>
      exact step _ member _ _ _ _ _ _ _ prepared
        (.inl (body.openCalls closed step (closed _ member _ _ _ _ prepared)))
  | returned prepared body =>
      exact step _ member _ _ _ _ _ _ _ prepared
        (.inr (body.openCalls closed step (closed _ member _ _ _ _ prepared)))

end Aiur.Generic.SourceSemantics
