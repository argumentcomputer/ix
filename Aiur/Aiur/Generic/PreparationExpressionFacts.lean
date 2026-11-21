import Aiur.Generic.UpdateSubstitution
import Aiur.Generic.ConstScopeFacts
import Aiur.Generic.ControlNoExit

namespace Aiur.Generic.Preparation

theorem expression_closed (program : Program F) (depth : Nat) (types) (expr : Expr F)
    (closed : Consts.Closed expr) {prepared : Expr F}
    (expanded : expression program depth types expr = .ok prepared) : Consts.Closed prepared := by
  have sub (d ts e) (smaller : Prod.Lex (· < ·) (· < ·) (d, sizeOf e) (depth, sizeOf expr))
      (hc : Consts.Closed e) {q : Expr F} (h : expression program d ts e = .ok q) : Consts.Closed q :=
    expression_closed program d ts e hc h
  cases closed with
  | literal =>
      simp only [expression, except_pure_ok] at expanded
      subst prepared; exact .literal
  | global =>
      rename_i n annotation
      cases annotation with
      | none => simp [expression] at expanded
      | some t =>
          cases depth with
          | zero => simp [expression] at expanded
          | succ d =>
              simp only [expression, except_bind_ok] at expanded
              obtain ⟨pat, _, body, interpreted, expanded⟩ := expanded
              exact sub d [] body (Prod.Lex.left _ _ (by omega)) (Consts.toExpr_closed _ interpreted) expanded
  | store hc | «repeat» hc =>
      simp only [expression, except_bind_ok, except_pure_ok] at expanded
      obtain ⟨q, hq, rfl⟩ := expanded
      constructor
      exact sub _ _ _ (by apply Prod.Lex.right; simp_wf <;> omega) hc hq
  | record hc | tuple hc | array hc | construct hc | constructAs hc =>
      simp only [expression, except_bind_ok, except_pure_ok] at expanded
      obtain ⟨qs, hqs, rfl⟩ := expanded
      constructor
      refine mapM_forall hqs ?_
      intro e he q hq
      exact sub _ _ _ (by apply Prod.Lex.right; simp_wf; have := List.sizeOf_lt_of_mem he; omega)
        (hc e he) hq
termination_by (depth, sizeOf expr)
decreasing_by all_goals exact smaller

end Aiur.Generic.Preparation

namespace Aiur.Generic.SourceSemantics
variable {calls : CallRelation F}
open Preparation

private theorem args_congr [Field F] [DecidableEq F] {world : World F}
    {left right : Types} {xs ys : List (Expr F)}
    (related : List.Forall₂ (fun x y => ∀ locals before result after,
      OpenSource.EvalExpr world calls left locals x before result after ↔
        OpenSource.EvalExpr world calls right locals y before result after) xs ys)
    (locals before values after) :
    OpenSource.EvalArgs world calls left locals xs before values after ↔ OpenSource.EvalArgs world calls right locals ys before values after := by
  induction related generalizing before values with
  | nil => constructor <;> intro h <;> cases h <;> exact .nil
  | cons h _ ih =>
      constructor
      · intro ev; cases ev with
        | cons head tail => exact .cons ((h _ _ _ _).mp head) ((ih _ _).mp tail)
      · intro ev; cases ev with
        | cons head tail => exact .cons ((h _ _ _ _).mpr head) ((ih _ _).mpr tail)

private theorem args_exit_congr [Field F] [DecidableEq F] {world : World F}
    {left right : Types} {xs ys : List (Expr F)}
    (related : List.Forall₂ (fun x y =>
      (∀ locals before result after, OpenSource.EvalExpr world calls left locals x before result after ↔
        OpenSource.EvalExpr world calls right locals y before result after) ∧
      (∀ locals before target result after, OpenSource.EvalExit world calls left locals x before target result after ↔
        OpenSource.EvalExit world calls right locals y before target result after)) xs ys)
    (locals before target result after) :
    OpenSource.EvalArgsExit world calls left locals xs before target result after ↔
      OpenSource.EvalArgsExit world calls right locals ys before target result after := by
  induction related generalizing before with
  | nil => constructor <;> intro h <;> cases h
  | cons h _ ih =>
      constructor
      · intro ev; cases ev with
        | head head => exact .head ((h.2 _ _ _ _ _).mp head)
        | tail head tail => exact .tail ((h.1 _ _ _ _).mp head) ((ih _).mp tail)
      · intro ev; cases ev with
        | head head => exact .head ((h.2 _ _ _ _ _).mpr head)
        | tail head tail => exact .tail ((h.1 _ _ _ _).mpr head) ((ih _).mpr tail)

private theorem select_transfer [DecidableEq F] {world : World F}
    {left right : Types} {arms others : List (Pattern F × Expr F)}
    {R : Expr F → Expr F → Prop}
    (related : List.Forall₂ (fun a b =>
      (∀ heap value, world.matchPattern left heap a.1 value = world.matchPattern right heap b.1 value) ∧
      R a.2 b.2) arms others)
    (selected : selectArm world left heap value arms = .ok (some (bindings, body))) :
    ∃ other, selectArm world right heap value others = .ok (some (bindings, other)) ∧ R body other := by
  induction related with
  | nil => simp [selectArm] at selected
  | @cons a b arms others h _ ih =>
      cases matched : world.matchPattern left heap a.1 value with
      | error e => simp [selectArm, matched, bind, Except.bind] at selected
      | ok result => cases result with
        | none =>
            obtain ⟨other, hs, hr⟩ := ih (by simpa [selectArm, matched, bind, Except.bind] using selected)
            exact ⟨other, by simpa [selectArm, ← h.1, matched, bind, Except.bind] using hs, hr⟩
        | some bs =>
            have same : bs = bindings ∧ a.2 = body := by
              simpa [selectArm, matched, bind, Except.bind, pure, Except.pure] using selected
            obtain ⟨rfl, rfl⟩ := same
            exact ⟨b.2, by simp [selectArm, ← h.1, matched, bind, Except.bind, pure, Except.pure], h.2⟩

mutual
/-- Compiler preparation preserves and reflects the independent source
predicate. Calls retain their ordinary source semantics; only type metadata
and checked declaration references change in this pass. -/
theorem expression_preparation_open_iff [Field F] [DecidableEq F]
    (program : Program F) (world : World F)
    (lookup : ∀ n t, world.constant n t = (elaborateConst program n t).mapError
      (fun _ => EvalError.unboundVariable ("::" ++ n)))
    (constDepth : world.constDepth = program.consts.length + 1)
    (depth : Nat) (types : Types) (expr : Expr F) {prepared : Expr F}
    (expanded : expression program depth types expr = .ok prepared)
    (locals before result after) :
    OpenSource.EvalExpr world calls types locals expr before result after ↔
      OpenSource.EvalExpr world calls [] locals prepared before result after := by
  have sub (d ts e) (smaller : Prod.Lex (· < ·) (· < ·) (d, sizeOf e) (depth, sizeOf expr))
      {q : Expr F} (h : expression program d ts e = .ok q) (ls b v a) :
      OpenSource.EvalExpr world calls ts ls e b v a ↔ OpenSource.EvalExpr world calls [] ls q b v a :=
    expression_preparation_open_iff program world lookup constDepth d ts e h ls b v a
  have subExit (d ts e) (smaller : Prod.Lex (· < ·) (· < ·) (d, sizeOf e) (depth, sizeOf expr))
      {q : Expr F} (h : expression program d ts e = .ok q) (ls b target v a) :
      OpenSource.EvalExit world calls ts ls e b target v a ↔ OpenSource.EvalExit world calls [] ls q b target v a :=
    exit_preparation_open_iff program world lookup constDepth d ts e h ls b target v a
  have children (es : List (Expr F)) (smaller : ∀ e ∈ es, sizeOf e < sizeOf expr)
      {qs : List (Expr F)} (mapped : es.mapM (expression program depth types) = .ok qs) :
      List.Forall₂ (fun e q => ∀ ls b v a,
        OpenSource.EvalExpr world calls types ls e b v a ↔ OpenSource.EvalExpr world calls [] ls q b v a) es qs := by
    have rel := mapM_relation mapped
    have both : List.Forall₂ (fun e q => e ∈ es ∧ expression program depth types e = .ok q) es qs :=
      (List.forall₂_and_left _ _).mpr ⟨fun _ h => h, rel⟩
    exact both.imp (fun e q h => sub depth types e (Prod.Lex.right _ (smaller e h.1)) h.2)
  have patterns (pat q : Pattern F) (h : pattern program (program.consts.length + 1) types pat = .ok q)
      (heap value) : world.matchPattern types heap pat value = world.matchPattern [] heap q value := by
    simp only [World.matchPattern, constDepth]
    exact pattern_match program world.constant lookup _ _ _ h world.constant _ heap value
  cases expr with
  | control kind e =>
      simp only [expression, except_bind_ok, except_pure_ok] at expanded
      obtain ⟨q, hq, rfl⟩ := expanded
      have ihn := sub depth types e (by apply Prod.Lex.right; simp_wf; omega) hq
      have ihe := subExit depth types e (by apply Prod.Lex.right; simp_wf; omega) hq
      cases kind with
      | exit target => constructor <;> intro h <;> cases h
      | block label =>
          constructor
          · intro h; cases h with
            | block ev => exact .block ((ihn _ _ _ _).mp ev)
            | blockExit ev => exact .blockExit ((ihe _ _ _ _ _).mp ev)
          · intro h; cases h with
            | block ev => exact .block ((ihn _ _ _ _).mpr ev)
            | blockExit ev => exact .blockExit ((ihe _ _ _ _ _).mpr ev)
  | literal x | var n =>
      simp only [expression, except_pure_ok] at expanded
      subst prepared
      constructor <;> intro h <;> cases h <;> constructor <;> assumption
  | global n annotation =>
      cases annotation with
      | none => simp [expression] at expanded
      | some t =>
          cases depth with
          | zero => simp [expression] at expanded
          | succ d =>
              simp only [expression, except_bind_ok] at expanded
              obtain ⟨pat, found, body, interpreted, expanded⟩ := expanded
              have resolved : world.constant n (t.subst types) = .ok pat := by
                simp only [lookup, found, Except.mapError]
              have bodyClosed := Consts.toExpr_closed _ interpreted
              have preparedClosed := expression_closed program d [] body bodyClosed expanded
              have ih := sub d [] body (Prod.Lex.left _ _ (by omega)) expanded [] before result after
              constructor
              · intro h; cases h with
                | global found' interpreted' ev =>
                    have same := found'.symm.trans resolved
                    cases Except.ok.inj same
                    have same := interpreted'.symm.trans interpreted
                    cases Except.ok.inj same
                    exact preparedClosed.openChangeLocals (ih.mp ev) locals
              · intro h
                exact .global resolved interpreted (ih.mpr (preparedClosed.openChangeLocals h []))
  | tuple es | array es =>
      simp only [expression, except_bind_ok, except_pure_ok] at expanded
      obtain ⟨qs, hqs, rfl⟩ := expanded
      have rel := children es (by intros; simp_wf; have := List.sizeOf_lt_of_mem ‹_ ∈ _›; omega) hqs
      have ih := args_congr rel
      constructor
      · intro h; cases h
        first | exact .tuple ((ih _ _ _ _).mp ‹_›) | exact .array ((ih _ _ _ _).mp ‹_›)
      · intro h; cases h
        first | exact .tuple ((ih _ _ _ _).mpr ‹_›) | exact .array ((ih _ _ _ _).mpr ‹_›)
  | constructAs params t ctor es =>
      simp only [expression, except_bind_ok, except_pure_ok] at expanded
      obtain ⟨qs, hqs, rfl⟩ := expanded
      have rel := children es (by intros; simp_wf; have := List.sizeOf_lt_of_mem ‹_ ∈ _›; omega) hqs
      have ih := args_congr rel
      have names : constructorName [] (t.subst types) = constructorName types t := by
        simp only [constructorName, Ty.subst_nil]
      constructor
      · intro h; cases h with
        | constructAs ev =>
            simpa only [names] using (OpenSource.EvalExpr.constructAs (params := params) (t := t.subst types)
              (ctor := ctor) ((ih _ _ _ _).mp ev))
      · intro h; cases h with
        | constructAs ev =>
            simpa only [names] using (OpenSource.EvalExpr.constructAs (params := params) (t := t)
              (ctor := ctor) ((ih _ _ _ _).mpr ev))
  | builtin paths es =>
      simp only [expression, except_bind_ok, except_pure_ok] at expanded
      obtain ⟨qs, hqs, rfl⟩ := expanded
      have rel := children es (by intros; simp_wf; have := List.sizeOf_lt_of_mem ‹_ ∈ _›; omega) hqs
      have ih := args_congr rel
      constructor
      · intro h; cases h with
        | builtin ev op => exact .builtin ((ih _ _ _ _).mp ev) (by simpa only [Builtin.apply_subst] using op)
      · intro h; cases h with
        | builtin ev op => exact .builtin ((ih _ _ _ _).mpr ev) (by simpa only [Builtin.apply_subst] using op)
  | update paths es =>
      simp only [expression, except_bind_ok, except_pure_ok] at expanded
      obtain ⟨qs, hqs, rfl⟩ := expanded
      have rel := children es (by intros; simp_wf; have := List.sizeOf_lt_of_mem ‹_ ∈ _›; omega) hqs
      have ih := args_congr rel
      constructor
      · intro h; cases h with
        | update ev op => exact .update ((ih _ _ _ _).mp ev) (by simpa only [Update.value_subst] using op)
      · intro h; cases h with
        | update ev op => exact .update ((ih _ _ _ _).mpr ev) (by simpa only [Update.value_subst] using op)
  | record head es =>
      simp only [expression, except_bind_ok, except_pure_ok] at expanded
      obtain ⟨qs, hqs, rfl⟩ := expanded
      have rel := children es (by intros; simp_wf; have := List.sizeOf_lt_of_mem ‹_ ∈ _›; omega) hqs
      have ih := args_congr rel
      have names : constructorName [] (head.subst types).type = constructorName types head.type := by
        simp only [RecordHead.subst, constructorName, Ty.subst_nil]
      constructor
      · intro h; cases h with
        | record ev =>
            simpa only [names, RecordHead.order_subst] using (OpenSource.EvalExpr.record (head := head.subst types) ((ih _ _ _ _).mp ev))
      · intro h; cases h with
        | record ev =>
            simpa only [names, RecordHead.order_subst] using (OpenSource.EvalExpr.record (head := head) ((ih _ _ _ _).mpr ev))
  | construct n ts ctor es =>
      simp only [expression, except_bind_ok, except_pure_ok] at expanded
      obtain ⟨qs, hqs, rfl⟩ := expanded
      have rel := children es (by intros; simp_wf; have := List.sizeOf_lt_of_mem ‹_ ∈ _›; omega) hqs
      have ih := args_congr rel
      have names : instanceName [] n (some ((ts.getD []).map (Ty.subst types))) = instanceName types n ts := by
        simp only [instanceName, Option.getD_some, List.map_map, Function.comp_def, Ty.subst_nil]
      constructor
      · intro h; cases h with
        | construct ev =>
            simpa only [names] using (OpenSource.EvalExpr.construct (name := n) (args := some ((ts.getD []).map (Ty.subst types)))
              (ctor := ctor) ((ih _ _ _ _).mp ev))
      · intro h; cases h with
        | construct ev =>
            simpa only [names] using (OpenSource.EvalExpr.construct (name := n) (args := ts)
              (ctor := ctor) ((ih _ _ _ _).mpr ev))
  | member e field =>
      simp only [expression, except_bind_ok, except_pure_ok] at expanded
      obtain ⟨q, hq, rfl⟩ := expanded
      have ih := sub depth types e (by apply Prod.Lex.right; simp_wf; omega) hq
      constructor
      · intro h; cases h with
        | member ev op => exact .member ((ih _ _ _ _).mp ev) (by simpa only [memberValue_subst] using op)
      · intro h; cases h with
        | member ev op => exact .member ((ih _ _ _ _).mpr ev) (by simpa only [memberValue_subst] using op)
  | «repeat» e n | index e i | project e i | slice e start stop | store e | load e | hint t e channel | neg e =>
      simp only [expression, except_bind_ok, except_pure_ok] at expanded
      obtain ⟨q, hq, rfl⟩ := expanded
      have ih := sub depth types e (by apply Prod.Lex.right; simp_wf <;> omega) hq
      constructor
      · intro h; cases h
        first
          | exact .repeat ((ih _ _ _ _).mp ‹_›)
          | exact .store ((ih _ _ _ _).mp ‹_›)
          | exact .index ((ih _ _ _ _).mp ‹_›) ‹_›
          | exact .project ((ih _ _ _ _).mp ‹_›) ‹_›
          | exact .slice ((ih _ _ _ _).mp ‹_›) ‹_›
          | exact .load ((ih _ _ _ _).mp ‹_›) ‹_›
          | exact .neg ((ih _ _ _ _).mp ‹_›) ‹_›
          | exact .hint ((ih _ _ _ _).mp ‹_›) (by simpa using ‹world.typed _ _ = true›)
      · intro h; cases h
        first
          | exact .repeat ((ih _ _ _ _).mpr ‹_›)
          | exact .store ((ih _ _ _ _).mpr ‹_›)
          | exact .index ((ih _ _ _ _).mpr ‹_›) ‹_›
          | exact .project ((ih _ _ _ _).mpr ‹_›) ‹_›
          | exact .slice ((ih _ _ _ _).mpr ‹_›) ‹_›
          | exact .load ((ih _ _ _ _).mpr ‹_›) ‹_›
          | exact .neg ((ih _ _ _ _).mpr ‹_›) ‹_›
          | rename_i input value typed ev
            exact .hint ((ih _ _ _ _).mpr ev) (by simpa only [Ty.subst_nil] using typed)
  | binary op lhs rhs =>
      simp only [expression, except_bind_ok, except_pure_ok] at expanded
      obtain ⟨left, hl, right, hr, rfl⟩ := expanded
      have ihl := sub depth types lhs (by apply Prod.Lex.right; simp_wf; omega) hl
      have ihr := sub depth types rhs (by apply Prod.Lex.right; simp_wf; omega) hr
      constructor
      · intro h; cases h with
        | binary l r op => exact .binary ((ihl _ _ _ _).mp l) ((ihr _ _ _ _).mp r) op
      · intro h; cases h with
        | binary l r op => exact .binary ((ihl _ _ _ _).mpr l) ((ihr _ _ _ _).mpr r) op
  | letValue pat operand body =>
      simp only [expression, except_bind_ok, except_pure_ok] at expanded
      obtain ⟨qpat, hp, qvalue, hv, qbody, hb, rfl⟩ := expanded
      have ihv := sub depth types operand (by apply Prod.Lex.right; simp_wf; omega) hv
      have ihb := sub depth types body (by apply Prod.Lex.right; simp_wf; omega) hb
      constructor
      · intro h; cases h with
        | letValue ev matched branch =>
            exact .letValue ((ihv _ _ _ _).mp ev) (by rw [← patterns _ _ hp]; exact matched)
              ((ihb _ _ _ _).mp branch)
      · intro h; cases h with
        | letValue ev matched branch =>
            exact .letValue ((ihv _ _ _ _).mpr ev) (by rw [patterns _ _ hp]; exact matched)
              ((ihb _ _ _ _).mpr branch)
  | call n ts es =>
      simp only [expression, except_bind_ok, except_pure_ok] at expanded
      obtain ⟨qs, hqs, rfl⟩ := expanded
      have rel := children es (by intros; simp_wf; have := List.sizeOf_lt_of_mem ‹_ ∈ _›; omega) hqs
      have ih := args_congr rel
      have names : instanceName [] n (some ((ts.getD []).map (Ty.subst types))) = instanceName types n ts := by
        simp only [instanceName, Option.getD_some, List.map_map, Function.comp_def, Ty.subst_nil]
      constructor
      · intro h; cases h with
        | call args callee => exact .call ((ih _ _ _ _).mp args) (by simpa only [names] using callee)
      · intro h; cases h with
        | call args callee => exact .call ((ih _ _ _ _).mpr args) (by simpa only [names] using callee)
  | matchValue operand arms =>
      simp only [expression, except_bind_ok, except_pure_ok] at expanded
      obtain ⟨qvalue, hv, others, ho, rfl⟩ := expanded
      have ihv := sub depth types operand (by apply Prod.Lex.right; simp_wf; omega) hv
      let R := fun e q => ∀ ls b v a, OpenSource.EvalExpr world calls types ls e b v a ↔ OpenSource.EvalExpr world calls [] ls q b v a
      have rel : List.Forall₂ (fun a b =>
          (∀ heap value, world.matchPattern types heap a.1 value = world.matchPattern [] heap b.1 value) ∧
          R a.2 b.2) arms others := by
        have mapped := mapM_relation ho
        have withMem := (List.forall₂_and_left arms others).mpr ⟨fun _ h => h, mapped⟩
        apply withMem.imp
        intro a b h
        rcases a with ⟨pat, body⟩
        simp only [except_bind_ok, except_pure_ok] at h
        obtain ⟨ha, qpat, hp, qbody, hb, rfl⟩ := h
        refine ⟨patterns _ _ hp, sub depth types body ?_ hb⟩
        apply Prod.Lex.right
        have := List.sizeOf_lt_of_mem ha
        simp only [Expr.matchValue.sizeOf_spec, Prod.mk.sizeOf_spec] at *
        omega
      constructor
      · intro h; cases h with
        | matchValue ev selected branch =>
            obtain ⟨other, selected', bodyRel⟩ := select_transfer rel selected
            exact .matchValue ((ihv _ _ _ _).mp ev) selected' ((bodyRel _ _ _ _).mp branch)
      · intro h; cases h with
        | matchValue ev selected branch =>
            have reverse : List.Forall₂ (fun a b =>
                (∀ heap value, world.matchPattern [] heap a.1 value = world.matchPattern types heap b.1 value) ∧
                R b.2 a.2) others arms :=
              rel.flip.imp (fun a b h => ⟨fun heap value => (h.1 heap value).symm, h.2⟩)
            obtain ⟨other, selected', bodyRel⟩ := select_transfer (R := fun a b => R b a) reverse selected
            exact .matchValue ((ihv _ _ _ _).mpr ev) selected' ((bodyRel _ _ _ _).mpr branch)
termination_by (depth, sizeOf expr)
decreasing_by all_goals exact smaller

theorem exit_preparation_open_iff [Field F] [DecidableEq F]
    (program : Program F) (world : World F)
    (lookup : ∀ n t, world.constant n t = (elaborateConst program n t).mapError
      (fun _ => EvalError.unboundVariable ("::" ++ n)))
    (constDepth : world.constDepth = program.consts.length + 1)
    (depth : Nat) (types : Types) (expr : Expr F) {prepared : Expr F}
    (expanded : expression program depth types expr = .ok prepared)
    (locals before target result after) :
    OpenSource.EvalExit world calls types locals expr before target result after ↔
      OpenSource.EvalExit world calls [] locals prepared before target result after := by
  have sub (d ts e) (smaller : Prod.Lex (· < ·) (· < ·) (d, sizeOf e) (depth, sizeOf expr))
      {q : Expr F} (h : expression program d ts e = .ok q) (ls b target v a) :
      OpenSource.EvalExit world calls ts ls e b target v a ↔ OpenSource.EvalExit world calls [] ls q b target v a :=
    exit_preparation_open_iff program world lookup constDepth d ts e h ls b target v a
  have subNormal (d ts e) (smaller : Prod.Lex (· < ·) (· < ·) (d, sizeOf e) (depth, sizeOf expr))
      {q : Expr F} (h : expression program d ts e = .ok q) (ls b v a) :
      OpenSource.EvalExpr world calls ts ls e b v a ↔ OpenSource.EvalExpr world calls [] ls q b v a :=
    expression_preparation_open_iff program world lookup constDepth d ts e h ls b v a
  have children (es : List (Expr F)) (smaller : ∀ e ∈ es, sizeOf e < sizeOf expr)
      {qs : List (Expr F)} (mapped : es.mapM (expression program depth types) = .ok qs) :
      List.Forall₂ (fun e q =>
        (∀ ls b v a, OpenSource.EvalExpr world calls types ls e b v a ↔ OpenSource.EvalExpr world calls [] ls q b v a) ∧
        (∀ ls b t v a, OpenSource.EvalExit world calls types ls e b t v a ↔ OpenSource.EvalExit world calls [] ls q b t v a)) es qs := by
    have rel := mapM_relation mapped
    have both : List.Forall₂ (fun e q => e ∈ es ∧ expression program depth types e = .ok q) es qs :=
      (List.forall₂_and_left _ _).mpr ⟨fun _ h => h, rel⟩
    exact both.imp (fun e q h => ⟨subNormal depth types e (Prod.Lex.right _ (smaller e h.1)) h.2,
      sub depth types e (Prod.Lex.right _ (smaller e h.1)) h.2⟩)
  have patterns (pat q : Pattern F) (h : pattern program (program.consts.length + 1) types pat = .ok q)
      (heap value) : world.matchPattern types heap pat value = world.matchPattern [] heap q value := by
    simp only [World.matchPattern, constDepth]
    exact pattern_match program world.constant lookup _ _ _ h world.constant _ heap value
  cases expr with
  | literal | var =>
      simp only [expression, except_pure_ok] at expanded
      subst prepared
      constructor <;> intro h <;> cases h
  | global =>
      constructor
      · intro h; exact (h.hasControl (by simp [ControlLower.hasControl])).elim
      · intro h; exact (h.hasControl (expression_closed program depth types _ .global expanded).noControl).elim
  | control kind e =>
      simp only [expression, except_bind_ok, except_pure_ok] at expanded
      obtain ⟨q, hq, rfl⟩ := expanded
      have ihn := subNormal depth types e (by apply Prod.Lex.right; simp_wf; omega) hq
      have ihe := sub depth types e (by apply Prod.Lex.right; simp_wf; omega) hq
      cases kind with
      | block label =>
          constructor
          · intro h; cases h with | fromBlock ne ev => exact .fromBlock ne ((ihe _ _ _ _ _).mp ev)
          · intro h; cases h with | fromBlock ne ev => exact .fromBlock ne ((ihe _ _ _ _ _).mpr ev)
      | exit target =>
          constructor
          · intro h; cases h with
            | exit ev => exact .exit ((ihn _ _ _ _).mp ev)
            | exitPayload ev => exact .exitPayload ((ihe _ _ _ _ _).mp ev)
          · intro h; cases h with
            | exit ev => exact .exit ((ihn _ _ _ _).mpr ev)
            | exitPayload ev => exact .exitPayload ((ihe _ _ _ _ _).mpr ev)
  | builtin _ es | update _ es | record _ es | tuple es | array es | construct _ _ _ es | constructAs _ _ _ es | call _ _ es =>
      simp only [expression, except_bind_ok, except_pure_ok] at expanded
      obtain ⟨qs, hqs, rfl⟩ := expanded
      have ih := args_exit_congr (children es (by intros; simp_wf; have := List.sizeOf_lt_of_mem ‹_ ∈ _›; omega) hqs)
      constructor
      · intro h; cases h
        first
          | exact .fromTuple ((ih _ _ _ _ _).mp ‹_›)
          | exact .fromArray ((ih _ _ _ _ _).mp ‹_›)
          | exact .fromConstruct ((ih _ _ _ _ _).mp ‹_›)
          | exact .fromBuiltin ((ih _ _ _ _ _).mp ‹_›)
          | exact .fromUpdate ((ih _ _ _ _ _).mp ‹_›)
          | exact .fromRecord ((ih _ _ _ _ _).mp ‹_›)
          | exact .fromConstructAs ((ih _ _ _ _ _).mp ‹_›)
          | exact .fromCall ((ih _ _ _ _ _).mp ‹_›)
      · intro h; cases h
        first
          | exact .fromTuple ((ih _ _ _ _ _).mpr ‹_›)
          | exact .fromArray ((ih _ _ _ _ _).mpr ‹_›)
          | exact .fromConstruct ((ih _ _ _ _ _).mpr ‹_›)
          | exact .fromBuiltin ((ih _ _ _ _ _).mpr ‹_›)
          | exact .fromUpdate ((ih _ _ _ _ _).mpr ‹_›)
          | exact .fromRecord ((ih _ _ _ _ _).mpr ‹_›)
          | exact .fromConstructAs ((ih _ _ _ _ _).mpr ‹_›)
          | exact .fromCall ((ih _ _ _ _ _).mpr ‹_›)
  | member e field | «repeat» e n | index e i | project e i | slice e start stop | store e | load e | hint t e channel | neg e =>
      simp only [expression, except_bind_ok, except_pure_ok] at expanded
      obtain ⟨q, hq, rfl⟩ := expanded
      have ih := sub depth types e (by apply Prod.Lex.right; simp_wf <;> omega) hq
      constructor
      · intro h; cases h
        first
          | exact .fromRepeat ((ih _ _ _ _ _).mp ‹_›)
          | exact .fromIndex ((ih _ _ _ _ _).mp ‹_›)
          | exact .fromMember ((ih _ _ _ _ _).mp ‹_›)
          | exact .fromProject ((ih _ _ _ _ _).mp ‹_›)
          | exact .fromSlice ((ih _ _ _ _ _).mp ‹_›)
          | exact .fromStore ((ih _ _ _ _ _).mp ‹_›)
          | exact .fromLoad ((ih _ _ _ _ _).mp ‹_›)
          | exact .fromHint ((ih _ _ _ _ _).mp ‹_›)
          | exact .fromNeg ((ih _ _ _ _ _).mp ‹_›)
      · intro h; cases h
        first
          | exact .fromRepeat ((ih _ _ _ _ _).mpr ‹_›)
          | exact .fromIndex ((ih _ _ _ _ _).mpr ‹_›)
          | exact .fromMember ((ih _ _ _ _ _).mpr ‹_›)
          | exact .fromProject ((ih _ _ _ _ _).mpr ‹_›)
          | exact .fromSlice ((ih _ _ _ _ _).mpr ‹_›)
          | exact .fromStore ((ih _ _ _ _ _).mpr ‹_›)
          | exact .fromLoad ((ih _ _ _ _ _).mpr ‹_›)
          | exact .fromHint ((ih _ _ _ _ _).mpr ‹_›)
          | exact .fromNeg ((ih _ _ _ _ _).mpr ‹_›)
  | binary op lhs rhs =>
      simp only [expression, except_bind_ok, except_pure_ok] at expanded
      obtain ⟨left, hl, right, hr, rfl⟩ := expanded
      have ihl := sub depth types lhs (by apply Prod.Lex.right; simp_wf; omega) hl
      have ihn := subNormal depth types lhs (by apply Prod.Lex.right; simp_wf; omega) hl
      have ihr := sub depth types rhs (by apply Prod.Lex.right; simp_wf; omega) hr
      constructor
      · intro h; cases h with
        | binaryLeft ev => exact .binaryLeft ((ihl _ _ _ _ _).mp ev)
        | binaryRight l r => exact .binaryRight ((ihn _ _ _ _).mp l) ((ihr _ _ _ _ _).mp r)
      · intro h; cases h with
        | binaryLeft ev => exact .binaryLeft ((ihl _ _ _ _ _).mpr ev)
        | binaryRight l r => exact .binaryRight ((ihn _ _ _ _).mpr l) ((ihr _ _ _ _ _).mpr r)
  | letValue pat operand body =>
      simp only [expression, except_bind_ok, except_pure_ok] at expanded
      obtain ⟨qpat, hp, qvalue, hv, qbody, hb, rfl⟩ := expanded
      have ihv := sub depth types operand (by apply Prod.Lex.right; simp_wf; omega) hv
      have ihn := subNormal depth types operand (by apply Prod.Lex.right; simp_wf; omega) hv
      have ihb := sub depth types body (by apply Prod.Lex.right; simp_wf; omega) hb
      constructor
      · intro h; cases h with
        | fromLetValue ev => exact .fromLetValue ((ihv _ _ _ _ _).mp ev)
        | letBody ev matched branch =>
            exact .letBody ((ihn _ _ _ _).mp ev) (by rw [← patterns _ _ hp]; exact matched)
              ((ihb _ _ _ _ _).mp branch)
      · intro h; cases h with
        | fromLetValue ev => exact .fromLetValue ((ihv _ _ _ _ _).mpr ev)
        | letBody ev matched branch =>
            exact .letBody ((ihn _ _ _ _).mpr ev) (by rw [patterns _ _ hp]; exact matched)
              ((ihb _ _ _ _ _).mpr branch)
  | matchValue operand arms =>
      simp only [expression, except_bind_ok, except_pure_ok] at expanded
      obtain ⟨qvalue, hv, others, ho, rfl⟩ := expanded
      have ihv := sub depth types operand (by apply Prod.Lex.right; simp_wf; omega) hv
      have ihn := subNormal depth types operand (by apply Prod.Lex.right; simp_wf; omega) hv
      let R := fun e q => ∀ ls b t v a, OpenSource.EvalExit world calls types ls e b t v a ↔ OpenSource.EvalExit world calls [] ls q b t v a
      have rel : List.Forall₂ (fun a b =>
          (∀ heap value, world.matchPattern types heap a.1 value = world.matchPattern [] heap b.1 value) ∧
          R a.2 b.2) arms others := by
        have mapped := mapM_relation ho
        have withMem := (List.forall₂_and_left arms others).mpr ⟨fun _ h => h, mapped⟩
        apply withMem.imp
        intro a b h
        rcases a with ⟨pat, body⟩
        simp only [except_bind_ok, except_pure_ok] at h
        obtain ⟨ha, qpat, hp, qbody, hb, rfl⟩ := h
        refine ⟨patterns _ _ hp, sub depth types body ?_ hb⟩
        apply Prod.Lex.right
        have := List.sizeOf_lt_of_mem ha
        simp only [Expr.matchValue.sizeOf_spec, Prod.mk.sizeOf_spec] at *
        omega
      constructor
      · intro h; cases h with
        | fromMatchValue ev => exact .fromMatchValue ((ihv _ _ _ _ _).mp ev)
        | matchBody ev selected branch =>
            obtain ⟨other, selected', bodyRel⟩ := select_transfer rel selected
            exact .matchBody ((ihn _ _ _ _).mp ev) selected' ((bodyRel _ _ _ _ _).mp branch)
      · intro h; cases h with
        | fromMatchValue ev => exact .fromMatchValue ((ihv _ _ _ _ _).mpr ev)
        | matchBody ev selected branch =>
            have reverse : List.Forall₂ (fun a b =>
                (∀ heap value, world.matchPattern [] heap a.1 value = world.matchPattern types heap b.1 value) ∧
                R b.2 a.2) others arms :=
              rel.flip.imp (fun a b h => ⟨fun heap value => (h.1 heap value).symm, h.2⟩)
            obtain ⟨other, selected', bodyRel⟩ := select_transfer (R := fun a b => R b a) reverse selected
            exact .matchBody ((ihn _ _ _ _).mpr ev) selected' ((bodyRel _ _ _ _ _).mpr branch)
termination_by (depth, sizeOf expr)
decreasing_by all_goals exact smaller
end

theorem expression_preparation_iff [Field F] [DecidableEq F]
    (program : Program F) (world : World F)
    (lookup : ∀ n t, world.constant n t = (elaborateConst program n t).mapError
      (fun _ => EvalError.unboundVariable ("::" ++ n)))
    (constDepth : world.constDepth = program.consts.length + 1)
    (depth : Nat) (types : Types) (expr : Expr F) {prepared : Expr F}
    (expanded : expression program depth types expr = .ok prepared)
    (locals before result after) :
    EvalExpr world types locals expr before result after ↔
      EvalExpr world [] locals prepared before result after := by
  simpa only [OpenSource.closed_iff] using expression_preparation_open_iff
    (calls := EvalFn world) program world lookup constDepth depth types expr expanded locals before result after

end Aiur.Generic.SourceSemantics
