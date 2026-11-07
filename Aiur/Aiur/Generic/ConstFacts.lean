import Aiur.Generic.Consts
import Aiur.ExceptFacts

namespace Aiur.Generic
namespace Consts

set_option linter.unusedSimpArgs false

private theorem except_map_eq (f : α → β) (x : Except String α) : x.map f = f <$> x := rfl

private theorem traverse_map (xs : List α) (input : α → β) (output : γ → δ)
    (left : α → Except String γ) (right : β → Except String δ)
    (agree : ∀ x ∈ xs, right (input x) = (left x).map output) :
    (xs.map input).mapM right = (xs.mapM left).map (List.map output) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.map_cons, List.mapM_cons]
      rw [agree x (by simp), ih (fun y hy => agree y (by simp [hy]))]
      cases left x <;> cases xs.mapM left <;> rfl

private theorem traverse_same (xs : List α) (input : α → β)
    (left : α → Except String γ) (right : β → Except String γ)
    (agree : ∀ x ∈ xs, right (input x) = left x) :
    (xs.map input).mapM right = xs.mapM left := by
  simpa using traverse_map xs input id left right (by simpa using agree)

theorem checkBody_map (f : α → β) (pat : Pattern α) : checkBody (pat.map f) = checkBody pat := by
  have sub (p : Pattern α) (hsize : sizeOf p < sizeOf pat) : checkBody (p.map f) = checkBody p :=
    checkBody_map f p
  have children (ps : List (Pattern α)) (h : ∀ q ∈ ps, sizeOf q < sizeOf pat) :
      (ps.map (Pattern.map f)).mapM checkBody = ps.mapM checkBody :=
    traverse_same ps _ _ _ (fun q hq => checkBody_map f q)
  cases pat <;> simp only [Pattern.map, checkBody]
  all_goals try rw [children _ (by intros; simp_wf; have := List.sizeOf_lt_of_mem ‹_ ∈ _›; omega)]
  all_goals exact sub _ (by simp_wf <;> omega)
termination_by sizeOf pat
decreasing_by all_goals first | exact h q hq | exact hsize

theorem substitute_map (f : α → β) (pat : Pattern α)
    (left : String → Except String (Pattern α)) (right : String → Except String (Pattern β))
    (agree : ∀ n, right n = (left n).map (Pattern.map f)) :
    substitute right (pat.map f) = (substitute left pat).map (Pattern.map f) := by
  have sub (p : Pattern α) (hsize : sizeOf p < sizeOf pat) :
      substitute right (p.map f) = (substitute left p).map (Pattern.map f) :=
    substitute_map f p left right agree
  have children (ps : List (Pattern α)) (h : ∀ q ∈ ps, sizeOf q < sizeOf pat) :
      (ps.map (Pattern.map f)).mapM (substitute right) =
        (ps.mapM (substitute left)).map (List.map (Pattern.map f)) :=
    traverse_map ps _ _ _ _ (fun q hq => substitute_map f q left right agree)
  cases pat with
  | global n ann => simpa only [Pattern.map, substitute] using agree n
  | literal | wildcard | bind => simp [Pattern.map, substitute, Except.map, pure, Except.pure]
  | orElse a b names =>
      simp only [Pattern.map, substitute, sub a (by simp_wf; omega), sub b (by simp_wf; omega)]
      cases substitute left a <;> cases substitute left b <;> simp [Except.map, bind, Except.bind, pure, Except.pure, Pattern.map]
  | load p | «repeat» p _ =>
      simp only [Pattern.map, substitute, sub p (by simp_wf <;> omega)]
      simp [except_map_eq, bind_map_left, _root_.map_bind, Functor.map_map, Pattern.map]
  | record _ ps | tuple ps | array ps | construct _ _ ps | constructAs _ _ _ ps =>
      simp only [Pattern.map, substitute]
      rw [children ps (by intros; simp_wf; have := List.sizeOf_lt_of_mem ‹_ ∈ _›; omega)]
      simp [except_map_eq, bind_map_left, _root_.map_bind, Functor.map_map, Pattern.map]
termination_by sizeOf pat
decreasing_by all_goals first | exact h q hq | exact hsize

theorem lookup_map (f : α → β) (decls : List (ConstDecl α)) (name : String) :
    lookup (decls.map (ConstDecl.map f)) name = (lookup decls name).map (Pattern.map f) := by
  simp only [lookup, List.find?_map, Function.comp_def]
  have same : (fun d : ConstDecl α => (d.map f).name == name) = (fun d => d.name == name) := rfl
  rw [same]
  cases decls.find? (·.name == name) <;> rfl

theorem resolve_map (f : α → β) (decls : List (ConstDecl α)) (fuel path name) :
    resolve (decls.map (ConstDecl.map f)) fuel path name =
      (resolve decls fuel path name).map (Pattern.map f) := by
  induction fuel generalizing path name with
  | zero => rfl
  | succ fuel ih =>
      simp only [resolve, lookup_map]
      by_cases cycle : path.contains name
      · simp only [cycle, ↓reduceIte]; rfl
      · simp only [cycle, Bool.false_eq_true, ↓reduceIte, pure_bind]
        cases found : lookup decls name with
        | error e => rfl
        | ok pat =>
            simpa only [Except.map, bind, Except.bind, pure, Except.pure] using
              substitute_map f pat (resolve decls fuel (name :: path))
                (resolve (decls.map (ConstDecl.map f)) fuel (name :: path)) (fun n => ih _ n)

theorem checkDeclarations_map (f : α → β) (p : Program α) :
    checkDeclarations (p.map f) = checkDeclarations p := by
  have checked := traverse_same p.consts (ConstDecl.map f)
    (checkDeclaration (p.functions.map (·.name) ++ p.maps.map (·.name)))
    (checkDeclaration (p.functions.map (·.name) ++ p.maps.map (·.name)))
    (fun d _ => by simp [checkDeclaration, ConstDecl.map, checkBody_map])
  simp only [checkDeclarations, Program.map, List.map_map, Function.comp_def]
  have names : (fun d : ConstDecl α => (d.map f).name) = (fun d => d.name) := rfl
  rw [names, checked]

theorem resolveDeclarations_map (f : α → β) (p : Program α) :
    resolveDeclarations (p.map f) = (resolveDeclarations p).map (List.map (ConstDecl.map f)) := by
  have resolved := traverse_map p.consts (ConstDecl.map f) (ConstDecl.map f)
    (fun d => do return { d with value := ← resolve p.consts (p.consts.length + 1) [] d.name })
    (fun d => do return { d with value := ← resolve (p.consts.map (ConstDecl.map f)) (p.consts.length + 1) [] d.name })
    (by
      intro d _
      simp [ConstDecl.map, resolve_map, except_map_eq, bind_map_left, _root_.map_bind, Functor.map_map])
  simp only [resolveDeclarations]
  rw [checkDeclarations_map]
  simp only [Program.map, List.length_map, resolved]
  simp [except_map_eq, bind_map_left, _root_.map_bind, Functor.map_map]

theorem toExpr_map (f : α → β) (pat : Pattern α) :
    toExpr (pat.map f) = (toExpr pat).map (Expr.map f) := by
  have sub (p : Pattern α) (hsize : sizeOf p < sizeOf pat) :
      toExpr (p.map f) = (toExpr p).map (Expr.map f) := toExpr_map f p
  have children (ps : List (Pattern α)) (h : ∀ q ∈ ps, sizeOf q < sizeOf pat) :
      (ps.map (Pattern.map f)).mapM toExpr = (ps.mapM toExpr).map (List.map (Expr.map f)) :=
    traverse_map ps _ _ _ _ (fun q hq => toExpr_map f q)
  cases pat with
  | literal | wildcard | bind | global | orElse =>
      simp [Pattern.map, toExpr, Expr.map, Except.map, pure, Except.pure]
  | load p | «repeat» p _ =>
      simp only [Pattern.map, toExpr, sub p (by simp_wf <;> omega)]
      simp [except_map_eq, bind_map_left, _root_.map_bind, Functor.map_map, Expr.map]
  | record _ ps | tuple ps | array ps | constructAs _ _ _ ps =>
      simp only [Pattern.map, toExpr]
      rw [children ps (by intros; simp_wf; have := List.sizeOf_lt_of_mem ‹_ ∈ _›; omega)]
      simp [except_map_eq, bind_map_left, _root_.map_bind, Functor.map_map, Expr.map]
  | construct t c ps =>
      cases t <;> simp only [Pattern.map, toExpr]
      all_goals first | rfl | skip
      rw [children ps (by intros; simp_wf; have := List.sizeOf_lt_of_mem ‹_ ∈ _›; omega)]
      simp [except_map_eq, bind_map_left, _root_.map_bind, Functor.map_map, Expr.map]
termination_by sizeOf pat
decreasing_by all_goals first | exact h q hq | exact hsize

theorem bindingNames_map (f : α → β) (pat : Pattern α) :
    (pat.map f).bindingNames = pat.bindingNames := by
  cases pat with
  | literal | wildcard | bind | global | orElse => simp [Pattern.map, Pattern.bindingNames]
  | load p => simpa only [Pattern.map, Pattern.bindingNames] using bindingNames_map f p
  | «repeat» p n => simp only [Pattern.map, Pattern.bindingNames, bindingNames_map f p]
  | record head ps =>
      simp only [Pattern.map, Pattern.bindingNames, List.map_map]
      congr 2
      apply List.map_congr_left
      intro p member
      exact bindingNames_map f p
  | tuple ps | array ps | construct _ _ ps | constructAs _ _ _ ps =>
      simp only [Pattern.map, Pattern.bindingNames, List.flatMap_map]
      apply List.flatMap_congr
      intro p member
      exact bindingNames_map f p
termination_by sizeOf pat
decreasing_by
  all_goals simp_wf
  all_goals try have := List.sizeOf_lt_of_mem member
  all_goals omega

theorem expandPattern_map (f : α → β) (decls : List (ConstDecl α)) (pat : Pattern α) :
    expandPattern (decls.map (ConstDecl.map f)) (pat.map f) =
      (expandPattern decls pat).map (Pattern.map f) :=
  substitute_map f pat _ _ (lookup_map f decls)

theorem expression_map (f : α → β) (decls : List (ConstDecl α)) (name : String) :
    expression (decls.map (ConstDecl.map f)) name = (expression decls name).map (Expr.map f) := by
  simp only [expression, lookup_map]
  cases lookup decls name with
  | error e => rfl
  | ok pat => exact toExpr_map f pat

theorem expandExpr_map (f : α → β) (decls : List (ConstDecl α)) (locals) (expr : Expr α) :
    expandExpr (decls.map (ConstDecl.map f)) locals (expr.map f) =
      (expandExpr decls locals expr).map (Expr.map f) := by
  have sub (x : Expr α) (hsize : sizeOf x < sizeOf expr) (locals) :
      expandExpr (decls.map (ConstDecl.map f)) locals (x.map f) =
        (expandExpr decls locals x).map (Expr.map f) :=
    expandExpr_map f decls locals x
  have children (xs : List (Expr α)) (h : ∀ x ∈ xs, sizeOf x < sizeOf expr) :
      (xs.map (Expr.map f)).mapM (expandExpr (decls.map (ConstDecl.map f)) locals) =
        (xs.mapM (expandExpr decls locals)).map (List.map (Expr.map f)) :=
    traverse_map xs _ _ _ _ (fun x hx => expandExpr_map f decls locals x)
  cases expr with
  | literal => simp [Expr.map, expandExpr, Except.map, pure, Except.pure]
  | var n =>
      simp only [Expr.map, expandExpr, List.any_map, Function.comp_def, ConstDecl.map]
      split <;> simp [expression_map, Except.map, pure, Except.pure, Expr.map]
  | global n ann => simpa only [Expr.map, expandExpr] using expression_map f decls n
  | builtin _ xs | update _ xs | record _ xs | tuple xs | array xs | construct _ _ _ xs | constructAs _ _ _ xs | call _ _ xs =>
      simp only [Expr.map, expandExpr]
      rw [children xs (by intros; simp_wf; have := List.sizeOf_lt_of_mem ‹_ ∈ _›; omega)]
      all_goals simp [except_map_eq, bind_map_left, _root_.map_bind, Functor.map_map, Expr.map]
  | member x _ | control _ x | project x _ | index x _ | slice x _ _ | «repeat» x _ | store x | load x | hint _ x channel | neg x =>
      simp only [Expr.map, expandExpr, sub x (by simp_wf <;> omega)]
      all_goals simp [except_map_eq, bind_map_left, _root_.map_bind, Functor.map_map, Expr.map]
  | binary _ x b =>
      simp only [Expr.map, expandExpr, sub x (by simp_wf <;> omega), sub b (by simp_wf <;> omega)]
      simp [except_map_eq, bind_map_left, _root_.map_bind, Functor.map_map, Expr.map]
  | letValue pat x b =>
      simp only [Expr.map, expandExpr, expandPattern_map]
      cases expandPattern decls pat with
      | error e => rfl
      | ok pat =>
          simp only [Except.map, bind, Except.bind, bindingNames_map,
            sub x (by simp_wf <;> omega), sub b (by simp_wf <;> omega)]
          cases expandExpr decls locals x <;> cases expandExpr decls (pat.bindingNames ++ locals) b <;>
            simp [Except.map, bind, Except.bind, pure, Except.pure, Expr.map]
  | matchValue x arms =>
      have mapped := traverse_map arms
        (fun arm => (arm.1.map f, arm.2.map f))
        (fun arm : Pattern α × Expr α => (arm.1.map f, arm.2.map f))
        (fun arm => do
          let pat ← expandPattern decls arm.1
          return (pat, ← expandExpr decls (pat.bindingNames ++ locals) arm.2))
        (fun arm => do
          let pat ← expandPattern (decls.map (ConstDecl.map f)) arm.1
          return (pat, ← expandExpr (decls.map (ConstDecl.map f)) (pat.bindingNames ++ locals) arm.2))
        (by
          intro arm member
          simp only [expandPattern_map]
          cases expandPattern decls arm.1 with
          | error e => rfl
          | ok pat =>
              simp only [Except.map, bind, Except.bind, bindingNames_map,
                sub arm.2 (by have := List.sizeOf_lt_of_mem member; cases arm; simp_all [Prod.mk.sizeOf_spec]; omega)]
              cases expandExpr decls (pat.bindingNames ++ locals) arm.2 <;>
                simp [Except.map, bind, Except.bind, pure, Except.pure])
      simp only [Expr.map, expandExpr, sub x (by simp_wf <;> omega), mapped]
      simp [except_map_eq, bind_map_left, _root_.map_bind, Functor.map_map, Expr.map]
termination_by sizeOf expr
decreasing_by all_goals first | exact h x hx | exact hsize

theorem expandProgram_map (f : α → β) (decls : List (ConstDecl α)) (p : Program α) :
    expandProgram (decls.map (ConstDecl.map f)) (p.map f) =
      (expandProgram decls p).map (Program.map f) := by
  have functions := traverse_map p.functions
    (fun d => { d with body := d.body.map f }) (fun d => { d with body := d.body.map f })
    (fun d => do return { d with body := ← expandExpr decls (d.params.map Prod.fst) d.body })
    (fun d => do return { d with body := ← expandExpr (decls.map (ConstDecl.map f)) (d.params.map Prod.fst) d.body })
    (by
      intro d _
      simp [expandExpr_map, except_map_eq, bind_map_left, _root_.map_bind, Functor.map_map])
  have tables := traverse_map p.tables
    (fun t => { t with rows := t.rows.map (Expr.map f) }) (fun t => { t with rows := t.rows.map (Expr.map f) })
    (fun t => do return { t with rows := ← t.rows.mapM (expandExpr decls []) })
    (fun t => do return { t with rows := ← t.rows.mapM (expandExpr (decls.map (ConstDecl.map f)) []) })
    (by
      intro t _
      have rows := traverse_map t.rows (Expr.map f) (Expr.map f)
        (expandExpr decls []) (expandExpr (decls.map (ConstDecl.map f)) [])
        (fun x _ => expandExpr_map f decls [] x)
      simp only [rows]
      simp [except_map_eq, bind_map_left, _root_.map_bind, Functor.map_map])
  simp only [expandProgram, Program.map, functions, tables]
  simp [except_map_eq, bind_map_left, _root_.map_bind, Functor.map_map, Program.map]

end Consts

/-- Literal conversion commutes with const resolution and substitution,
including every scope decision and expansion error. -/
theorem expandConsts_map (f : α → β) (p : Program α) :
    expandConsts (p.map f) = (expandConsts p).map (Program.map f) := by
  simp only [expandConsts, Consts.resolveDeclarations_map]
  cases Consts.resolveDeclarations p with
  | error e => rfl
  | ok decls => exact Consts.expandProgram_map f decls p

theorem expandConsts_toField (p : Program Nat) (F : Type) [NatCast F] :
    expandConsts (p.toField F) = (expandConsts p).map (fun q => q.toField F) :=
  expandConsts_map Nat.cast p

end Aiur.Generic
