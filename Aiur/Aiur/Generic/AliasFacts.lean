import Aiur.Generic.Aliases

namespace Aiur.Generic
namespace Aliases

set_option linter.unusedSimpArgs false

private theorem map_pure (x : α) (f : α → β) :
    (pure x : Except String α).map f = pure (f x) := rfl

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

theorem checkPatternTypes_map (enums aliases rigid) (f : α → β) (pat : Pattern α) :
    checkPatternTypes enums aliases rigid (pat.map f) = checkPatternTypes enums aliases rigid pat := by
  have sub (p : Pattern α) (hsize : sizeOf p < sizeOf pat) :
      checkPatternTypes enums aliases rigid (p.map f) = checkPatternTypes enums aliases rigid p :=
    checkPatternTypes_map enums aliases rigid f p
  have children (ps : List (Pattern α)) (h : ∀ q ∈ ps, sizeOf q < sizeOf pat) :
      (ps.map (Pattern.map f)).mapM (checkPatternTypes enums aliases rigid) =
        ps.mapM (checkPatternTypes enums aliases rigid) :=
    traverse_same ps _ _ _ (fun q hq => checkPatternTypes_map enums aliases rigid f q)
  cases pat <;> simp only [Pattern.map, checkPatternTypes]
  all_goals try rw [children _ (by intros; simp_all only [Pattern.tuple.sizeOf_spec, Pattern.array.sizeOf_spec,
    Pattern.record.sizeOf_spec, Pattern.construct.sizeOf_spec, Pattern.constructAs.sizeOf_spec]; have := List.sizeOf_lt_of_mem ‹_ ∈ _›; omega)]
  all_goals first
    | exact sub _ (by simp_wf <;> omega)
    | rw [sub _ (by simp_wf; omega), sub _ (by simp_wf; omega)]
termination_by sizeOf pat
decreasing_by all_goals first | exact h q hq | exact hsize

theorem expandPattern_map (aliases) (f : α → β) (pat : Pattern α) :
    expandPattern aliases (pat.map f) = (expandPattern aliases pat).map (Pattern.map f) := by
  have sub (p : Pattern α) (hsize : sizeOf p < sizeOf pat) :
      expandPattern aliases (p.map f) = (expandPattern aliases p).map (Pattern.map f) :=
    expandPattern_map aliases f p
  have children (ps : List (Pattern α)) (h : ∀ q ∈ ps, sizeOf q < sizeOf pat) :
      (ps.map (Pattern.map f)).mapM (expandPattern aliases) =
        (ps.mapM (expandPattern aliases)).map (List.map (Pattern.map f)) :=
    traverse_map ps _ _ _ _ (fun q hq => expandPattern_map aliases f q)
  cases pat with
  | literal | wildcard | bind | global => simp [Pattern.map, expandPattern, map_pure]
  | orElse left right names =>
      simp only [Pattern.map, expandPattern, sub left (by simp_wf; omega), sub right (by simp_wf; omega)]
      cases expandPattern aliases left <;> cases expandPattern aliases right <;> simp [Except.map, bind, Except.bind, pure, Except.pure, Pattern.map]
  | load p | «repeat» p _ =>
      simp only [Pattern.map, expandPattern, sub p (by simp_wf <;> omega)]
      simp [except_map_eq, bind_map_left, _root_.map_bind, Functor.map_map, Pattern.map]
  | record head ps =>
      simp only [Pattern.map, expandPattern]
      rw [children ps (by intros; simp_wf; have := List.sizeOf_lt_of_mem ‹_ ∈ _›; omega)]
      simp [except_map_eq, bind_map_left, _root_.map_bind, Functor.map_map, Pattern.map]
  | tuple ps | array ps =>
      simp only [Pattern.map, expandPattern]
      rw [children ps (by intros; simp_wf; have := List.sizeOf_lt_of_mem ‹_ ∈ _›; omega)]
      cases ps.mapM (expandPattern aliases) <;>
        simp [Except.map, bind, Except.bind, pure, Except.pure, Pattern.map]
  | construct t c ps =>
      simp only [Pattern.map, expandPattern]
      rw [children ps (by intros; simp only [Pattern.construct.sizeOf_spec]; have := List.sizeOf_lt_of_mem ‹_ ∈ _›; omega)]
      cases ps.mapM (expandPattern aliases) <;> simp only [Except.map, bind, Except.bind]
      cases t with
      | field => cases expandType aliases .field <;> simp [pure, Except.pure, Except.map, bind, Except.bind, Pattern.map]
      | tuple ts => cases expandType aliases (.tuple ts) <;> simp [pure, Except.pure, Except.map, bind, Except.bind, Pattern.map]
      | array t n => cases expandType aliases (.array t n) <;> simp [pure, Except.pure, Except.map, bind, Except.bind, Pattern.map]
      | ptr t => cases expandType aliases (.ptr t) <;> simp [pure, Except.pure, Except.map, bind, Except.bind, Pattern.map]
      | param n => cases expandType aliases (.param n) <;> simp [pure, Except.pure, Except.map, bind, Except.bind, Pattern.map]
      | named n ts =>
          cases found : aliases.find? (·.name == n) with
          | none =>
              cases expandType aliases (.named n ts) <;>
                simp [found, pure, Except.pure, Except.map, bind, Except.bind, Pattern.map]
          | some d =>
              cases resolved : constructorType aliases d (if ts.isEmpty then none else some ts) <;>
                simp only [found, resolved, pure, Except.pure, Except.map, bind, Except.bind, Pattern.map]
  | constructAs params t c ps =>
      simp only [Pattern.map, expandPattern]
      rw [children ps (by intros; simp only [Pattern.constructAs.sizeOf_spec]; have := List.sizeOf_lt_of_mem ‹_ ∈ _›; omega)]
      cases expandType aliases t <;> cases ps.mapM (expandPattern aliases) <;>
        simp [Except.map, bind, Except.bind, pure, Except.pure, Pattern.map]
termination_by sizeOf pat
decreasing_by all_goals first | exact h q hq | exact hsize

theorem checkExprTypes_map (enums aliases rigid) (f : α → β) (expr : Expr α) :
    checkExprTypes enums aliases rigid (expr.map f) = checkExprTypes enums aliases rigid expr := by
  have sub (x : Expr α) (hsize : sizeOf x < sizeOf expr) :
      checkExprTypes enums aliases rigid (x.map f) = checkExprTypes enums aliases rigid x :=
    checkExprTypes_map enums aliases rigid f x
  have children (xs : List (Expr α)) (h : ∀ x ∈ xs, sizeOf x < sizeOf expr) :
      (xs.map (Expr.map f)).mapM (checkExprTypes enums aliases rigid) =
        xs.mapM (checkExprTypes enums aliases rigid) :=
    traverse_same xs _ _ _ (fun x hx => checkExprTypes_map enums aliases rigid f x)
  cases expr with
  | literal | var | global => simp [Expr.map, checkExprTypes]
  | builtin _ xs | update _ xs | record _ xs | tuple xs | array xs | construct _ _ _ xs | constructAs _ _ _ xs | call _ _ xs =>
      simp only [Expr.map, checkExprTypes]
      rw [children xs (by intros; simp_wf; have := List.sizeOf_lt_of_mem ‹_ ∈ _›; omega)]
  | member x _ | control _ x | project x _ | index x _ | slice x _ _ | «repeat» x _ | store x | load x | hint _ x channel | neg x =>
      simp only [Expr.map, checkExprTypes, sub x (by simp_wf <;> omega)]
  | letValue _ x b | binary _ x b =>
      simp only [Expr.map, checkExprTypes, checkPatternTypes_map,
        sub x (by simp_wf <;> omega), sub b (by simp_wf <;> omega)]
  | matchValue x arms =>
      simp only [Expr.map, checkExprTypes, sub x (by simp_wf <;> omega)]
      congr 1
      funext _
      apply congrArg (fun v : Except String (List Unit) => v >>= fun _ => pure ())
      apply traverse_same
      intro arm member
      simp only [checkPatternTypes_map,
        sub arm.2 (by have := List.sizeOf_lt_of_mem member; cases arm; simp_all [Prod.mk.sizeOf_spec]; omega)]
termination_by sizeOf expr
decreasing_by
  all_goals first | exact h x hx | exact hsize

theorem expandExpr_map (aliases) (f : α → β) (expr : Expr α) :
    expandExpr aliases (expr.map f) = (expandExpr aliases expr).map (Expr.map f) := by
  have sub (x : Expr α) (hsize : sizeOf x < sizeOf expr) :
      expandExpr aliases (x.map f) = (expandExpr aliases x).map (Expr.map f) :=
    expandExpr_map aliases f x
  have children (xs : List (Expr α)) (h : ∀ x ∈ xs, sizeOf x < sizeOf expr) :
      (xs.map (Expr.map f)).mapM (expandExpr aliases) =
        (xs.mapM (expandExpr aliases)).map (List.map (Expr.map f)) :=
    traverse_map xs _ _ _ _ (fun x hx => expandExpr_map aliases f x)
  cases expr with
  | literal | var | global => simp [Expr.map, expandExpr, map_pure]
  | builtin _ xs | update _ xs | record _ xs | tuple xs | array xs | constructAs _ _ _ xs | call _ _ xs =>
      simp only [Expr.map, expandExpr]
      rw [children xs (by intros; simp_wf; have := List.sizeOf_lt_of_mem ‹_ ∈ _›; omega)]
      all_goals simp [except_map_eq, bind_map_left, _root_.map_bind, Functor.map_map, Expr.map]
  | construct n ts c xs =>
      simp only [Expr.map, expandExpr]
      rw [children xs (by intros; simp_wf; have := List.sizeOf_lt_of_mem ‹_ ∈ _›; omega)]
      cases xs.mapM (expandExpr aliases) <;> simp only [Except.map, bind, Except.bind]
      cases found : aliases.find? (·.name == n) with
      | none =>
          cases ts.mapM (fun ts => ts.mapM (expandType aliases)) <;>
            simp [found, pure, Except.pure, Except.map, bind, Except.bind, Expr.map]
      | some d =>
          cases resolved : constructorType aliases d ts <;>
            simp only [found, resolved, pure, Except.pure, Except.map, bind, Except.bind, Expr.map]
  | member x _ | control _ x | project x _ | index x _ | slice x _ _ | «repeat» x _ | store x | load x | hint _ x channel | neg x =>
      simp only [Expr.map, expandExpr, sub x (by simp_wf <;> omega)]
      all_goals simp [except_map_eq, bind_map_left, _root_.map_bind, Functor.map_map, Expr.map]
  | letValue _ x b | binary _ x b =>
      simp only [Expr.map, expandExpr, expandPattern_map,
        sub x (by simp_wf <;> omega), sub b (by simp_wf <;> omega)]
      all_goals simp [except_map_eq, bind_map_left, _root_.map_bind, Functor.map_map, Expr.map]
  | matchValue x arms =>
      have mapped := traverse_map arms
        (fun arm => (arm.1.map f, arm.2.map f))
        (fun arm : Pattern α × Expr α => (arm.1.map f, arm.2.map f))
        (fun arm => do return (← expandPattern aliases arm.1, ← expandExpr aliases arm.2))
        (fun arm => do return (← expandPattern aliases arm.1, ← expandExpr aliases arm.2))
        (by
          intro arm member
          simp only [expandPattern_map,
            sub arm.2 (by have := List.sizeOf_lt_of_mem member; cases arm; simp_all [Prod.mk.sizeOf_spec]; omega)]
          simp [except_map_eq, bind_map_left, _root_.map_bind, Functor.map_map])
      simp only [Expr.map, expandExpr, sub x (by simp_wf <;> omega), mapped]
      simp [except_map_eq, bind_map_left, _root_.map_bind, Functor.map_map, Expr.map]
termination_by sizeOf expr
decreasing_by
  all_goals first | exact h x hx | exact hsize

theorem expandFunction_map (enums raw aliases) (f : α → β) (fn : Function α) :
    expandFunction enums raw aliases { fn with body := fn.body.map f } =
      (expandFunction enums raw aliases fn).map (fun fn => { fn with body := fn.body.map f }) := by
  simp only [expandFunction, checkExprTypes_map, expandExpr_map]
  simp [except_map_eq, bind_map_left, _root_.map_bind, Functor.map_map]

theorem expandTable_map (enums raw aliases) (f : α → β) (table : Table α) :
    expandTable enums raw aliases { table with rows := table.rows.map (Expr.map f) } =
      (expandTable enums raw aliases table).map (fun t => { t with rows := t.rows.map (Expr.map f) }) := by
  have checked := traverse_same table.rows (Expr.map f)
    (checkExprTypes enums raw []) (checkExprTypes enums raw [])
    (fun x _ => checkExprTypes_map enums raw [] f x)
  have expanded := traverse_map table.rows (Expr.map f) (Expr.map f)
    (expandExpr aliases) (expandExpr aliases) (fun x _ => expandExpr_map aliases f x)
  simp only [expandTable, checked, expanded]
  simp [except_map_eq, bind_map_left, _root_.map_bind, Functor.map_map]

theorem expandConst_map (enums raw aliases) (f : α → β) (d : ConstDecl α) :
    expandConst enums raw aliases (d.map f) = (expandConst enums raw aliases d).map (ConstDecl.map f) := by
  simp only [expandConst, ConstDecl.map, checkPatternTypes_map, expandPattern_map]
  simp [except_map_eq, bind_map_left, _root_.map_bind, Functor.map_map, ConstDecl.map]

theorem expandProgram_map (aliases) (f : α → β) (p : Program α) :
    expandProgram aliases (p.map f) = (expandProgram aliases p).map (Program.map f) := by
  have functions := traverse_map p.functions
    (fun fn => { fn with body := fn.body.map f }) (fun fn => { fn with body := fn.body.map f })
    (expandFunction p.nominals p.aliases aliases) (expandFunction p.nominals p.aliases aliases)
    (fun fn _ => expandFunction_map p.nominals p.aliases aliases f fn)
  have tables := traverse_map p.tables
    (fun t => { t with rows := t.rows.map (Expr.map f) }) (fun t => { t with rows := t.rows.map (Expr.map f) })
    (expandTable p.nominals p.aliases aliases) (expandTable p.nominals p.aliases aliases)
    (fun t _ => expandTable_map p.nominals p.aliases aliases f t)
  have consts := traverse_map p.consts (ConstDecl.map f) (ConstDecl.map f)
    (expandConst p.nominals p.aliases aliases) (expandConst p.nominals p.aliases aliases)
    (fun d _ => expandConst_map p.nominals p.aliases aliases f d)
  change expandProgram aliases { p with functions := p.functions.map (fun fn => { fn with body := fn.body.map f }), tables := p.tables.map (fun t => { t with rows := t.rows.map (Expr.map f) }), consts := p.consts.map (ConstDecl.map f) } = _
  simp only [expandProgram, Program.nominals, Program.map] at functions tables consts ⊢
  rw [functions, tables, consts]
  simp [except_map_eq, bind_map_left, _root_.map_bind, Functor.map_map, Program.map]

end Aliases

/-- Alias expansion depends only on types and names, not on literal values. -/
theorem expandAliases_map (f : α → β) (p : Program α) :
    expandAliases (p.map f) = (expandAliases p).map (Program.map f) := by
  have resolved : Aliases.resolveDeclarations (p.map f) = Aliases.resolveDeclarations p := rfl
  simp only [expandAliases, resolved, Aliases.expandProgram_map]
  cases Aliases.resolveDeclarations p <;> rfl

/-- Choosing a field after alias expansion gives exactly the same AST as
expanding after literal conversion, with the same expansion errors. -/
theorem expandAliases_toField (p : Program Nat) (F : Type) [NatCast F] :
    expandAliases (p.toField F) = (expandAliases p).map (fun q => q.toField F) :=
  expandAliases_map Nat.cast p

end Aiur.Generic
