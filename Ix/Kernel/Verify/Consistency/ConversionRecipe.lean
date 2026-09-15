/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.SourceConversion
import Ix.Kernel.Verify.Consistency.IngressCoherence

/-!
# Exact source conversion under finite interning assumptions

The prediction and its finite candidate inventories depend only on source
conversion. Faithful interning makes actual execution follow that same path,
including failures, while deriving coherence of every intermediate table.
-/

namespace Ix.Kernel.Consistency

/-- Collision data for the initial table and the finite predicted candidates.
No conclusion about a loaded declaration or model reading is an input. -/
structure ConversionData (recipe : ConversionRecipe α) (before : InternTable .anon) : Prop where
  expressions : KExpr.CollisionFree fun term => before.ExprSupport term ∨ term ∈ recipe.exprs
  universes : KUniv.CollisionFree fun level => before.UnivSupport level ∨ level ∈ recipe.univs

private structure InternClosed (expressions : KExpr .anon → Prop)
    (universes : KUniv .anon → Prop) (table : InternTable .anon) : Prop where
  coherent : table.WF
  exprs : ∀ term, table.ExprSupport term → expressions term
  univs : ∀ level, table.UnivSupport level → universes level

private theorem recipe_spec {expressions : KExpr .anon → Prop} {universes : KUniv .anon → Prop}
    (exprFaithful : KExpr.CollisionFree expressions) (univFaithful : KUniv.CollisionFree universes)
    (recipe : ConversionRecipe α) (coveredExprs : ∀ term ∈ recipe.exprs, expressions term)
    (coveredUnivs : ∀ level ∈ recipe.univs, universes level)
    (before : InternTable .anon) (valid : InternClosed expressions universes before) :
    match recipe.run before with
    | .ok value after => recipe.predict = .ok value ∧ InternClosed expressions universes after
    | .error error after => recipe.predict = .error error ∧ InternClosed expressions universes after := by
  induction recipe generalizing before with
  | done value => exact ⟨rfl, valid⟩
  | fail error => exact ⟨rfl, valid⟩
  | internE candidate next ih =>
      have member : expressions candidate := coveredExprs candidate (by simp [ConversionRecipe.exprs])
      have exactValue : (before.internExpr candidate).1 = candidate := by
        simpa only [KExpr.eraseMeta_anon] using before.internExpr_eraseMeta valid.coherent
          (KExpr.keyCollisionFree_anon.mpr (exprFaithful.mono fun term h =>
            h.elim (valid.exprs term) (fun equal => equal ▸ member)))
      have nextValid : InternClosed expressions universes (before.internExpr candidate).2 := by
        refine ⟨valid.coherent.internExpr candidate, ?_, ?_⟩
        · intro term found
          exact (InternTable.ExprSupport.of_internExpr found).elim
            (valid.exprs term) (fun equal => equal ▸ member)
        · intro level found
          exact valid.univs level (by simpa only [InternTable.UnivSupport,
            InternTable.internExpr_univs] using found)
      have post := ih candidate
        (fun term h => coveredExprs term (List.mem_cons_of_mem _ h)) coveredUnivs _ nextValid
      simpa only [ConversionRecipe.run, ConversionRecipe.predict, InternIngressM.internE,
        Bind.bind, EStateM.bind, exactValue] using post
  | internU candidate next ih =>
      have member : universes candidate := coveredUnivs candidate (by simp [ConversionRecipe.univs])
      have exactValue : (before.internUniv candidate).1 = candidate := by
        simpa only [KUniv.eraseMeta_anon] using before.internUniv_eraseMeta valid.coherent
          (univFaithful.mono fun level h =>
            h.elim (valid.univs level) (fun equal => equal ▸ member))
      have nextValid : InternClosed expressions universes (before.internUniv candidate).2 := by
        refine ⟨valid.coherent.internUniv candidate, ?_, ?_⟩
        · intro term found
          exact valid.exprs term (by simpa only [InternTable.ExprSupport,
            InternTable.internUniv_exprs] using found)
        · intro level found
          exact (InternTable.UnivSupport.of_internUniv found).elim
            (valid.univs level) (fun equal => equal ▸ member)
      have post := ih candidate coveredExprs
        (fun level h => coveredUnivs level (List.mem_cons_of_mem _ h)) _ nextValid
      simpa only [ConversionRecipe.run, ConversionRecipe.predict, InternIngressM.internU,
        Bind.bind, EStateM.bind, exactValue] using post

/-- Both actual outcomes agree with the source-only prediction. The finite
collision domain also covers every newly retained intern entry. -/
theorem ConversionRecipe.run_predict (recipe : ConversionRecipe α) (before : InternTable .anon)
    (coherent : before.WF) (data : ConversionData recipe before) :
    match recipe.run before with
    | .ok value after => recipe.predict = .ok value ∧ after.WF ∧
        (∀ term, after.ExprSupport term → before.ExprSupport term ∨ term ∈ recipe.exprs) ∧
        (∀ level, after.UnivSupport level → before.UnivSupport level ∨ level ∈ recipe.univs)
    | .error error after => recipe.predict = .error error ∧ after.WF ∧
        (∀ term, after.ExprSupport term → before.ExprSupport term ∨ term ∈ recipe.exprs) ∧
        (∀ level, after.UnivSupport level → before.UnivSupport level ∨ level ∈ recipe.univs) := by
  have post := recipe_spec data.expressions data.universes recipe (fun _ => Or.inr)
    (fun _ => Or.inr) before ⟨coherent, fun _ => Or.inl, fun _ => Or.inl⟩
  cases run : recipe.run before <;> rw [run] at post <;>
    exact ⟨post.1, post.2.coherent, post.2.exprs, post.2.univs⟩

end Ix.Kernel.Consistency

namespace Ix.Kernel.ConversionRecipe

theorem run_bind (recipe : ConversionRecipe α) (next : α → ConversionRecipe β) :
    (recipe >>= next).run = recipe.run >>= fun value => (next value).run := by
  change (bind recipe next).run = _
  induction recipe with
  | done value => rfl
  | fail error => rfl
  | internE candidate rest ih | internU candidate rest ih =>
      simp only [bind, run, ih, bind_assoc]

end Ix.Kernel.ConversionRecipe

namespace Ix.Kernel.Consistency

private def RecipeCorresponds (recipe : ConversionRecipe α) (action : InternIngressM α) : Prop :=
  recipe.run = action

private theorem recipe_pure (value : α) : RecipeCorresponds (pure value) (pure value) := rfl
private theorem recipe_throw (error : IngressErr) :
    RecipeCorresponds (throw error : ConversionRecipe α) (throw error) := rfl

private theorem recipe_bind {first : ConversionRecipe α} {second : α → ConversionRecipe β}
    {action : InternIngressM α} {next : α → InternIngressM β}
    (head : RecipeCorresponds first action) (tail : ∀ value, RecipeCorresponds (second value) (next value)) :
    RecipeCorresponds (first >>= second) (action >>= next) := by
  change (first >>= second).run = _
  rw [ConversionRecipe.run_bind, head]
  exact congrArg (fun rest => action >>= rest) (funext tail)

private theorem recipe_expr (term : KExpr .anon) :
    RecipeCorresponds (ConversionRecipe.emitExpr term) (InternIngressM.internE term) := rfl

private theorem recipe_univ (level : KUniv .anon) :
    RecipeCorresponds (ConversionRecipe.emitUniv level) (InternIngressM.internU level) := rfl

private def ConvCorresponds (recipe : StateT ConvState ConversionRecipe α)
    (action : InternConvM α) : Prop := ∀ cache, RecipeCorresponds (recipe cache) (action cache)

private theorem conv_pure (value : α) : ConvCorresponds (pure value) (pure value) := fun _ => rfl
private theorem conv_throw (error : IngressErr) :
    ConvCorresponds (throw error : StateT ConvState ConversionRecipe α) (throw error) := fun _ => rfl
private theorem conv_throw_bind (error : IngressErr) (next : α → StateT ConvState ConversionRecipe β)
    (action : α → InternConvM β) :
    ConvCorresponds ((throw error : StateT ConvState ConversionRecipe α) >>= next)
      ((throw error : InternConvM α) >>= action) := fun _ => rfl

private theorem conv_bind {first : StateT ConvState ConversionRecipe α}
    {second : α → StateT ConvState ConversionRecipe β} {action : InternConvM α}
    {next : α → InternConvM β} (head : ConvCorresponds first action)
    (tail : ∀ value, ConvCorresponds (second value) (next value)) :
    ConvCorresponds (first >>= second) (action >>= next) := by
  intro cache
  exact recipe_bind (head cache) (fun (value, cache) => tail value cache)

private theorem conv_lift {recipe : ConversionRecipe α} {action : InternIngressM α}
    (correct : RecipeCorresponds recipe action) : ConvCorresponds (liftM recipe) (liftM action) :=
  fun _ => recipe_bind correct (fun _ => recipe_pure _)

private theorem conv_get : ConvCorresponds (get : StateT ConvState ConversionRecipe ConvState) get :=
  fun _ => rfl

private theorem conv_modify (update : ConvState → ConvState) :
    ConvCorresponds (modify update : StateT ConvState ConversionRecipe Unit) (modify update) := fun _ => rfl

theorem conversionRecipe_univStep (stack : Array UFrame) (values : Array (KUniv .anon)) :
    (ConversionRecipe.univStep stack values).run = convertUnivStep stack values := by
  change RecipeCorresponds _ _
  dsimp only [ConversionRecipe.univStep, convertUnivStep]
  cases stack.back! with
  | process level =>
      cases level <;> first
        | exact recipe_pure _
        | exact recipe_bind (recipe_univ _) (fun _ => recipe_pure _)
  | succ | max | imax => exact recipe_bind (recipe_univ _) (fun _ => recipe_pure _)

theorem conversionRecipe_univLoop (fuel : Nat) (stack : Array UFrame) (values : Array (KUniv .anon)) :
    (ConversionRecipe.univLoop fuel stack values).run = convertUnivLoop fuel stack values := by
  change RecipeCorresponds _ _
  induction fuel generalizing stack values with
  | zero =>
      dsimp only [ConversionRecipe.univLoop, convertUnivLoop]
      split
      · cases values.back? <;> first | exact recipe_pure _ | exact recipe_throw _
      · exact recipe_throw _
  | succ fuel ih =>
      dsimp only [ConversionRecipe.univLoop, convertUnivLoop]
      split
      · cases values.back? <;> first | exact recipe_pure _ | exact recipe_throw _
      · exact recipe_bind (conversionRecipe_univStep stack values) (fun (stack, values) => ih stack values)

theorem conversionRecipe_univTree (root : Ixon.Univ) :
    (ConversionRecipe.univTree root).run = convertUnivTree root :=
  conversionRecipe_univLoop _ _ _

theorem conversionRecipe_univIdx (ctx : IngressCtx) (idx : UInt64) (cache : ConvState) :
    (ConversionRecipe.univIdx ctx idx cache).run = convertUnivIdx ctx idx cache := by
  suffices correct : ConvCorresponds (ConversionRecipe.univIdx ctx idx) (convertUnivIdx ctx idx) from
    correct cache
  dsimp only [ConversionRecipe.univIdx, convertUnivIdx]
  apply conv_bind conv_get
  intro state
  cases state.univCache[idx]? with
  | some level => exact conv_pure _
  | none =>
      cases ctx.univs[idx.toNat]? with
      | none => exact conv_throw _
      | some level =>
          exact conv_bind (conv_lift (conversionRecipe_univTree level))
            (fun _ => conv_bind (conv_modify _) (fun _ => conv_pure _))

private theorem list_forIn_corresponds {m n : Type → Type} [Monad m] [Monad n]
    (P : {α : Type} → m α → n α → Prop)
    (hpure : ∀ {α} (value : α), P (pure value) (pure value))
    (hbind : ∀ {α β} {first : m α} {second : α → m β} {action : n α} {next : α → n β},
      P first action → (∀ value, P (second value) (next value)) → P (first >>= second) (action >>= next))
    (items : List α) (initial : β) (left : α → β → m (ForInStep β))
    (right : α → β → n (ForInStep β)) (step : ∀ item state, P (left item state) (right item state)) :
    P (forIn items initial left) (forIn items initial right) := by
  induction items generalizing initial with
  | nil => simpa only [List.forIn_nil] using hpure initial
  | cons item rest ih =>
      simp only [List.forIn_cons]
      apply hbind (step item initial)
      intro result
      cases result with
      | done state => exact hpure state
      | yield state => exact ih state

private theorem array_forIn_corresponds {m n : Type → Type} [Monad m] [Monad n]
    (P : {α : Type} → m α → n α → Prop)
    (hpure : ∀ {α} (value : α), P (pure value) (pure value))
    (hbind : ∀ {α β} {first : m α} {second : α → m β} {action : n α} {next : α → n β},
      P first action → (∀ value, P (second value) (next value)) → P (first >>= second) (action >>= next))
    (items : Array α) (initial : β) (left : α → β → m (ForInStep β))
    (right : α → β → n (ForInStep β)) (step : ∀ item state, P (left item state) (right item state)) :
    P (forIn items initial left) (forIn items initial right) := by
  rw [← Array.forIn_toList, ← Array.forIn_toList]
  exact list_forIn_corresponds P hpure hbind _ initial _ _ step

theorem conversionRecipe_univArgs (ctx : IngressCtx) (idxs : Array UInt64) (cache : ConvState) :
    (ConversionRecipe.univArgs ctx idxs cache).run = convertUnivArgs ctx idxs cache := by
  suffices correct : ConvCorresponds (ConversionRecipe.univArgs ctx idxs) (convertUnivArgs ctx idxs) from
    correct cache
  dsimp only [ConversionRecipe.univArgs, convertUnivArgs]
  apply conv_bind _ (fun _ => conv_pure _)
  apply array_forIn_corresponds (@ConvCorresponds) (@conv_pure) (@conv_bind)
  intro idx out
  exact conv_bind (conversionRecipe_univIdx ctx idx) (fun _ => conv_pure _)

theorem conversionRecipe_exprStep (source : Ixon.Env) (ctx : IngressCtx)
    (stack : Array EFrame) (values : Array (KExpr .anon)) (cache : ConvState) :
    (ConversionRecipe.exprStep source ctx stack values cache).run =
      convertExprStep source ctx stack values cache := by
  suffices correct : ConvCorresponds (ConversionRecipe.exprStep source ctx stack values)
      (convertExprStep source ctx stack values) from correct cache
  dsimp only [ConversionRecipe.exprStep, convertExprStep]
  cases stack.back! with
  | process term =>
      cases term with
      | share idx =>
          apply conv_bind conv_get
          intro state
          cases state.exprCache[idx]? with
          | some value => exact conv_pure _
          | none => cases ctx.sharing[idx.toNat]? <;> first
              | exact conv_pure _
              | exact conv_throw_bind _ _ _
      | var idx => exact conv_bind (conv_lift (recipe_expr _)) (fun _ => conv_pure _)
      | sort idx =>
          exact conv_bind (conversionRecipe_univIdx ctx idx)
            (fun _ => conv_bind (conv_lift (recipe_expr _)) (fun _ => conv_pure _))
      | ref idx arguments =>
          dsimp only
          cases ctx.refs[idx.toNat]? with
          | none => exact conv_throw_bind _ _ _
          | some addr =>
              dsimp only
              exact conv_bind (conversionRecipe_univArgs ctx arguments)
                (fun _ => conv_bind (conv_lift (recipe_expr _)) (fun _ => conv_pure _))
      | recur idx arguments =>
          dsimp only
          cases ctx.mutCtx[idx.toNat]? with
          | none => exact conv_throw_bind _ _ _
          | some id =>
              exact conv_bind (conversionRecipe_univArgs ctx arguments)
                (fun _ => conv_bind (conv_lift (recipe_expr _)) (fun _ => conv_pure _))
      | nat idx =>
          dsimp only
          cases ctx.refs[idx.toNat]? with
          | none => exact conv_throw_bind _ _ _
          | some addr =>
              dsimp only
              cases source.getBlob? addr with
              | none => exact conv_throw_bind _ _ _
              | some bytes => exact conv_bind (conv_lift (recipe_expr _)) (fun _ => conv_pure _)
      | str idx =>
          dsimp only
          cases ctx.refs[idx.toNat]? with
          | none => exact conv_throw_bind _ _ _
          | some addr =>
              dsimp only
              cases source.getBlob? addr with
              | none => exact conv_throw_bind _ _ _
              | some bytes =>
                  dsimp only
                  cases String.fromUTF8? bytes with
                  | none => exact conv_throw_bind _ _ _
                  | some value => exact conv_bind (conv_lift (recipe_expr _)) (fun _ => conv_pure _)
      | app | lam | all | letE => exact conv_pure _
      | prj idx field value =>
          dsimp only
          cases ctx.refs[idx.toNat]? <;> first
          | exact conv_pure _
          | exact conv_throw_bind _ _ _
  | appDone | lamDone | allDone | letDone | prjDone =>
      exact conv_bind (conv_lift (recipe_expr _)) (fun _ => conv_pure _)
  | cacheShare idx => exact conv_bind (conv_modify _) (fun _ => conv_pure _)

theorem conversionRecipe_exprLoop (source : Ixon.Env) (ctx : IngressCtx) (fuel : Nat)
    (stack : Array EFrame) (values : Array (KExpr .anon)) (cache : ConvState) :
    (ConversionRecipe.exprLoop source ctx fuel stack values cache).run =
      convertExprLoop source ctx fuel stack values cache := by
  suffices correct : ConvCorresponds (ConversionRecipe.exprLoop source ctx fuel stack values)
      (convertExprLoop source ctx fuel stack values) from correct cache
  induction fuel generalizing stack values with
  | zero =>
      dsimp only [ConversionRecipe.exprLoop, convertExprLoop]
      split
      · cases values.back? with
        | none => exact conv_throw _
        | some value =>
            dsimp only
            split
            · exact conv_throw_bind _ _ _
            · exact conv_pure _
      · exact conv_throw _
  | succ fuel ih =>
      dsimp only [ConversionRecipe.exprLoop, convertExprLoop]
      split
      · cases values.back? with
        | none => exact conv_throw _
        | some value =>
            dsimp only
            split
            · exact conv_throw_bind _ _ _
            · exact conv_pure _
      · exact conv_bind (conversionRecipe_exprStep source ctx stack values)
          (fun (stack, values) => ih stack values)

theorem conversionRecipe_expr (source : Ixon.Env) (ctx : IngressCtx) (root : Ixon.Expr)
    (cache : ConvState) :
    (ConversionRecipe.expr source ctx root cache).run = convertExpr source ctx root cache :=
  conversionRecipe_exprLoop source ctx _ _ _ cache

theorem conversionRecipe_defn (source : Ixon.Env) (defn : Ixon.Definition)
    (constant : Ixon.Constant) (block : KId .anon) (mutCtx : Array (KId .anon))
    (hints : Option Lean.ReducibilityHints) :
    (ConversionRecipe.defn source defn constant block mutCtx hints).run =
      convertDefnAnon source defn constant block mutCtx hints := by
  change RecipeCorresponds _ _
  dsimp only [ConversionRecipe.defn, convertDefnAnon]
  apply recipe_bind (conversionRecipe_expr source _ defn.typ {})
  intro result
  exact recipe_bind (conversionRecipe_expr source _ defn.value result.2) (fun _ => recipe_pure _)

theorem conversionRecipe_recursor (source : Ixon.Env) (rec : Ixon.Recursor)
    (constant : Ixon.Constant) (block : KId .anon) (mutCtx : Array (KId .anon)) :
    (ConversionRecipe.recursor source rec constant block mutCtx).run =
      convertRecursorAnon source rec constant block mutCtx := by
  change RecipeCorresponds _ _
  dsimp only [ConversionRecipe.recursor, convertRecursorAnon]
  apply recipe_bind (conversionRecipe_expr source _ rec.typ {})
  intro result
  apply recipe_bind _ (fun _ => recipe_pure _)
  apply array_forIn_corresponds (@RecipeCorresponds) (@recipe_pure) (@recipe_bind)
  intro rule state
  exact recipe_bind (conversionRecipe_expr source _ rule.rhs _) (fun _ => recipe_pure _)

theorem conversionRecipe_standalone (source : Ixon.Env) (addr : Address) (constant : Ixon.Constant) :
    (ConversionRecipe.standalone source addr constant).run = convertAnonStandalone source addr constant := by
  change RecipeCorresponds _ _
  dsimp only [ConversionRecipe.standalone, convertAnonStandalone]
  cases constant.info with
  | defn defn => exact conversionRecipe_defn source defn constant _ _ _
  | recr rec => exact conversionRecipe_recursor source rec constant _ _
  | axio axio => exact recipe_bind (conversionRecipe_expr source _ axio.typ {}) (fun _ => recipe_pure _)
  | quot quot => exact recipe_bind (conversionRecipe_expr source _ quot.typ {}) (fun _ => recipe_pure _)
  | muts | dPrj | iPrj | rPrj | cPrj => exact recipe_throw _

/-- The actual standalone converter returns the declaration predicted from
the source, including its exact universe arity, type, body, and metadata. -/
theorem convertAnonStandalone_prediction {source : Ixon.Env} {addr : Address}
    {constant : Ixon.Constant} {before after : InternTable .anon} {concrete : KConst .anon}
    (coherent : before.WF) (data : ConversionData (ConversionRecipe.standalone source addr constant) before)
    (run : convertAnonStandalone source addr constant before = .ok concrete after) :
    (ConversionRecipe.standalone source addr constant).predict = .ok concrete ∧ after.WF := by
  have post := ConversionRecipe.run_predict (ConversionRecipe.standalone source addr constant) before coherent data
  rw [conversionRecipe_standalone, run] at post
  exact ⟨post.1, post.2.1⟩

end Ix.Kernel.Consistency
