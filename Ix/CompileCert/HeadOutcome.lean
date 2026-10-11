import Ix.CompileCert.HeadPublication
import Ix.CompileCert.Promotion

/-!
Authenticated heads across the actual worker-outcome handler. Source overlays
do not affect recipe authentication; original-form promotion preserves the
source/head view; remaining claims and failure paths preserve its invariant.
Consequently any fold of outcomes with authenticated compiled caches retains
the invariant. Proving that every production compile supplies such a cache,
and connecting the recipe laws to semantics, remain separate obligations.
-/

namespace Ix.CompileCert.HeadOutcome

open Ix (Name)
open Ix.CompileM Ix.CompileCert.HeadPublication

theorem certified_overlay (source : Ix.Environment) (overlay : Std.HashMap Name Ix.ConstantInfo)
    (name owner : Name) :
    Certified { source with overlay } name owner ↔ Certified source name owner := Iff.rfl

theorem claims_overlay (source : Ix.Environment) (overlay : Std.HashMap Name Ix.ConstantInfo)
    (claims : Array (Name × Name)) :
    ClaimsValid { source with overlay } claims ↔ ClaimsValid source claims := Iff.rfl

theorem promoteAuxDriver_observe (before after : CompileEnv) (name : Name)
    (address : Address) (metadata : Ixon.ConstantMeta)
    (success : promoteAuxDriver before name address metadata = .ok after) :
    observe after = observe before := by
  unfold promoteAuxDriver at success
  simp only [bind, pure, Except.bind, Except.pure, throw, throwThe] at success
  repeat' first | split at success | cases success
  all_goals rfl

private theorem promotionLoop_observe (rows : Array (Name × Address × Ixon.ConstantMeta))
    (before after : DriverAcc)
    (success : forIn rows before (fun row state => do
      let cenv ← Ix.PhaseTimers.withPhase .noAux state.cenv
        (promoteAuxDriver · row.1 row.2.1 row.2.2)
      pure (.yield { state with cenv })) = (Except.ok after : Except CompileError DriverAcc)) :
    observe after.cenv = observe before.cenv := by
  apply Canon.forIn_except_array _ (fun _ state => observe state.cenv = observe before.cenv)
    ?_ rows rfl success
  intro pre row state step previous ran
  obtain ⟨cenv, promoted, emitted⟩ := Canon.except_bind_ok.mp ran
  have stable := promoteAuxDriver_observe state.cenv cenv row.1 row.2.1 row.2.2
    (by simpa [Ix.PhaseTimers.withPhase, Ix.PhaseTimers.enterV, Ix.PhaseTimers.exitV] using promoted)
  exact ⟨{ state with cenv }, (Canon.except_pure_ok emitted).symm, stable.trans previous⟩

theorem promoteOriginalBlock_observe (before after : DriverAcc) (lo : Name)
    (result : BlockResult) (cache : BlockState)
    (success : promoteOriginalBlock before lo result cache = .ok after) :
    observe after.cenv = observe before.cenv := by
  unfold promoteOriginalBlock at success
  obtain ⟨_, _, success⟩ := Canon.except_bind_ok.mp success
  obtain ⟨staged, loop, success⟩ := Canon.except_bind_ok.mp success
  have stable := promotionLoop_observe _ before staged loop
  have final := Canon.except_pure_ok success
  subst after
  exact stable

def Good (source : Ix.Environment) (state : DriverAcc) : Prop :=
  state.cenv.env = source ∧ TableValid source state.cenv.p3Heads

theorem good_of_observe {source : Ix.Environment} {before after : DriverAcc}
    (same : observe after.cenv = observe before.cenv) (valid : Good source before) : Good source after := by
  have hs := congrArg Prod.fst same
  have hh := congrArg (fun view => view.2.1) same
  dsimp only [observe] at hs hh
  exact ⟨hs.trans valid.1, by rw [hh]; exact valid.2⟩

theorem fail_good {source : Ix.Environment} (before : DriverAcc) (all : Ix.Set Name) (message : String)
    (valid : Good source before) : Good source (failAuxPromotion before all message) := by
  have hs := congrArg Prod.fst (failAuxPromotion_observe before all message)
  dsimp only [observe] at hs
  refine ⟨hs.trans valid.1, ?_⟩
  rw [← hs.trans valid.1]
  apply failAuxPromotion_valid
  rw [valid.1]
  exact valid.2

theorem forIn_id_pred {α β : Type} (items : List α) (initial : β)
    (body : α → β → Id (ForInStep β)) (property : β → Prop)
    (preserved : ∀ item state, property state → property (body item state).value)
    (valid : property initial) : property (forIn (m := Id) items initial body) := by
  induction items generalizing initial with
  | nil => exact valid
  | cons item rest ih =>
    rw [List.forIn_cons]
    have next := preserved item initial valid
    cases result : body item initial with
    | done after =>
      change property after
      simpa [result] using next
    | yield after =>
      apply ih
      simpa [result] using next

theorem forIn_set_pred {β : Type} (items : Ix.Set Name) (initial : β)
    (body : Name → β → Id (ForInStep β)) (property : β → Prop)
    (preserved : ∀ item state, property state → property (body item state).value)
    (valid : property initial) : property (forIn (m := Id) items initial body) := by
  rw [Std.HashSet.forIn_eq_forIn_toList]
  exact forIn_id_pred items.toList initial body property preserved valid

theorem forIn_array_pred {α β : Type} (items : Array α) (initial : β)
    (body : α → β → Id (ForInStep β)) (property : β → Prop)
    (preserved : ∀ item state, property state → property (body item state).value)
    (valid : property initial) : property (forIn (m := Id) items initial body) := by
  rw [← Array.forIn_toList]
  exact forIn_id_pred items.toList initial body property preserved valid

theorem auxNames_good {source : Ix.Environment} (before : DriverAcc) (names : Array Name)
    (valid : Good source before) :
    Good source (forIn (m := Id) names before (fun name state => .yield
      { state with cenv := { state.cenv with auxGenExtraNames := state.cenv.auxGenExtraNames.insert name } })) := by
  apply forIn_array_pred names before _ (Good source) ?_ valid
  intro name state previous
  exact previous

theorem forIn_selected {α : Type} (items : Ix.Set Name)
    (body : Name → (Option α × Unit) → Id (ForInStep (Option α × Unit))) (property : α → Prop)
    (preserved : ∀ name state result, (body name state).value.1 = some result → property result)
    {result : α} (selected : (forIn (m := Id) items (none, ()) body).1 = some result) :
    property result := by
  have checked := forIn_set_pred items (none, ()) body
    (fun state => ∀ result, state.1 = some result → property result)
    (fun name state _ => preserved name state) (by intro result missing; cases missing)
  exact checked result selected

theorem promoteRemaining_good {source : Ix.Environment} (before : DriverAcc) (all : Ix.Set Name)
    (valid : Good source before) : Good source (promoteRemaining before all).1 := by
  unfold promoteRemaining
  simp only [Id.run, bind, pure]
  split
  · rename_i result selected
    apply forIn_selected all _ (fun state => Good source state.1) ?_ selected
    intro name state result outcome
    repeat' first | split at outcome | cases outcome
    all_goals exact fail_good before all _ valid
  · apply forIn_set_pred all (before, #[]) _ (fun state => Good source state.1) ?_ valid
    intro name state previous
    split
    · exact previous
    · split <;> exact previous

theorem finishAuxPromotion_good {source : Ix.Environment} (before : DriverAcc) (lo : Name)
    (all : Ix.Set Name) (original : Option (BlockResult × BlockState))
    (valid : Good source before) : Good source (finishAuxPromotion before lo all original).1 := by
  unfold finishAuxPromotion
  simp only [Id.run, bind, pure]
  cases original with
  | none =>
    dsimp only
    split
    · rename_i result selected
      apply forIn_selected all _ (fun state => Good source state.1) ?_ selected
      intro name state result outcome
      repeat' first | split at outcome | cases outcome
      all_goals exact fail_good before all _ valid
    · exact promoteRemaining_good before all valid
  | some pair =>
    rcases pair with ⟨result, cache⟩
    dsimp only
    cases promoted : promoteOriginalBlock before lo result cache with
    | error error => exact fail_good before all _ valid
    | ok staged =>
      have stagedGood := good_of_observe
        (promoteOriginalBlock_observe before staged lo result cache promoted) valid
      dsimp only
      split
      · rename_i result selected
        apply forIn_selected all _ (fun state => Good source state.1) ?_ selected
        intro name state result outcome
        repeat' first | split at outcome | cases outcome
        all_goals exact fail_good before all _ valid
      · exact promoteRemaining_good staged all stagedGood

theorem merge_good {source : Ix.Environment} (before : DriverAcc) (lo : Name)
    (result : BlockResult) (cache : BlockState) (valid : Good source before)
    (checked : ClaimsValid source cache.p3Heads) : Good source (mergeCompiledBlock before lo result cache) := by
  refine ⟨(merge_source before lo result cache).trans valid.1, ?_⟩
  have preserved := merge_valid before lo result cache
    (by rw [valid.1]; exact valid.2) (by rw [valid.1]; exact checked)
  simpa only [merge_source, valid.1] using preserved

def OutcomeCertified (source : Ix.Environment) : AuxBlockOutcome → Prop
  | .compiled _ cache => ClaimsValid source cache.p3Heads
  | .promoted (some (_, _, cache)) .. => ClaimsValid source cache.p3Heads
  | _ => True

theorem applyAuxBlockOutcome_good {source : Ix.Environment} (before : DriverAcc) (lo : Name)
    (all : Ix.Set Name) (outcome : AuxBlockOutcome) (valid : Good source before)
    (checked : OutcomeCertified source outcome) :
    Good source (applyAuxBlockOutcome before lo all outcome).1 := by
  unfold applyAuxBlockOutcome
  simp only [Id.run, bind, pure]
  cases outcome with
  | compiled result cache =>
    dsimp only
    cases accepted : checkCompiledBlock before.cenv lo result cache with
    | error error =>
      apply forIn_set_pred all before _ (Good source) ?_ valid
      intro name state previous
      exact previous
    | ok value =>
      cases value
      dsimp only
      split <;> exact merge_good before lo result cache valid checked
  | failed message =>
    apply forIn_set_pred all before _ (Good source) ?_ valid
    intro name state previous
    exact previous
  | promoted cross names incomplete original failed =>
    dsimp only
    cases cross with
    | none =>
      repeat' first
        | exact fail_good before all _ valid
        | exact finishAuxPromotion_good before lo all original valid
        | dsimp only
        | split
    | some entry =>
      rcases entry with ⟨crossName, result, cache⟩
      dsimp only
      cases accepted : checkCompiledBlock before.cenv crossName result cache with
      | error error =>
        repeat' first
          | exact fail_good before all _ valid
          | exact finishAuxPromotion_good before lo all original valid
          | dsimp only
          | split
      | ok acceptedUnit =>
        cases acceptedUnit
        have crossed := auxNames_good (mergeCompiledBlock before crossName result cache) names
          (merge_good before crossName result cache valid checked)
        repeat' first
          | exact fail_good _ all _ crossed
          | exact finishAuxPromotion_good _ lo all original crossed
          | dsimp only
          | split

theorem fold_outcomes_good {source : Ix.Environment} (before : DriverAcc)
    (outcomes : List (Name × Ix.Set Name × AuxBlockOutcome)) (valid : Good source before)
    (checked : ∀ row ∈ outcomes, OutcomeCertified source row.2.2) :
    Good source (outcomes.foldl
      (fun state row => (applyAuxBlockOutcome state row.1 row.2.1 row.2.2).1) before) := by
  induction outcomes generalizing before with
  | nil => exact valid
  | cons row rest ih =>
    apply ih
    · exact applyAuxBlockOutcome_good before row.1 row.2.1 row.2.2 valid (checked row (by simp))
    · intro later member
      exact checked later (List.mem_cons_of_mem _ member)

theorem initial_good (source : Ix.Environment) :
    Good source { cenv := CompileEnv.new source } := by
  exact ⟨rfl, table_empty source⟩

theorem outcome_lookup_certified {source : Ix.Environment} (before : DriverAcc) (lo : Name)
    (all : Ix.Set Name) (outcome : AuxBlockOutcome) (valid : Good source before)
    (checked : OutcomeCertified source outcome) {name owner : Name}
    (found : Ix.Compile.Pass.headOwner? (applyAuxBlockOutcome before lo all outcome).1.cenv.p3Heads name = some owner) :
    Certified source name owner :=
  headOwner_certified (applyAuxBlockOutcome_good before lo all outcome valid checked).2 found

end Ix.CompileCert.HeadOutcome
