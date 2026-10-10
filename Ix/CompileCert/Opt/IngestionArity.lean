import Ix.CanonM
import Ix.CompileCert.Opt.SourceInstallScope

/-!
Counts on the actual source-ingestion/export paths.
No cache-content fidelity, hash injectivity, source arity law or new final
compiler premise is assumed. General ingestion and lookup refinement remain
open; these facts preserve counts even for an arbitrary CanonState.
-/

namespace Ix.CompileCert.Opt.IngestionArity

theorem list_mapM_state_length {σ α β : Type} (f : α → StateM σ β)
    (xs : List α) (state : σ) :
    ((xs.mapM f).run state).1.length = xs.length := by
  induction xs generalizing state with
  | nil => rfl
  | cons x xs ih =>
    rw [List.mapM_cons]
    change (((xs.mapM f).run ((f x).run state).2).1.length + 1) = xs.length + 1
    exact congrArg (fun n => n + 1) (ih ((f x).run state).2)

theorem array_mapM_state_size {σ α β : Type} (f : α → StateM σ β)
    (xs : Array α) (state : σ) :
    ((xs.mapM f).run state).1.size = xs.size := by
  rw [Array.mapM_eq_mapM_toList, StateT.run_map]
  change (((xs.toList.mapM f).run state).1.toArray).size = xs.size
  simpa only [List.size_toArray, Array.length_toList] using
    list_mapM_state_length f xs.toList state

/-- Header telescope cardinality is independent of every cache content. -/
theorem canonConstantVal_params_size (source : Lean.ConstantVal)
    (state : Ix.CanonM.CanonState) :
    ((Ix.CanonM.canonConstantVal source).run state).1.levelParams.size =
      source.levelParams.length := by
  unfold Ix.CanonM.canonConstantVal
  simp only [StateT.run_bind, StateT.run_pure]
  change ((source.levelParams.toArray.mapM Ix.CanonM.canonName).run
    ((Ix.CanonM.canonName source.name).run state).2).1.size = source.levelParams.length
  simpa only [List.size_toArray] using array_mapM_state_size
    Ix.CanonM.canonName source.levelParams.toArray
      ((Ix.CanonM.canonName source.name).run state).2

/-- Every actual declaration kind retains its source universe-parameter count.
This says nothing about the identities returned from the name/expression caches. -/
theorem canonConst_params_size (source : Lean.ConstantInfo)
    (state : Ix.CanonM.CanonState) :
    ((Ix.CanonM.canonConst source).run state).1.getCnst.levelParams.size =
      source.levelParams.length := by
  cases source <;>
    change ((Ix.CanonM.canonConstantVal _).run state).1.levelParams.size = _
  all_goals exact canonConstantVal_params_size _ state

theorem list_mapM_export_length {α β : Type} (f : α → ExportM β)
    {xs : List α} {ys : List β} (success : xs.mapM f = .ok ys) :
    ys.length = xs.length := by
  induction xs generalizing ys with
  | nil =>
    have same : ys = [] := (except_pure_ok' success).symm
    subst ys
    rfl
  | cons x xs ih =>
    rw [List.mapM_cons] at success
    obtain ⟨y, _, success⟩ := except_bind_ok success
    obtain ⟨rest, tail, success⟩ := except_bind_ok success
    have same := except_pure_ok' success
    subst ys
    simpa only [List.length_cons] using congrArg Nat.succ (ih tail)

/-- Successful source export preserves all arguments in their original spine. -/
theorem source_levels_length {params : List Lean.Name} {levels : List Lean.Level}
    {out : List Kernel.Level}
    (exported : levels.mapM (exportSourceLevel params) = .ok out) :
    out.length = levels.length :=
  list_mapM_export_length _ exported

theorem source_constant_export {params : List Lean.Name} {name : Lean.Name}
    {levels : List Lean.Level} {out : Kernel.Expr}
    (exported : exportSourceExpr params (.const name levels) = .ok out) :
    ∃ targetLevels, out = .const (sourceName name) targetLevels ∧
      levels.mapM (exportSourceLevel params) = .ok targetLevels ∧
      targetLevels.length = levels.length := by
  simp only [exportSourceExpr, exportExprWith, bind, Except.bind] at exported
  obtain ⟨targetLevels, levelsExported, exported⟩ := except_bind_ok exported
  have same := except_pure_ok' exported
  exact ⟨targetLevels, same.symm, levelsExported, source_levels_length levelsExported⟩

/-- The referenced arity is obtained from the existing source rule's actual
lookup. No arity assumption is introduced by this export/ingestion bridge. -/
theorem source_constant_inferred_arity {params : List Lean.Name} {name : Lean.Name}
    {levels : List Lean.Level} {out type : Kernel.Expr} {env : Kernel.Env}
    {grade : Kernel.Rules.Grade} {depth : Nat}
    (exported : exportSourceExpr params (.const name levels) = .ok out)
    (inferred : Kernel.Rules.Infer env grade depth out type) :
    ∃ referenced, env.find? (sourceName name) = some referenced ∧
      levels.length = referenced.toConstantVal.levelParams.length := by
  obtain ⟨targetLevels, rfl, _, size⟩ := source_constant_export exported
  cases inferred with
  | const lookup _ arity => exact ⟨_, lookup, size.symm.trans arity⟩


end Ix.CompileCert.Opt.IngestionArity
