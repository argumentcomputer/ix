import Ix.Compile.SourceGraph
import Ix.Cert.SourceReverse
import Ix.Cert.Canon

/-! The concrete SourceGraph constructor and collector, not assumed summary
correctness. Materialization below is a proof specification only; the runtime
producer/collector and input-order/classifier bridges remain to be connected.
-/
namespace Ix.Cert.SourceGraph

open Ix (Name ConstantInfo)
open Ix.Compile.SourceGraph

theorem hasStrLit_eq (e : Ix.Expr) : Ix.Compile.SourceGraph.hasStrLit e = Ix.Cert.hasStrLit e := by
  induction e with
  | lit l _ => cases l <;> rfl
  | _ => simp_all [Ix.Compile.SourceGraph.hasStrLit, Ix.Cert.hasStrLit]

theorem hasNatLit_eq (e : Ix.Expr) : Ix.Compile.SourceGraph.hasNatLit e = Ix.Cert.hasNatLit e := by
  induction e with
  | lit l _ => cases l <;> rfl
  | _ => simp_all [Ix.Compile.SourceGraph.hasNatLit, Ix.Cert.hasNatLit]

theorem terms_eq (ci : ConstantInfo) : terms ci = termsOf ci := by cases ci <;> rfl

theorem literalNames_eq (ci : ConstantInfo) : literalNames (literalUse ci) = literalSupport ci := by
  simp only [literalUse, terms_eq, show Ix.Compile.SourceGraph.hasStrLit = Ix.Cert.hasStrLit from
    funext hasStrLit_eq, show Ix.Compile.SourceGraph.hasNatLit = Ix.Cert.hasNatLit from funext hasNatLit_eq,
    literalSupport]
  split
  · rfl
  · split <;> rfl

theorem captureUsing_eq (ci : ConstantInfo) (direct : Ix.Set Name) (h : direct = refsOf ci) :
    captureUsing ci direct = capture ci := by rw [h]; rfl

theorem rowUsing_eq (n : Name) (ci : ConstantInfo) (direct : Ix.Set Name) (h : direct = refsOf ci) :
    rowUsing n ci direct = rowOfCanonical n ci := by
  simp only [rowUsing, rowOfCanonical, captureUsing_eq ci direct h]

private theorem nameEq_eq (a b : Name) : Ix.Compile.ExactKey.nameEq a b = Ix.Cert.nameEq a b := by
  apply Bool.eq_iff_iff.mpr
  rw [Ix.Compile.ExactKey.nameEq_iff, Closure.nameEq_iff]

theorem dependencies_capture (rs : Ix.Map Name (Array (Name × Name))) (ci : ConstantInfo) :
    Ix.Compile.SourceGraph.dependencies rs (capture ci) = Ix.Cert.dependencies rs ci := by
  simp only [Ix.Compile.SourceGraph.dependencies, capture, captureUsing, literalNames_eq, Ix.Cert.dependencies,
    refsOf, nameEq_eq]
  cases ci with
  | inductInfo v => cases h : v.all[0]? <;> simp [h]
  | _ => rfl

/-- The full-map specification uses the same key and insertion order as the
rows. No complete canonical map is built by the executable collector. -/
def full (xs : List (Name × ConstantInfo)) : Ix.Environment :=
  { consts := xs.foldl (fun m p => m.insert p.1 p.2) {} }

private def Coherent (acc : Collected) (m : Ix.Map Name ConstantInfo) : Prop :=
  (∀ n, acc.nodes.get? n = (m.get? n).map capture) ∧
  (∀ n, acc.code.get? n = (m.get? n).bind keep)

private theorem coherent_empty : Coherent {} {} := by
  constructor <;> intro n <;> simp

private theorem coherent_merge (acc : Collected) (m : Ix.Map Name ConstantInfo)
    (h : Coherent acc m) (n : Name) (ci : ConstantInfo) :
    Coherent (mergeRow acc (rowOfCanonical n ci)) (m.insert n ci) := by
  constructor
  · intro query
    simp only [mergeRow, rowOfCanonical, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]
    split
    · rfl
    · exact h.1 query
  · intro query
    cases kept : keep ci with
    | none =>
      simp only [mergeRow, rowOfCanonical, kept, Std.HashMap.get?_eq_getElem?,
        Std.HashMap.getElem?_erase, Std.HashMap.getElem?_insert]
      split
      · simpa only [Option.bind_some] using kept.symm
      · exact h.2 query
    | some value =>
      simp only [mergeRow, rowOfCanonical, kept, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]
      split
      · simpa only [Option.bind_some] using kept.symm
      · exact h.2 query

private theorem coherent_fold (xs : List (Name × ConstantInfo)) (acc : Collected)
    (m : Ix.Map Name ConstantInfo) (h : Coherent acc m) :
    Coherent ((xs.map fun p => rowOfCanonical p.1 p.2).foldl mergeRow acc)
      (xs.foldl (fun m p => m.insert p.1 p.2) m) := by
  induction xs generalizing acc m with
  | nil => exact h
  | cons p xs ih => exact ih _ _ (coherent_merge acc m h p.1 p.2)

theorem collect_nodes_get (xs : List (Name × ConstantInfo)) (n : Name) :
    (collect (xs.map fun p => rowOfCanonical p.1 p.2)).nodes.get? n =
      ((full xs).consts.get? n).map capture :=
  (coherent_fold xs {} {} coherent_empty).1 n

theorem collect_code_get (xs : List (Name × ConstantInfo)) (n : Name) :
    (collect (xs.map fun p => rowOfCanonical p.1 p.2)).code.get? n =
      ((full xs).consts.get? n).bind keep :=
  (coherent_fold xs {} {} coherent_empty).2 n

private theorem keep_some {ci out : ConstantInfo} (h : keep ci = some out) : out = ci := by
  cases ci <;> simp [keep] at h <;> exact h.symm

/-- Derived lookup agreement: a kept record cannot shadow a different final
fallback winner. There is no injectivity, Nodup or code-invariant premise. -/
theorem collected_hybrid_get (xs : List (Name × ConstantInfo)) (n : Name) :
    ({ consts := (collect (xs.map fun p => rowOfCanonical p.1 p.2)).code
       fallback? := some (full xs).get? } : Ix.Environment).get? n = (full xs).get? n := by
  unfold Ix.Environment.get?
  rw [collect_code_get]
  simp only [Std.HashMap.get?_eq_getElem?]
  cases (full xs).consts[n]? with
  | none => simp
  | some ci =>
    simp only [Option.bind_some]
    cases kept : keep ci with
    | none => simp
    | some out => rw [keep_some kept]

/-- The exact single-row canonical producer, from any memo states. The full
chunk join/order and live loop replacement are separate remaining bridges. -/
theorem rowOfCanonical_canon (name : Lean.Name) (ci : Lean.ConstantInfo)
    (nameState constantState : Ix.CanonM.CanonState) :
    rowOfCanonical ((Ix.CanonM.canonName name).run nameState).1
      ((Ix.CanonM.canonConst ci).run constantState).1 =
      rowOfCanonical (Canon.nameS name) (Canon.constS ci) := by
  congr 1
  · exact Canon.canonName_run name nameState
  · exact Canon.canonConst_run ci constantState

end Ix.Cert.SourceGraph
