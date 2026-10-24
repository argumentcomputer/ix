import Ix.Compile.Pass.Driver
import Ix.Cert.Condense
import Ix.CompileCert.ImageShape

/-! # Provenance of the actual optimization hook

The engine's first successful branch retains every earlier miss, its exact
recursive callback and reports. The production hook derives its permission
and literal driver environment; no caller-supplied OptEnv or pass tag.
-/

namespace Ix.CompileCert.OptDispatchOrigin

open Ix (Name Expr ConstantInfo)
open Ix.CompileM Ix.Compile.Pass Ix.Compile.Pass.Opt
open Ix.Compile.ExactKey (ExactName)

/-- Exactly the callback installed by engineN, with its real predecessor fuel. -/
abbrev recur (fuel : Nat) (env : OptEnv) (o : Occ) : Option (Expr × Array String) :=
  (engineN fuel env o).map fun (_, e, reports) => (e, reports)

/-- The selected actual branch, including all first-success negatives. -/
inductive Branch (fuel : Nat) (env : OptEnv) (o : Occ) : String → Expr → Array String → Prop
  | o11a {out} (hit : O11a.apply env o = some out) : Branch fuel env o "O11a" out #[]
  | o2 {out reports} (miss11 : O11a.apply env o = none)
      (hit : O2.apply (recur fuel env) env o = some (out, reports)) :
      Branch fuel env o "O2" out (mergeDeclines (O11a.declineCause? env o).toArray reports)
  | o3 {out} (miss11 : O11a.apply env o = none)
      (miss2 : O2.apply (recur fuel env) env o = none) (hit : O3.apply env o = some out) :
      Branch fuel env o "O3" out (O11a.declineCause? env o).toArray
  | o4 {out} (miss11 : O11a.apply env o = none)
      (miss2 : O2.apply (recur fuel env) env o = none) (miss3 : O3.apply env o = none)
      (hit : O4.apply env o = some out) :
      Branch fuel env o "O4" out (O11a.declineCause? env o).toArray
  | o6 {out} (miss11 : O11a.apply env o = none)
      (miss2 : O2.apply (recur fuel env) env o = none) (miss3 : O3.apply env o = none)
      (miss4 : O4.apply env o = none) (hit : O6.apply env o = some out) :
      Branch fuel env o "O6" out (O11a.declineCause? env o).toArray

theorem engineN_origin {fuel : Nat} {env : OptEnv} {o : Occ} {tag : String}
    {out : Expr} {reports : Array String}
    (run : engineN (fuel + 1) env o = some (tag, out, reports)) : Branch fuel env o tag out reports := by
  cases first : O11a.apply env o with
  | some e =>
    simp [engineN, first] at run
    obtain ⟨rfl, rfl, rfl⟩ := run
    exact .o11a first
  | none =>
    cases second : O2.apply (recur fuel env) env o with
    | some result =>
      obtain ⟨e, rs⟩ := result
      simp [engineN, first, second] at run
      obtain ⟨rfl, rfl, rfl⟩ := run
      exact .o2 first second
    | none =>
      cases third : O3.apply env o with
      | some e =>
        simp [engineN, first, second, third] at run
        obtain ⟨rfl, rfl, rfl⟩ := run
        exact .o3 first second third
      | none =>
        cases fourth : O4.apply env o with
        | some e =>
          simp [engineN, first, second, third, fourth] at run
          obtain ⟨rfl, rfl, rfl⟩ := run
          exact .o4 first second third fourth
        | none =>
          cases fifth : O6.apply env o with
          | some e =>
            simp [engineN, first, second, third, fourth, fifth] at run
            obtain ⟨rfl, rfl, rfl⟩ := run
            exact .o6 first second third fourth fifth
          | none =>
            simp [engineN, first, second, third, fourth, fifth] at run

/-- A successful run cannot have exhausted its fuel. -/
theorem engineN_success_origin {n : Nat} {env : OptEnv} {o : Occ} {tag : String}
    {out : Expr} {reports : Array String} (run : engineN n env o = some (tag, out, reports)) :
    ∃ fuel, n = fuel + 1 ∧ Branch fuel env o tag out reports := by
  cases n with
  | zero => cases run
  | succ fuel => exact ⟨fuel, rfl, engineN_origin run⟩

/-- The production engine's callback fuel is literally63. -/
theorem engine_origin {env : OptEnv} {o : Occ} {tag : String} {out : Expr} {reports : Array String}
    (run : engine env o = some (tag, out, reports)) : Branch 63 env o tag out reports :=
  engineN_origin run

/-- The literal environment constructed by this passConfig/optLookup call. -/
def driverEnv (cenv : CompileEnv) (views : Std.HashMap ExactName BlockView)
    (sourceAll : Ix.Set Name) : OptEnv :=
  { ienv := cenv.env, resolves := fun n => (resolveAddr cenv n).isSome
    blockOf := fun h => (cenv.p3Heads.get? h).bind (optBlocks cenv views).get?
    rejectRef? := rejectO11aRef cenv (o11aBlockPlan cenv sourceAll) }

/-- The actual hook success recovers its discarded tag and every branch.
Permission, empty canonical outputs and absent proof tag are all derived. -/
theorem passConfig_origin {cenv : CompileEnv} {views : Std.HashMap ExactName BlockView}
    {sourceAll : Ix.Set Name} {site : Option Name} {n : Name} {us : Array Ix.Level} {args : Array Expr}
    {out : Expr} {constants : Array ConstantInfo} {proofTag : Option String} {reports : Array String}
    (hit : (passConfig cenv views sourceAll).opt? site n us args = some (out, constants, proofTag, reports)) :
    Ix.AuxGen.SourceIdentity.permitsOptimization cenv.env n = true ∧ constants = #[] ∧ proofTag = none ∧
    ∃ tag, engine (driverEnv cenv views sourceAll) { head := n, us, args, site } = some (tag, out, reports) ∧
      Branch 63 (driverEnv cenv views sourceAll) { head := n, us, args, site } tag out reports := by
  change (if !Ix.AuxGen.SourceIdentity.permitsOptimization cenv.env n then none else
    (engine (driverEnv cenv views sourceAll) { head := n, us, args, site }).map
      fun (_, e, rs) => (e, #[], none, rs)) = some (out, constants, proofTag, reports) at hit
  cases permitted : Ix.AuxGen.SourceIdentity.permitsOptimization cenv.env n with
  | false => simp only [permitted, Bool.not_false, ↓reduceIte] at hit; cases hit
  | true =>
    simp only [permitted, Bool.not_true] at hit
    cases ran : engine (driverEnv cenv views sourceAll) { head := n, us, args, site } with
    | none => simp only [ran, Option.map_none] at hit; cases hit
    | some result =>
      obtain ⟨tag, e, rs⟩ := result
      simp only [ran, Option.map_some] at hit
      obtain ⟨rfl, rfl, rfl, rfl⟩ := hit
      exact ⟨rfl, rfl, rfl, tag, rfl, engine_origin ran⟩

/-- The actual exact-key fold supplies its own view and computed block. -/
theorem optBlocks_origin {cenv : CompileEnv} {views : Std.HashMap ExactName BlockView}
    {key : ExactName} {block : OptBlock} (hit : (optBlocks cenv views).get? key = some block) :
    ∃ view, views.get? key = some view ∧ block = optBlockOf (viewInput cenv) view := by
  unfold optBlocks at hit
  rw [Std.HashMap.fold_eq_foldl_toList] at hit
  refine Ix.Cert.Condense.foldl_insert_get_of
    (P := fun k b => ∃ v, views.get? k = some v ∧ b = optBlockOf (viewInput cenv) v)
    (fun x : ExactName × BlockView => x.1) (fun x => optBlockOf (viewInput cenv) x.2)
    views.toList {} ?_ ?_ key block hit
  · intro k b impossible
    simp at impossible
  · intro x member k same
    exact ⟨x.2, Ix.Cert.Condense.get_of_mem_toList member same, rfl⟩

/-- Invert the actual O6 calls without selecting rec over recOn or inferring
an occurrence universe count from the shape's O5 guard. -/
theorem o6_lookup_origin {env : OptEnv} {o : Occ} {out : Expr}
    (run : O6.apply env o = some out) :
    ∃ k r block s count levels,
      classify o.head = some (k, r) ∧ (k = .kRec ∨ k = .kRecOn) ∧
      env.blockOf o.head = some block ∧ block.shapes.get? r = some s ∧
      s.isSelection = true ∧ standardTelescope env s k o.head = some count ∧
      count ≤ o.args.size ∧ O5.levels s o.us = some levels := by
  unfold O6.apply at run
  obtain ⟨⟨k, r⟩, kind, run⟩ := ImageShape.bind_some run
  dsimp only at run
  split at run
  · cases run
  · rename_i allowed
    have kinds : k = .kRec ∨ k = .kRecOn := by
      cases k <;> first | exact Or.inl rfl | exact Or.inr rfl | exact (allowed rfl).elim
    obtain ⟨block, blockHit, run⟩ := ImageShape.bind_some run
    obtain ⟨s, shapeHit, run⟩ := ImageShape.bind_some run
    split at run
    · cases run
    · rename_i selected
      have selection : s.isSelection = true := by simpa using selected
      obtain ⟨count, telescope, run⟩ := ImageShape.bind_some run
      split at run
      · cases run
      · rename_i enough
        obtain ⟨levels, levelRun, _⟩ := ImageShape.bind_some run
        exact ⟨k, r, block, s, count, levels, kind, kinds, blockHit, shapeHit,
          selection, telescope, Nat.le_of_not_gt enough, levelRun⟩

/-- Operational O6 provenance at the actual driver snapshot. The view hit
is NOT a fresh buildView result; the shape hit is NOT an image-origin law. -/
def O6Calls (cenv : CompileEnv) (views : Std.HashMap ExactName BlockView)
    (sourceAll : Ix.Set Name) (o : Occ) (out : Expr) : Prop :=
  O6.apply (driverEnv cenv views sourceAll) o = some out ∧
  ∃ (k : AuxKind) (r key : Name) (view : BlockView) (block : OptBlock) (s : RecShape)
    (count : Nat) (levels : Array Ix.Level),
    classify o.head = some (k, r) ∧ (k = .kRec ∨ k = .kRecOn) ∧
    cenv.p3Heads.get? o.head = some key ∧ views.get? key = some view ∧
    (optBlocks cenv views).get? key = some block ∧ block = optBlockOf (viewInput cenv) view ∧
    (driverEnv cenv views sourceAll).blockOf o.head = some block ∧ block.shapes.get? r = some s ∧
    s.isSelection = true ∧ standardTelescope (driverEnv cenv views sourceAll) s k o.head = some count ∧
    count ≤ o.args.size ∧ O5.levels s o.us = some levels

theorem driver_o6_origin {cenv : CompileEnv} {views : Std.HashMap ExactName BlockView}
    {sourceAll : Ix.Set Name} {o : Occ} {out : Expr}
    (run : O6.apply (driverEnv cenv views sourceAll) o = some out) :
    O6Calls cenv views sourceAll o out := by
  obtain ⟨k, r, block, s, count, levels, kind, kinds, blockHit, shapeHit,
      selection, telescope, enough, levelRun⟩ := o6_lookup_origin run
  have actualBlock := blockHit
  change ((cenv.p3Heads.get? o.head).bind (optBlocks cenv views).get?) = some block at actualBlock
  obtain ⟨key, owner, storedBlock⟩ := ImageShape.bind_some actualBlock
  obtain ⟨view, storedView, blockEq⟩ := optBlocks_origin storedBlock
  exact ⟨run, k, r, key, view, block, s, count, levels, kind, kinds, owner, storedView,
    storedBlock, blockEq, blockHit, shapeHit, selection, telescope, enough, levelRun⟩

/-- An actual hook result retains EVERY branch, and its recovered O6 branch
supplies all driver/map/call provenance. No O6 tag is a caller premise. -/
theorem passConfig_with_o6_origin {cenv : CompileEnv} {views : Std.HashMap ExactName BlockView}
    {sourceAll : Ix.Set Name} {site : Option Name} {n : Name} {us : Array Ix.Level} {args : Array Expr}
    {out : Expr} {constants : Array ConstantInfo} {proofTag : Option String} {reports : Array String}
    (hit : (passConfig cenv views sourceAll).opt? site n us args = some (out, constants, proofTag, reports)) :
    Ix.AuxGen.SourceIdentity.permitsOptimization cenv.env n = true ∧ constants = #[] ∧ proofTag = none ∧
    ∃ tag, engine (driverEnv cenv views sourceAll) { head := n, us, args, site } = some (tag, out, reports) ∧
      Branch 63 (driverEnv cenv views sourceAll) { head := n, us, args, site } tag out reports ∧
      (tag = "O6" → O6Calls cenv views sourceAll { head := n, us, args, site } out) := by
  obtain ⟨permitted, empty, noProof, tag, ran, branch⟩ := passConfig_origin hit
  refine ⟨permitted, empty, noProof, tag, ran, branch, ?_⟩
  intro selected
  cases branch with
  | o11a => simp at selected
  | o2 => simp at selected
  | o3 => simp at selected
  | o4 => simp at selected
  | o6 _ _ _ _ pass => exact driver_o6_origin pass

end Ix.CompileCert.OptDispatchOrigin
