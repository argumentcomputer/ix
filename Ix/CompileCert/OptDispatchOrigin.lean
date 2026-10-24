import Ix.Compile.Pass.Driver

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

end Ix.CompileCert.OptDispatchOrigin
