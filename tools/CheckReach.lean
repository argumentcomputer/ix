/-
Check reachability of named theorems from `compile_correct`.

For each candidate name, walks `compile_correct`'s transitive constant
closure and reports whether the candidate is reached. Handles mutual-block
peers by also checking auto-generated companions.

Run:
  cd /workspace/dev/lean/ix
  lake env lean tools/CheckReach.lean
-/
import Ix.Aiur

open Lean Elab Command

namespace Aiur.CheckReach

partial def collectUsed (env : Environment) (root : Name) : NameSet :=
  go ({} : NameSet) [root]
where
  go (acc : NameSet) : List Name → NameSet
    | [] => acc
    | n :: rest =>
      if acc.contains n then go acc rest
      else
        let acc := acc.insert n
        match env.find? n with
        | none => go acc rest
        | some info =>
          let cs : List Name :=
            match info.value? with
            | some e => e.foldConsts (init := []) (fun c xs => c :: xs)
            | none => []
          let typeCs : List Name :=
            info.type.foldConsts (init := []) (fun c xs => c :: xs)
          -- Mutual-block peers: ConstantInfo.all lists all simultaneously-defined
          -- names. Adding peers when ANY is reached captures mutual recursion.
          let peers : List Name := info.all
          go acc (cs ++ typeCs ++ peers ++ rest)

/-- Candidates: theorem names containing `sorry`. -/
def candidates : List Name := [
  -- A: compile_correct's direct entry-bridges
  `Aiur.Toplevel.concretize_produces_refClosed_entry,
  `Aiur.namespace_preservation_entry,
  `Aiur.concretize_preserves_function_kind_entry_wf,
  `Aiur.concretize_preserves_entry_inputs_wf,
  `Aiur.flatten_agree_entry,
  `Aiur.compile_ok_implies_struct_compatible_entry,
  -- B: Simulation leaves
  `Aiur.Simulation.ValueR_of_FnFree_at_entry,
  `Aiur.Simulation.step_R_preservation_applyGlobal,
  `Aiur.Simulation.ValueR_implies_flatten_eq,
  -- C: CompilerProgress entry-bridges
  `Aiur.concretize_produces_ctorPresent_entry,
  `Aiur.Lower.compile_progress_entry,
  -- D: hparamsEmpty bridge
  `Aiur.Toplevel.typedDecls_params_empty_universal_entry,
  -- E: concrete-side leaves
  `Aiur.Function_body_preservation_succ_fuel,
  `Aiur.FnFreeBody.interp_FnFree,
  `Aiur.concretizeBuild_preserves_TermRefsDt,
  -- F: dead (suspected orphan)
  `Aiur.concretize_preserves_runFunction,
  `Aiur.concretize_under_fullymono_dt_flat_size_agree,
  `Aiur.DirectDagBody.spine_transfer,
  `Aiur.concretize_extract_function_at_name,
  -- G: LowerCalleesFromLayout helpers
  `Aiur.term_compile_delta_letVar_match_continue,
  `Aiur.term_compile_delta_letWild_match_continue,
  -- New post-session candidates
  `Aiur.concretize_PendingArgsFO_bridge,
  `Aiur.concretize_preserves_TypesNotFunction,
  `Aiur.concretize_produces_ctorPresent_under_entry,
  `Aiur.concretize_extract_concF_at_reachable_wf,
  `Aiur.concretize_preserves_runFunction,
  `Aiur.concretize_under_fullymono_dt_flat_size_agree,
  `Aiur.DirectDagBody.spine_transfer,
  `Aiur.concretize_extract_function_at_name,
  -- TypesNotFunction helpers (must be reachable post-wiring)
  `Aiur.substInTypedTerm_preserves_TypesNotFunction,
  `Aiur.rewriteTypedTerm_preserves_TypesNotFunction,
  `Aiur.substInTypedTerm_typ,
  `Aiur.rewriteTypedTerm_typ,
  `Aiur.typToConcrete_preserves_NotFunction,
  `Aiur.Concrete.Typ.NotFunction_of_FirstOrder,
  `Aiur.concretizeBuild_function_origin_with_body,
  `Aiur.destructureTuple_typ,
  `Aiur.destructureArray_typ,
  `Aiur.concretizeBuild_preserves_TypesNotFunction,
  -- Audit candidates
  `Aiur.FnFreeBody.applyGlobal_FnFree,
  `Aiur.FnFreeBody.evalList_FnFree,
  `Aiur.FnFreeBody.evalMatchCases_FnFree,
  `Aiur.FnFreeBody.applyLocal_FnFree,
  `Aiur.FnFreeBody.runFunction_preserves_FnFree_body,
  `Aiur.Concrete.Eval.runFunction_preserves_FnFree,
  -- Wiring targets 2026-04-30
  `Aiur.runFunction_preserves_MonoCtorReach,
  `Aiur.concretizeBuild_preserves_ctor_kind_at_entry_fwd,
  `Aiur.typed_function_at_concrete_function_key_params_empty,
  `Aiur.dataTypeFlatSize_eq_layoutMap_size_wf,
  `Aiur.concretize_dataType_nameAgrees,
  `Aiur.concretize_dataType_srcStep_origin,
  `Aiur.concretize_dataType_ctor_argTypes_lenAgree,
  `Aiur.dataTypeFlatSizeBound_eq_sizeBound_wf,
  `Aiur.layoutMap_dataType_size_extract,
  `Aiur.RefClosedBody.DrainState.PendingArgsAppRefToDt.init,
  `Aiur.RefClosedBody.concretizeDrainEntry_preserves_PendingArgsAppRefToDt,
  -- MonoCtorReachBody granular leaves (decomposed from Sorry #1, 2026-05-04)
  `Aiur.MonoCtorReachBody.applyGlobal_MonoCtorReach,
  `Aiur.MonoCtorReachBody.applyLocal_MonoCtorReach,
  `Aiur.MonoCtorReachBody.interp_MonoCtorReach,
  `Aiur.MonoCtorReachBody.evalList_MonoCtorReach,
  `Aiur.MonoCtorReachBody.evalMatchCases_MonoCtorReach,
]

/-- Find all `Name`s in env whose mangled form ends with `..<core>`. Used to
discover the actual mangled form of a private theorem. -/
def findMangled (env : Environment) (core : Name) : List Name := Id.run do
  let coreStr := core.toString
  let mut hits : List Name := []
  for (n, _) in env.constants.toList do
    let s := n.toString
    if s == coreStr || s.endsWith ("." ++ coreStr) then
      hits := n :: hits
  hits

end Aiur.CheckReach

open Aiur.CheckReach in
#eval show CommandElabM Unit from do
  let env ← getEnv
  let used := collectUsed env `Aiur.Toplevel.compile_correct
  IO.println s!"# Reachability check from `Aiur.Toplevel.compile_correct`"
  IO.println ""
  IO.println s!"Closure size: {used.size} constants."
  IO.println ""
  IO.println "## Per-candidate reachability"
  IO.println ""
  for cand in candidates do
    let mangled := findMangled env cand
    let direct_reach := used.contains cand
    let any_mangled_reach := mangled.any (fun n => used.contains n)
    let status :=
      if direct_reach then "REACHED (direct)"
      else if any_mangled_reach then s!"REACHED (via mangled: {mangled.filter (fun n => used.contains n)})"
      else if mangled.isEmpty then "NOT FOUND in env"
      else s!"ORPHAN (mangled forms exist but unreached: {mangled.length} forms)"
    IO.println s!"- `{cand}` → {status}"
