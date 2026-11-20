import IxAICombined
open Lean in
partial def depClosure (env : Environment) (roots : List Name) : NameSet := Id.run do
  let mut seen : NameSet := {}
  let mut todo := roots
  while !todo.isEmpty do
    match todo with
    | [] => break
    | n :: rest =>
      todo := rest
      if seen.contains n then continue
      seen := seen.insert n
      if let some ci := env.find? n then
        for m in ci.getUsedConstantsAsSet.toList do
          unless seen.contains m do todo := m :: todo
  return seen
open Lean Elab Command in
#eval show CommandElabM Unit from do
  let env ← getEnv
  let names := env.allImportedModuleNames
  for roots in [[`IxAICombined.blockRun], [`IxAICombined.stepRun, `IxAICombined.blockRun, `IxAICombined.publish_sound, `IxAICombined.publish_confident, `IxAICombined.defer_iff], [`Aiur.Optimized.Physical.Prepared.depth_grouped_activated_native_heap_sound_goldilocks_observed], [`IxAICore.train]] do
    let s : NameSet := depClosure env roots
    let mods : List Name := s.toList.filterMap fun n => (env.getModuleIdxFor? n).map fun i => names[i.toNat]!
    let count (p : Name) : Nat := (mods.filter fun m => p.isPrefixOf m).length
    logInfo m!"{roots}: {s.size} constants; Mathlib {count `Mathlib}, Aiur {count `Aiur}, IxAIRefine {count `IxAIRefine}, Init {count `Init}, Std {count `Std}, Lean {count `Lean}"
