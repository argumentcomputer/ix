import Tests.Ix.Compile.ClaimConflict
import Tests.Ix.Compile.Mutual

open Lean

namespace Tests.Ix.Compile.ClaimOrder

inductive Owner where
  | stop : Owner
  | next : Owner → Owner

def unrelated : Type := PUnit

/-- No source dependency relates the fake helper to Owner. The only added
edge is a test scheduler constraint, varied in both directions. Ownership
must come from the source declaration, not this arrival order or its address. -/
def run : IO UInt32 := do
  let env ← get_env!
  let owner := ``Owner
  let fake := owner ++ `below
  let some (.defnInfo original) := env.find? ``unrelated
    | throw (IO.userError "claim-order fixture missing")
  let input := Ix.EnvScope.collectSelectedDeps env
    ([owner, owner ++ `rec] ++ ClaimConflict.auxSeeds)
  let input := (fake, ConstantInfo.defnInfo { original with name := fake, all := [fake] }) ::
    input.filter (fun (n, _) => n != fake && n != ``unrelated)
  let phases ← Ix.CompileM.rsCompilePhasesOf input
  let ownerIx := Ix.Name.fromLeanName owner
  let fakeIx := Ix.Name.fromLeanName fake
  let mut failures := 0
  -- Evaporation can erase every type/rule mention of the source parent.
  -- Its recursor's explicit source-family metadata still owns the claim.
  let some (.recInfo sourceRec) := phases.rawEnv.get? (Ix.Name.fromLeanName (owner ++ `rec))
    | throw (IO.userError "claim-order source recursor missing")
  let sourceAliasName := Ix.Name.fromLeanName (owner ++ `rec_1)
  let foreign := Ix.Name.fromLeanName `List.rec
  let makeRec := fun name all =>
    let cnst := { sourceRec.cnst with name := name, type := Ix.Expr.mkSort Ix.Level.mkZero }
    Ix.ConstantInfo.recInfo { sourceRec with cnst := cnst, all := all, rules := #[] }
  let provenanceConsts := phases.rawEnv.consts.insert sourceAliasName (makeRec sourceAliasName #[ownerIx])
  let provenanceConsts := provenanceConsts.insert foreign (makeRec foreign #[Ix.Name.fromLeanName `List])
  let provenanceEnv := { phases.rawEnv with consts := provenanceConsts }
  let owners := ({} : Std.HashSet Ix.Name).insert ownerIx
  for (name, expected) in [(sourceAliasName, true), (foreign, false), (fakeIx, false)] do
    let result := Ix.AuxGen.sourceClaimOwned provenanceEnv owners name provenanceEnv.consts.size
    unless result.toOption == some expected do
      failures := failures + 1
      IO.println s!"[claim-order] FAIL source-family provenance {name.pretty}: {result}"
  let mut reference : Option (List (String × String)) := none
  for ownerFirst in [false, true] do
    let before := if ownerFirst then ownerIx else fakeIx
    let after := if ownerFirst then fakeIx else ownerIx
    let some afterLo := phases.condensed.lowLinks.get? after
      | throw (IO.userError s!"claim-order fixture has no block for {after.pretty}")
    let blockRefs := phases.condensed.blockRefs.insert afterLo
      ((phases.condensed.blockRefs.getD afterLo {}).insert before)
    let blocks := { phases.condensed with blockRefs := blockRefs }
    let .ok (_, _, cenv) := Ix.CompileM.compileEnvAux phases.rawEnv blocks
      | throw (IO.userError "claim-order scheduler failed")
    let refused := ClaimConflict.sorted (cenv.ungrounded.toList.map fun (n, why) => (n.pretty, why))
    let label := if ownerFirst then "owner-first" else "user-first"
    IO.println s!"[claim-order] {label}: {refused}"
    unless cenv.ungrounded.contains ownerIx do
      failures := failures + 1
      IO.println s!"[claim-order] FAIL {label}: owner silently claimed an unrelated source name"
    if cenv.ungrounded.contains fakeIx then
      failures := failures + 1
      IO.println s!"[claim-order] FAIL {label}: unrelated source declaration was refused"
    match reference with
    | none => reference := some refused
    | some prior => unless refused == prior do
      failures := failures + 1
      IO.println "[claim-order] FAIL changing only ready order changed refusals"
  -- Real split/nested aliases, including a source-owned helper whose
  -- compiled content equals an unrelated external container recursor.
  let fixturePrefixes := [`Tests.Ix.Compile.Mutual.AuxOwnership.Evap,
    `Tests.Ix.Compile.Mutual.AuxOwnership.SplitSpecs]
  let seeds := env.constants.toList.filterMap fun (name, _) =>
    if fixturePrefixes.any (·.isPrefixOf name) then some name else none
  if seeds.isEmpty then throw (IO.userError "claim-order positive fixture set is empty")
  let positive ← Ix.CompileM.rsCompilePhasesOf (Ix.EnvScope.collectSelectedDeps env seeds)
  let .ok (output, _, positiveEnv) := Ix.CompileM.compileEnvAux positive.rawEnv positive.condensed
    | throw (IO.userError "claim-order positive scheduler failed")
  for (name, why) in positiveEnv.ungrounded.toList do
    failures := failures + 1
    IO.println s!"[claim-order] FAIL legitimate source claim {name.pretty}: {why}"
  let sourceAlias := Ix.Name.fromLeanName `Tests.Ix.Compile.Mutual.AuxOwnership.Evap.M.rec_2
  let externalRec := Ix.Name.fromLeanName `List.rec
  match output.named[sourceAlias]?, output.named[externalRec]? with
  | some source, some target => unless source.addr == target.addr do
      failures := failures + 1
      IO.println "[claim-order] FAIL evaporation control no longer shares List.rec content"
  | _, _ =>
    failures := failures + 1
    IO.println "[claim-order] FAIL evaporation control source or target missing"
  return if failures == 0 then 0 else 1

end Tests.Ix.Compile.ClaimOrder
