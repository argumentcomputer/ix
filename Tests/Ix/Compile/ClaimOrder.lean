import Tests.Ix.Compile.ClaimConflict
import Tests.Ix.Compile.Mutual

open Lean

namespace Tests.Ix.Compile.ClaimOrder

inductive Owner where
  | stop : Owner
  | next : Owner → Owner

def unrelated : Type := PUnit

/-- No source dependency relates the custom helper to Owner. The only added
edge is a test scheduler constraint, varied in both directions. Source
provenance is independent of arrival order; generated support uses a private
identity so both orders preserve the source definition and compile equally. -/
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
  let nameByHash := phases.rawEnv.consts.fold
    (fun names name _ => names.insert name.getHash name) ({} : Std.HashMap Address Ix.Name)
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
  -- Neither order may reject valid source or let a generated helper replace
  -- it. Compare full output, not just matching refusal sets.
  do
    let mode := "pass3"
    let mut reference : Option ByteArray := none
    for ownerFirst in [false, true] do
      let before := if ownerFirst then ownerIx else fakeIx
      let after := if ownerFirst then fakeIx else ownerIx
      let some afterLo := phases.condensed.lowLinks.get? after
        | throw (IO.userError s!"claim-order fixture has no block for {after.pretty}")
      let blockRefs := phases.condensed.blockRefs.insert afterLo
        ((phases.condensed.blockRefs.getD afterLo {}).insert before)
      let blocks := { phases.condensed with blockRefs := blockRefs }
      let .ok (output, _, cenv) := Ix.CompileM.compileEnvAux phases.rawEnv blocks
          (nameByHash := nameByHash)
        | throw (IO.userError s!"claim-order scheduler failed ({mode})")
      let refused := ClaimConflict.sorted (cenv.ungrounded.toList.map fun (n, why) => (n.pretty, why))
      let label := s!"{if ownerFirst then "owner-first" else "user-first"} ({mode})"
      IO.println s!"[claim-order] {label}: {refused.length} refusals, roots {(refused.filter fun (_, m) => !(m.startsWith "missing")).map (·.1)}"
      unless refused.isEmpty do
        throw (IO.userError s!"{label}: valid source declarations refused: {refused}")
      for (name, _) in input do
        unless output.named.contains (Ix.Name.fromLeanName name) do
          throw (IO.userError s!"{label}: source declaration missing: {name}")
      let generatedIx := ownerIx.mkStr "_ix" |>.mkStr "below"
      let some source := output.getNamed? fakeIx | throw (IO.userError s!"{label}: source below missing")
      let some generated := output.getNamed? generatedIx | throw (IO.userError s!"{label}: private below missing")
      unless source.addr != generated.addr do
        throw (IO.userError s!"{label}: generated helper replaced the source definition")
      let (recovered, errors, _) ← Ix.DecompileM.decompileEnvFullParallel output
        (some phases.rawEnv.consts)
      unless errors.isEmpty && recovered.size == phases.rawEnv.consts.size &&
          phases.rawEnv.consts.toArray.all (fun (name, ci) => recovered.get? name == some ci) do
        throw (IO.userError s!"{label}: source round-trip differs")
      let bytes ← IO.ofExcept (Ixon.serEnv output)
      match reference with
      | none => reference := some bytes
      | some prior => unless bytes == prior do
        failures := failures + 1
        IO.println s!"[claim-order] FAIL changing only ready order changed output bytes ({mode})"
      IO.println s!"[claim-order] {label}: every source name preserved; distinct private below; exact source round-trip"
  -- Real split/nested aliases, including a source-owned helper whose
  -- compiled content equals an unrelated external container recursor.
  let fixturePrefixes := [`Tests.Ix.Compile.Mutual.AuxOwnership.Evap,
    `Tests.Ix.Compile.Mutual.AuxOwnership.SplitSpecs]
  let seeds := env.constants.toList.filterMap fun (name, _) =>
    if fixturePrefixes.any (·.isPrefixOf name) then some name else none
  if seeds.isEmpty then throw (IO.userError "claim-order positive fixture set is empty")
  let positive ← Ix.CompileM.rsCompilePhasesOf (Ix.EnvScope.collectSelectedDeps env seeds)
  let externalRec := Ix.Name.fromLeanName `List.rec
  let evapPrefix := "Tests.Ix.Compile.Mutual.AuxOwnership.Evap."
  do
    let mode := "pass3"
    let .ok (output, _, positiveEnv) := Ix.CompileM.compileEnvAux positive.rawEnv positive.condensed
      | throw (IO.userError s!"claim-order positive scheduler failed ({mode})")
    for (name, why) in positiveEnv.ungrounded.toList do
      failures := failures + 1
      IO.println s!"[claim-order] FAIL legitimate source claim {name.pretty} ({mode}): {why}"
    match output.named[externalRec]? with
    | none =>
      failures := failures + 1
      IO.println s!"[claim-order] FAIL evaporation control: List.rec missing ({mode})"
    | some target =>
      -- the source-owned names of the fixture that share `List.rec`'s content
      let sharing := output.named.fold (init := #[]) fun acc n e =>
        if n != externalRec && n.pretty.startsWith evapPrefix && e.addr == target.addr then
          acc.push n.pretty else acc
      IO.println s!"[claim-order] evaporation control ({mode}): {sharing.size} source-owned \
name(s) at List.rec's address: {sharing}"
      -- Pass 3 stores the evaporated nested recursor under its `_ix` display name
      -- (D14) and the Lean name holds its image (the legacy surgery, deleted at
      -- M6R slice 6, kept it under its Lean name)
      let ixAlias := Ix.Name.fromLeanName `Tests.Ix.Compile.Mutual.AuxOwnership.Evap.M._ix.rec_2
      let exact := sharing.size == 1 && (output.named[ixAlias]?.map
          (·.addr == target.addr)).getD false
      unless exact do
        failures := failures + 1
        IO.println s!"[claim-order] FAIL evaporation control no longer shares List.rec content ({mode})"
  return if failures == 0 then 0 else 1

end Tests.Ix.Compile.ClaimOrder
