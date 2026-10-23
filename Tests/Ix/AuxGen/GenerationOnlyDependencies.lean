import Tests.Ix.AuxGen.GenerationOnlyFactory
import Tests.Ix.AuxGen.GenerationOnlyAliases
import Tests.Ix.AuxGen.GenerationOnlyOpaques
import Tests.Ix.Compile.AuxGenDiff
import Tests.Ix.IxVM
import Tests.Ix.Fixtures
import Lean.Elab.Command

namespace Tests.Ix.AuxGen.GenerationOnlyDependencies
open _root_.Ix _root_.Ix.AuxGen
open Tests.Ix.AuxGen.GenerationOnlySpike (runTail sameTail)

deriving instance BEq for Ix.Compile.Pass.Clique.Decl,
  Ix.Compile.Pass.Clique.CliquePlan, Ix.Compile.Pass.Clique.CliqueOutcome,
  BlockReport, CompileM.MetaRefTable, CompileM.BlockState, CompileM.BlockResult,
  Ix.Compile.OriginalData.Receipt, Ix.Compile.Pass.Published

-- Explicit test-only access, with exact unique private-name matching. No
-- constructor, environment or guard hook is added to the production API.
run_cmd do
  let env ← Lean.getEnv
  for (suffix, aliasName) in #[("sealCharDelta", `sealForTest), ("actualGroup", `groupOf), ("refsOf", `refs),
      ("Context", `Ctx), ("Context.mk", `context), ("prepare", `prepareDeps),
      ("checkedCharUnit", `charUnit), ("Context.baseline", `baseline)] do
    let names := env.constants.fold (init := (#[] : Array Lean.Name)) fun acc n _ =>
      if n.toString.startsWith "_private.Ix.AuxGen.GenerationOnly." &&
          n.toString.endsWith (".Ix.AuxGen.GenerationOnly." ++ suffix) then acc.push n else acc
    unless names.size == 1 do throwError "private test alias {suffix}: {names}"
    Lean.Elab.Command.elabCommand (← `(abbrev $(Lean.mkIdent aliasName) := $(Lean.mkIdent names[0]!)))

private def need (ok : Bool) (why : String) : IO Unit := unless ok do throw (IO.userError why)
private def refused (label : String) (r : Except String α) (want : String) : IO Unit := do
  match r with
  | .ok _ => throw (IO.userError s!"{label}: unexpectedly succeeded")
  | .error e => need (e == want) s!"{label}: wrong error {e}"

private def replace (s : Source.Service) (n : Name) (ci : Option ConstantInfo) : Source.Service :=
  let look k := if Name.beqRaw k n then ci else s.input.get? k
  { s with input := { s.input with get? := look } }

private def charContext (svc : Source.Service) : Except String Ctx := do
  let some why := Ixc.blockStatus? svc #[Name.fromLeanName `IxVMInd.AuxTie] | throw "owner accepted"
  let group ← groupOf svc.input (Name.fromLeanName `Char)
  let mut g := context svc svc.env.tier svc.env.sigma why
  for n in (refs group).toArray.qsort (fun a b => Ix.LeanIngress.nameCmp a b == .lt) do
    if group.names.any (Name.beqRaw · n) then continue
    g ← prepareDeps 256 g group.names n
  return g

private def controls (base : Source.Service) : IO Unit := do
  let owner := Name.fromLeanName `IxVMInd.AuxTie
  let char := Name.fromLeanName `Char
  let svc := base.ensureNames #[owner]
  let some why := Ixc.blockStatus? svc #[owner] | throw (IO.userError "owner accepted")
  let initial := context svc svc.env.tier svc.env.sigma why
  refused "depth" (prepareDeps 0 initial #[] owner) s!"generation: dependency depth exhausted at {owner.pretty}"
  refused "cycle" (prepareDeps 1 initial #[owner] owner) s!"generation: dependency cycle at {owner.pretty}"
  let g ← IO.ofExcept (charContext svc)
  need ((baseline g).entries.map (·.status) == svc.entries.map (·.status) &&
    decide ((baseline g).env.fold.fe.env.consts = svc.env.fold.fe.env.consts)) "preparation changed original baseline"
  let (old, checked) ← IO.ofExcept (charUnit g)
  let entry ← IO.ofExcept (sealForTest old checked)
  need (entry.stage == 2 && entry.check.all (fun | .indInfo _ c => decide (c = {}) | .recInfo _ _ _ rs => rs.isEmpty | _ => true)) "check view retained capabilities/rules"
  let .infos answers := entry.answer | throw (IO.userError "answer view kind differs")
  need (answers.any (fun | .recInfo _ _ _ rs => rs.length == 1 | _ => false)) "answer view lost rule"
  let withChar ← IO.ofExcept (prepareDeps 256 g #[] char)
  refused "role collision" (charUnit withChar) "Char adapter: role/key collision"
  let some first := checked.env.consts.head? | throw (IO.userError "delta missing")
  let some oldFirst := old.env.consts.head? | throw (IO.userError "old index empty")
  let make xs := Ix.Kernel.mkFEnv { consts := xs }
  let extra := Ix.Kernel.ConstantInfo.indInfo { name := .aux (.role .char) .model, levelParams := [], type := .sort (.succ .zero) } {}
  refused "extra" (sealForTest old (make (extra :: checked.env.consts))) "Char adapter: extra/overwritten entry or nonexact old suffix"
  refused "duplicate" (sealForTest old (make ([first, first] ++ (checked.env.consts.take 4).drop 2 ++ old.env.consts))) "Char adapter: duplicate/unexpected/missing delta key"
  refused "generated extra" (sealForTest old (make (extra :: checked.env.consts.tail))) "Char adapter: duplicate/unexpected/missing delta key"
  let overwritten := Ix.Kernel.ConstantInfo.axiomInfo { oldFirst.toConstantVal with type := .sort .zero }
  refused "old overwrite" (sealForTest old (make (checked.env.consts.take 4 ++ overwritten :: old.env.consts.tail))) "Char adapter: extra/overwritten entry or nonexact old suffix"
  let wrong := (checked.env.consts.take 4).map fun ci => if ci.name == .role .char then .axiomInfo ci.toConstantVal else ci
  refused "axiom delta" (sealForTest old (make (wrong ++ old.env.consts))) "Char adapter: wrong delta record kind"
  let some (.inductive ts cs rs) := svc.input.blockGroupOf? char | throw (IO.userError "Char group missing")
  let some t := ts[0]? | throw (IO.userError "Char former missing")
  let some c := cs.flatten[0]? | throw (IO.userError "Char ctor missing")
  let some r := rs[0]? | throw (IO.userError "Char rec missing")
  let factory s := GenerationOnly.ofService s owner
  let badT := { t with cnst := { t.cnst with type := Expr.mkSort (Level.mkSucc (Level.mkSucc Level.mkZero)) } }
  refused "former" (factory (replace svc char (some (.inductInfo badT)))) "Char adapter: anchor header mismatch"
  let badC := { c with cnst := { c.cnst with type := Expr.mkLit (.natVal 0) } }
  refused "ctor" (factory (replace svc c.cnst.name (some (.ctorInfo badC)))) "Char adapter: conversion: ingress: malformed: constructor Char.mk declares 2 fields at 0 parameters; its type has 0 binders"
  let badR := { r with rules := r.rules.modify 0 fun ru => { ru with rhs := Expr.mkLit (.natVal 7) } }
  refused "rec rule" (factory (replace svc r.cnst.name (some (.recInfo badR)))) "Char adapter: complete check: invalid: direct rec: recursor rules are not the generated ones"
  let extract s := groupOf s.input char
  refused "missing ctor" (extract (replace svc c.cnst.name none)) "generation: missing constructor Char.mk"
  refused "unsafe former" (extract (replace svc char (some (.inductInfo { t with isUnsafe := true })))) "generation: unsafe supplied former Char"
  refused "unsafe ctor" (extract (replace svc c.cnst.name (some (.ctorInfo { c with isUnsafe := true })))) "generation: unsafe supplied constructor Char.mk"
  refused "unsafe rec" (extract (replace svc r.cnst.name (some (.recInfo { r with isUnsafe := true })))) "generation: unsafe supplied recursor Char.rec"
  let other := Name.fromLeanName `Nat
  refused "rec family" (extract (replace svc r.cnst.name (some (.recInfo { r with all := #[other] })))) "generation: supplied recursor family/name differs at Char.rec"
  let misnamed := { r with cnst := { r.cnst with name := r.cnst.name.mkStr "wrong" } }
  refused "rec name" (extract (replace svc r.cnst.name (some (.recInfo misnamed)))) "generation: supplied recursor family/name differs at Char.rec"
  let wrongRec := ConstantInfo.axiomInfo { cnst := r.cnst, isUnsafe := false }
  refused "rec kind" (extract (replace svc r.cnst.name (some wrongRec))) "generation: supplied recursor slot has another kind at Char.rec"
  let existsName := Name.fromLeanName `Exists
  let .inductive _ _ absent ← IO.ofExcept (groupOf svc.input existsName) | throw (IO.userError "Exists not inductive")
  need absent.isEmpty "actual recordless Exists changed"
  let dn := Name.fromLeanName `List.instMembership
  let some (.defnInfo dv) := svc.input.get? dn | throw (IO.userError "definition fixture missing")
  -- Safe opaques with the supplied body are now an intentionally supported
  -- private generation input. Full-body/opacity negatives run in Opaques.
  let opaqueVariant := ConstantInfo.opaqueInfo ⟨dv.cnst, dv.value, false, dv.all⟩
  let .definitions #[.opaqueInfo actual] ← IO.ofExcept (groupOf (replace svc dn (some opaqueVariant)).input dn)
    | throw (IO.userError "valid safe opaque was not extracted intact")
  need (actual.cnst == dv.cnst && actual.value == dv.value && !actual.isUnsafe) "opaque extraction changed supplied data"
  let unsupported := #[ConstantInfo.axiomInfo ⟨dv.cnst, false⟩, .thmInfo ⟨dv.cnst, dv.value, dv.all⟩]
  for ci in unsupported do
    refused "unsupported dependency" (groupOf (replace svc dn (some ci)).input dn) s!"generation: unsupported supplied dependency {dn.pretty}"
  refused "unsafe definition" (groupOf (replace svc dn (some (.defnInfo { dv with safety := .unsafe }))).input dn) s!"generation: non-safe definition unit member {dn.pretty}"
  let some lo := svc.input.blocks.lowLinks.get? dn | throw (IO.userError "definition unit missing")
  let some members := svc.input.blocks.blocks.get? lo | throw (IO.userError "definition members missing")
  let missing := dn.mkStr "missing"
  let incomplete : Source.Input := { svc.input with blocks := { svc.input.blocks with blocks := svc.input.blocks.blocks.insert lo (members.insert missing) } }
  refused "incomplete unit" (groupOf incomplete dn) s!"generation: missing or non-definition unit member {missing.pretty}"
  let mixed := { svc.input with blocks := { svc.input.blocks with blocks := svc.input.blocks.blocks.insert lo (members.insert char) } }
  refused "mixed unit" (groupOf mixed dn) "generation: missing or non-definition unit member Char"
  let unavailable := (replace svc dn none).input
  refused "missing record" (groupOf unavailable dn) s!"generation: missing input record {dn.pretty}"
  let vr := Name.fromLeanName `Tests.Ix.Compile.Mutual.NestedPredicate.VR
  let vs := base.ensureNames #[vr]
  let fn := Name.fromLeanName `Tests.Ix.Compile.Mutual.NestedPredicate.CtorInfo.ofKey
  let some (.defnInfo original) := vs.input.get? fn | throw (IO.userError "ofKey fixture missing")
  let absent := fn.mkStr "unresolved_generation_dependency"
  let broken := replace vs fn (some (.defnInfo { original with value := Expr.mkConst absent #[] }))
  match GenerationOnly.ofService broken vr with
  | .ok _ => throw (IO.userError "unresolved input reference was allowed")
  | .error e => need (e == s!"invalid: unknown constant in value of {fn.pretty}") s!"wrong unresolved-reference cause: {e}"
  let accepted := base.ensureNames #[Name.fromLeanName `Nat]
  refused "accepted owner" (GenerationOnly.ofService accepted (Name.fromLeanName `Nat)) "generation: Source-accepted block is ineligible"
  let o ← IO.ofExcept (factory svc)
  let aliasName := char.mkStr "_production_generation_alias"
  let (after, ok, bad) ← IO.ofExcept (o.admitBelow #[⟨aliasName, r.cnst.levelParams, r.cnst.type, Expr.mkConst r.cnst.name (r.cnst.levelParams.map Level.mkParam), false⟩])
  need (ok == 1 && bad == 0 && after.mode == .failClosed && after.recursors && after.retry.isNone && after.blockStatus () == some why) "callback changed policy"
  IO.println "production dependency controls: exact extraction/delta/cycle/depth failures; stage separation and immutable baseline; checked-role callback remains failClosed"

private def targets : Array String := #["Exists.intro", "Tests.Ix.Compile.Mutual.NestedPredicate.E.node",
  "_private.Tests.Ix.Compile.Canonicity.0.Tests.Ix.Compile.Canonicity.ZFA.Lists.Equiv.antisymm",
  "_private.Tests.Ix.Compile.Canonicity.0.Tests.Ix.Compile.Canonicity.ZFA3.Lists'.Subset.nil",
  "_private.Tests.Ix.Compile.Canonicity.0.Tests.Ix.Compile.Canonicity.ZFA5.Lists.Equiv.antisymm",
  "_private.Tests.Ix.Compile.Canonicity.0.Tests.Ix.Compile.Canonicity.ZFA4.Lists'.Subset.cons",
  "_private.Tests.Ix.Compile.Canonicity.0.Tests.Ix.Compile.Canonicity.ZFA2.Lists'.Subset.cons",
  "Tests.Ix.Compile.Mutual.NestedPredicate.VR.con", "IxVMInd.AuxTie.c"]

def evaluate (factoryControls : Bool := true) : IO Unit := do
  if factoryControls then
    GenerationOnlyAliases.evaluate
    GenerationOnlyOpaques.evaluate
    GenerationOnlyFactory.evaluate
  let leanEnv ← getCompileEnv #[`Tests.Ix.Compile.ValidateAux, `Tests.Ix.IxVM, `Tests.Ix.Fixtures]
  let filtered := validateAuxClosure leanEnv
  let raw ← CompileM.rsCompilePhasesFFI filtered
  let env := raw.rawEnv.toEnvironment
  let blocks := raw.condensed.toCondensedBlocks
  let compiled := raw.compileEnv.toEnv
  let cenv := Tests.Compile.AuxGenDiff.seedBlockRegistry (Ix.Commit.mkCompileEnv { rawEnv := env, condensed := blocks, compileEnv := compiled }) blocks
  let opts : CompileM.AuxIxcOptions := {}
  let ra := Source.RunAhead.start env.get? blocks (CompileM.scheduleLevels blocks (CompileM.FoldSchedule.of blocks)) opts.asks
  let cenv := opts.withSourceProviders env.get? blocks ra cenv
  let pre ← IO.ofExcept (Ix.Kernel.Reader.builtinPrelude.mapError IO.userError)
  let base := Source.Service.create pre env blocks (evidence := some (Ix.RoleEvidence.bundleEvidence ()))
  IO.println s!"production raw input: {filtered.length} constants, {blocks.blocks.size} blocks, {compiled.named.size} named surroundings"
  if factoryControls then controls base
  let mut count := 0
  for label in targets do
    let choices := blocks.blocks.toArray.filter (fun (_, ms) => ms.toArray.any (·.pretty == label))
    need (choices.size == 1) s!"missing/ambiguous target {label}"
    let some (lo, ms) := choices[0]? | throw (IO.userError "target missing")
    let lo := CompileM.blockKey lo ms
    let members := ms.toArray.qsort (fun a b => Ix.LeanIngress.nameCmp a b == .lt)
    let svc := base.ensureNames members
    let some why := Ixc.blockStatus? svc members | throw (IO.userError "target unexpectedly accepted")
    let original mode := Ixc.oracleOf mode false { members, recursors := true, lookup := env.get? } none 8 (fun _ => .ok svc)
    let expected ← IO.ofExcept (← IO.lazyPure fun _ => runTail cenv lo members (original .fallback))
    let some provider := cenv.auxGenerationRetry | throw (IO.userError "driver provider absent")
    let actual ← IO.ofExcept (provider lo)
    need (actual.mode == .failClosed && actual.recursors && actual.retry.isNone && actual.blockStatus () == some why) "factory policy changed"
    let some ordinary := cenv.auxOracle.bind (· lo) | throw (IO.userError "driver oracle absent")
    need ordinary.retry.isNone "production retained legacy retry"
    let observed ← IO.ofExcept (← IO.lazyPure fun _ => runTail cenv lo members ordinary true)
    let direct ← IO.ofExcept (← IO.lazyPure fun _ => runTail cenv lo members actual)
    need ({ observed.2 with auxReport := { observed.2.auxReport with retried := none } } == direct.2) s!"whole BlockState rollback changed: {label}"
    need (sameTail expected observed) s!"output changed: {label}"
    need (observed.2.auxReport.retried == some why && observed.1.2.admitted.size == observed.1.2.generated.size &&
      observed.1.2.admitted.all (fun (_, v) => v == .exempt s!"{AuxTable.notAcceptedPrefix}{why}")) s!"exemption/retry changed: {label}"
    need (observed.1.2.scopeEpoch == 0 && observed.1.2.ingressCache.isEmpty && observed.1.2.auxIngressSeen.isEmpty &&
      observed.1.2.sourceNames.isEmpty && observed.1.2.tcState.env.consts.isEmpty) s!"legacy activity: {label}"
    let full ← IO.ofExcept ((← IO.lazyPure fun _ => CompileM.runBlockWithAux cenv ms lo).mapError toString)
    let reference ← IO.ofExcept ((← IO.lazyPure fun _ => CompileM.runBlockWithAux
      { cenv with auxOracle := some (fun _ => some (original .fallback)) } ms lo).mapError toString)
    need (full.1 == reference.1 && full.2.2 == reference.2.2 &&
      { full.2.1 with auxReport := {} } == { reference.2.1 with auxReport := {} } &&
      full.2.1.auxReport.retried == some why) s!"full driver output changed: {label}"
    if label == "Tests.Ix.Compile.Mutual.NestedPredicate.VR.con" then
      let fn := Name.fromLeanName `Tests.Ix.Compile.Mutual.NestedPredicate.CtorInfo.ofKey
      let owner := Name.fromLeanName `Tests.Ix.Compile.Mutual.NestedPredicate.VR
      let some (.defnInfo dv) := svc.input.get? fn | throw (IO.userError "unresolved fixture missing")
      let broken := replace svc fn (some (.defnInfo { dv with value := Expr.mkConst (fn.mkStr "missing") #[] }))
      refused "driver unresolved" (runTail { cenv with auxGenerationRetry := some (fun _ => GenerationOnly.ofService broken owner) }
        lo members ordinary true) s!"unsupportedExpr: AuxGen (generation retry): block {lo.pretty}: invalid: unknown constant in value of {fn.pretty}"
    count := count + 1
    IO.println s!"production driver SAME {label}: {observed.1.2.generated.size} exempt rows"
  need (count == 9) "incomplete nine-case confirmation"
  IO.println "production generation retry: 9/9 full-driver and tail comparisons; whole-state rollback"

end Tests.Ix.AuxGen.GenerationOnlyDependencies
