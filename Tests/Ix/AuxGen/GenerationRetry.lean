import Tests.Ix.AuxGen.GenerationOnlyDependencies
import Tests.Ix.AuxGen.NestedTailReference

namespace Tests.Ix.AuxGen.GenerationRetry
open _root_.Ix _root_.Ix.AuxGen
open Tests.Ix.AuxGen.GenerationOnlySpike (runTail sameTail)
open Tests.Ix.AuxGen.BelowIxc (runIn planted)
open Tests.Ix.AuxGen.GenerationOnlyDependencies (context prepareDeps)

unsafe inductive TierTree where
  | leaf (n : Nat)
  | node (next : TierTree)

run_cmd do
  let env ← Lean.getEnv
  let names := env.constants.fold (init := (#[] : Array Lean.Name)) fun acc n _ =>
    if n.toString.startsWith "_private.Ix.CompileDriver." && n.toString.endsWith ".Ix.CompileM.preparedSource" then acc.push n else acc
  unless names.size == 1 do throwError "prepared snapshot alias: {names}"
  Lean.Elab.Command.elabCommand (← `(abbrev $(Lean.mkIdent `prepared) := $(Lean.mkIdent names[0]!)))

private def need (ok : Bool) (why : String) : IO Unit := unless ok do throw (IO.userError why)
private def refused (r : Except String α) (want : String) : IO Unit := match r with
  | .error e => need (e == want) s!"expected {want}, got {e}"
  | .ok _ => throw (IO.userError s!"unexpected success: {want}")

def evaluate : IO Unit := do
  let leanEnv ← getCompileEnv #[`Tests.Ix.AuxGen.GenerationRetry,
    `Tests.Ix.Compile.AuxCert.NestedSortUK]
  let env ← Tests.Ix.Kernel.SourceIngress.envOf leanEnv #[`NestedSortUK.T, `NestedSortUK.t_rec, ``TierTree]
  let blocks := Tests.Ix.Kernel.SourceIngressStep.condense env
  let ((ix1, _, c1), _) ← IO.ofExcept (← IO.lazyPure fun _ => CompileM.compileEnvFoldWithSource env blocks (width := 1))
  let ((ix4, _, c4), _) ← IO.ofExcept (← IO.lazyPure fun _ => CompileM.compileEnvFoldWithSource env blocks (width := 4))
  need (c1.ungrounded.isEmpty && c4.ungrounded.isEmpty && (← IO.ofExcept (Ixon.serEnv ix1)) == (← IO.ofExcept (Ixon.serEnv ix4))) "width 1/4 compile differs"
  need (c4.auxOracle.isNone && c4.auxGenerationRetry.isNone && c4.sourceFamilyOracle.isSome) "provider lifetime changed"
  let opts : CompileM.AuxIxcOptions := {}
  let ra := Source.RunAhead.start env.get? blocks (CompileM.scheduleLevels blocks (CompileM.FoldSchedule.of blocks)) opts.asks
  let cenv := opts.withSourceProviders env.get? blocks ra c4
  let owner := Name.fromLeanName `NestedSortUK.T
  let some rep := blocks.lowLinks.get? owner | throw (IO.userError "owner missing")
  let some ms := blocks.blocks.get? rep | throw (IO.userError "members missing")
  let key := CompileM.blockKey rep ms
  let members := ra.membersFor key
  let some provider := cenv.auxGenerationRetry | throw (IO.userError "provider missing")
  let some ordinary := cenv.auxOracle.bind (· key) | throw (IO.userError "oracle missing")
  let some snapshot := (prepared ra).get? ⟨key⟩ | throw (IO.userError "snapshot missing")
  let svc ← IO.ofExcept snapshot.get
  let svcAgain ← IO.ofExcept snapshot.get
  need (svc.entries.map (·.status) == svcAgain.entries.map (·.status) && decide (svc.env.fold.fe.env.consts = svcAgain.env.fold.fe.env.consts)) "cached snapshot advanced logical fold"
  let some why := ordinary.blockStatus () | throw (IO.userError "owner accepted")
  let retained ← IO.ofExcept (c4.familyOracle owner)
  need (retained.blockStatus () == some why) "retained SourceFamily changed the original status"
  let some (.inductInfo ind) := env.get? owner | throw (IO.userError "retained owner missing")
  let _ ← IO.ofExcept (do
    let scope ← retained.newScope ind.cnst.levelParams #[]
    scope.infer (Expr.mkConst owner (ind.cnst.levelParams.map Level.mkParam)))
  let actual ← IO.ofExcept (provider key)
  need ((← IO.ofExcept (provider key)).blockStatus () == some why && Ixc.blockStatus? svc members == some why) "provider changed original status"
  let checked ← IO.ofExcept (runTail cenv key members ordinary true)
  need (checked.1.2.ixcStats.recWhnf == 8 && checked.1.2.ixcStats.recRefused == 0 &&
    checked.1.2.generated.size == 2) "NestedSortUK checked query/tail coverage changed"
  need (((svc.ensureNames #[Name.fromLeanName `NestedSortUK.t_rec]).statusOf? (Name.fromLeanName `NestedSortUK.t_rec)).any
    (fun | .blocked _ => true | _ => false)) "NestedSortUK dependent fence changed"
  let direct ← IO.ofExcept (runTail cenv key members actual)
  need ({ checked.2 with auxReport := { checked.2.auxReport with retried := none } } == direct.2) "whole checked rollback changed"
  IO.ofExcept (NestedTailReference.check 1 #[`Tests.Ix.AuxGen.GenerationRetry, `Tests.Ix.Compile.AuxCert.NestedSortUK]
    #[`NestedSortUK.T, `NestedSortUK.t_rec, ``TierTree] none env blocks key members why checked direct)
  IO.println "nested tail reference: retry-tier-tree binding, full output and rollback passed"
  let some recOff := ({ opts with recursors := false }).oracleFor ra env.get? key | throw (IO.userError "rec-off missing")
  need recOff.retry.isNone "retired rec-off request constructed a legacy retry"
  refused (runTail cenv key members (planted recOff (some why)) true)
    "unsupportedExpr: AuxGen (configuration): recursors must be enabled (rec=off is retired)"
  let run p (o := planted ordinary (some why)) := runTail { cenv with auxGenerationRetry := p } key members o true
  let failurePrefix := s!"unsupportedExpr: AuxGen (generation retry): block {key.pretty}: "
  refused (run none) (failurePrefix ++ "checked provider absent")
  refused (run (some (fun _ => .error "provider sentinel"))) (failurePrefix ++ "provider sentinel")
  let stopped := run (some (fun _ => .error "provider sentinel")) (planted ordinary none)
  match stopped with
  | .error e => need ((e.splitOn "accepted by Source mode").length == 2 && (e.splitOn "provider sentinel").length == 1) "accepted block forced retry"
  | .ok _ => throw (IO.userError "accepted refusal succeeded")
  let nonIxc := runIn { cenv with auxGenerationRetry := some (fun _ => .error "provider sentinel") } key
    (CompileM.runAuxTail key #[] [] default (AddrMaps.ofCompileEnv cenv) (.ixc (AddrMaps.ofCompileEnv cenv) ordinary))
  refused nonIxc s!"invalidMutualBlock: internal error in block '{key.pretty}': compileMutualAuxTail: first class: index 0 out of range (size 0)"
  let wrong mode rec status retry := match actual with
    | .mk _ trace scope flat below _ asked lazyScope admit _ _ family =>
      AuxOracle.mk mode trace scope flat below rec asked lazyScope admit (fun _ => status) retry family
  for bad in #[wrong .fallback true (some why) none, wrong .failClosed false (some why) none,
      wrong .failClosed true (some why) (some actual)] do
    refused (run (some (fun _ => .ok bad))) (failurePrefix ++ "capability must be failClosed, recursors-on, without nested retry")
  refused (run (some (fun _ => .ok (wrong .failClosed true (some "changed") none))))
    (failurePrefix ++ "capability changed the original Source nonacceptance reason")
  let brokenLookup n := match svc.input.get? n with
    | some (.recInfo r) => some (.recInfo { r with rules := r.rules.modify 0 fun v => { v with rhs := Expr.mkLit (.natVal 7) } })
    | other => other
  let malformed := { svc with input := { svc.input with get? := brokenLookup } }
  refused (run (some (fun _ => GenerationOnly.ofService malformed owner))) (failurePrefix ++ "invalid: function expected")
  let initial := context svc svc.env.tier svc.env.sigma why
  for (fuel, active, cause) in #[(0, #[], "depth exhausted"), (1, #[owner], "cycle")] do
    refused (run (some (fun _ => (prepareDeps fuel initial active owner).bind fun _ => .ok actual)))
      (failurePrefix ++ s!"generation: dependency {cause} at {owner.pretty}")
  let failedRa : Source.RunAhead := { ra with levels := ra.levels.map fun _ => Task.pure { service := .error "snapshot sentinel" } }
  let failed := opts.withSourceProviders env.get? blocks failedRa c4
  let some failedProvider := failed.auxGenerationRetry | throw (IO.userError "failure provider missing")
  for _ in [:2] do refused (failedProvider key) "snapshot sentinel"
  refused (run failed.auxGenerationRetry) (failurePrefix ++ "snapshot sentinel")
  let missingTask := opts.withSourceProviders env.get? blocks { ra with levels := #[] } c4
  refused (run missingTask.auxGenerationRetry) (failurePrefix ++ s!"scheduled Source task absent for {key.pretty}")
  let mismatched := opts.withSourceProviders env.get? blocks { ra with levelOf := ra.levelOf.insert ⟨key⟩ (0, {}) } c4
  refused (run mismatched.auxGenerationRetry) (failurePrefix ++ s!"scheduled members differ at {key.pretty}")
  let noOwner n := match env.get? n with | some (.inductInfo _) => none | other => other
  let absent := opts.withSourceProviders noOwner blocks ra c4
  refused (run absent.auxGenerationRetry) (failurePrefix ++ s!"original member absent: {owner.pretty}")
  for n in #[Name.fromLeanName `Nat, Name.fromLeanName ``TierTree] do
    let some rep := blocks.lowLinks.get? n | throw (IO.userError "unforced fixture absent")
    let some ms := blocks.blocks.get? rep | throw (IO.userError "unforced members absent")
    let key := CompileM.blockKey rep ms
    let some oracle := cenv.auxOracle.bind (· key) | throw (IO.userError "unforced oracle absent")
    if n == Name.fromLeanName ``TierTree then need (oracle.blockStatus () == some AuxOracle.tierBlockStatus) "tier fixture lost its tier"
    let _ ← IO.ofExcept (runTail { cenv with auxGenerationRetry := some (fun _ => .error "unforced retry") } key ms.toArray oracle true)
  IO.println "retry boundary: named failures/policy guards; cached statuses/errors; ordinary/tier unforced; width 1/4; NestedSortUK eight checked queries/fence; rec-off explicitly refused"

end Tests.Ix.AuxGen.GenerationRetry
